from sage.rings.rational_field import QQ
from sage.rings.infinity import Infinity
from copy import deepcopy


class myLP:
    def __init__(
        self, c, A, b, check_twophase=True, start_index=1, from_ineq=True, noprint=True
    ):
        """
        expects an LP in standard form, as represented by a cost
        vector c (list), a matrix A (list of list), and a constraint
        vector b (list)

        given_as_ineq: whether A represents inequalities
        """
        self.n = len(c)
        self.m = len(b)
        self.b = b
        self.c = c

        # A represents the coefficients in the inequalities so need to
        # negate them to get dictionary coefficients
        if from_ineq:
            self.A = [[-1 * a_ij for a_ij in row] for row in A]
        else:
            self.A = A
        self.start_index = start_index  # I don't think this is
        # necessary

        # These should be stored in the order that they appear in in
        # the dictionary columns.
        self.nonbasic = [i for i in range(start_index, self.n + start_index)]

        # These should be stored in the order that they appear in
        # the dictionary rows.
        self.basic = [
            i for i in range(self.n + start_index, self.n + self.m + start_index)
        ]

        # The _index_ (nonbasic: start_index -- start_index + self.n;
        # basic: start_index + self.n -- start_index + self.n +
        # self.m) representing where the variable with subscript `key`
        # is stored.
        self.where_is = {i: i - self.start_index for i in self.nonbasic + self.basic}

        # Initialize objective function
        self.z = list(zip(c, self.nonbasic))
        self.z_val = 0

        # Check if we need to do the two-phase method
        self.feasible = all([bj >= 0 for bj in b])

        # This is the case where we need to solve the auxiliary problem
        if check_twophase and not self.feasible:
            aux = self.get_aux(A, b)
            if not noprint:
                print("Aux problem:")
            aux.simplex_method(noprint=noprint)
            if aux.z_val == 0:
                # Construct the feasible dictionary for the original
                # problem
                assert 0 in aux.nonbasic
                # print(aux_col)
                # print(aux.nonbasic)
                # print(aux)
                if aux.nonbasic[-1] == 0:
                    Anew = [row[:-1] for row in aux.A]
                    nonbasicnew = aux.nonbasic[:-1]
                else:
                    aux_col = aux.nonbasic.index(0)
                    Anew = [row[:aux_col] + row[aux_col + 1 :] for row in aux.A]
                    nonbasicnew = aux.nonbasic[:aux_col] + aux.nonbasic[aux_col + 1 :]
                newwhere_is = aux.where_is
                where_is_0 = newwhere_is[0]

                del newwhere_is[0]
                for var in newwhere_is:
                    if newwhere_is[var] > where_is_0:
                        newwhere_is[var] -= 1

                self.where_is = newwhere_is
                self.A = Anew
                self.b = [bval for bval in aux.b]

                self.nonbasic = nonbasicnew
                self.basic = aux.basic

                for var in self.nonbasic:
                    assert self.where_is[var] < self.n
                for var in self.basic:
                    assert self.where_is[var] >= self.n

                cnew = [0 for _ in self.c]

                for (c_coeff, var) in self.z:
                    if var in nonbasicnew:
                        cnew[self.where_is[var]] += c_coeff
                    else:
                        assert var in aux.basic
                        row_index = self.where_is[var] - self.n
                        for (i, a_coeff) in enumerate(self.A[row_index]):
                            cnew[i] += a_coeff * c_coeff
                        self.z_val += c_coeff * self.b[row_index]
                self.c = cnew
                self.z = list(zip(self.c, self.nonbasic))
                self.aux = aux
                self.first_feasible = deepcopy(self)
                # print("FIRST FEASIBLE IS!!!!\n")
                # print(self.first_feasible)

        # This is the case where we _are_ the auxiliary problem
        elif not self.feasible:
            self.special_pivot(noprint=noprint)
        else:
            pass

    def __repr__(self):

        str_rep = ""

        # Indexed by variable indices
        coeff_padding = {}
        for col_ind in range(self.n):
            # Remove minus signs and check both cost function
            # coefficient and
            coeffs_to_test = [self.c[col_ind]] + [
                self.A[row_ind][col_ind] for row_ind in range(self.m)
            ]

            maxlen_coeff = 0
            for coeff in coeffs_to_test:
                thislen = len(str(coeff).strip("-"))
                if len(str(coeff).strip("-")) > maxlen_coeff:
                    maxlen_coeff = thislen

            coeff_padding[col_ind] = maxlen_coeff

        ##################### hell yes ###############################
        subscript_chars = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")

        longest_basic_subscript = max([len(s) for s in [f"x{j}" for j in self.basic]])

        max_const_len = max([len(str(s).strip("-")) for s in [self.z_val] + self.b])

        # Top row. I guess we'll try `str.rjust()` for padding
        z_line = "z".rjust(longest_basic_subscript) + " == "

        z_val = self.z_val
        z_sgn = (z_val >= 0) * "+" + (z_val < 0) * "-"
        z_str = str(z_val).strip("-")
        z_line += (max_const_len - len(z_str)) * " " + z_sgn + z_str + " "

        # c_coeff --> cost vector coefficient
        for (col_ind, (c_coeff, var)) in enumerate(self.z):
            sgn_str = (c_coeff >= 0) * "+" + (c_coeff < 0) * "-"
            c_str = str(c_coeff).strip("-")
            subscr = str(var).translate(subscript_chars)
            z_line += (
                coeff_padding[col_ind] - len(c_str)
            ) * " " + f" {sgn_str}{c_str}x{subscr} "
        str_rep += z_line + "\n"

        # Print out the constraints
        str_rep += 70 * "-" + "\n"
        for (row, row_ind) in zip(self.A, range(self.m)):
            row_str = f"x{self.basic[row_ind]} == ".translate(
                subscript_chars
            )  # To align with the z columns

            b_val = self.b[row_ind]
            b_sgn = (b_val >= 0) * "+" + (b_val < 0) * "-"
            b_str = str(b_val).strip("-")
            row_str += (max_const_len - len(b_str)) * " " + b_sgn + b_str + " "

            for (col_ind, a_coeff) in enumerate(row):
                sgn_str = (a_coeff >= 0) * "+" + (a_coeff < 0) * "-"
                a_str = str(a_coeff).strip("-")
                subscr = str(self.nonbasic[col_ind]).translate(subscript_chars)
                row_str += (
                    coeff_padding[col_ind] - len(a_str)
                ) * " " + f" {sgn_str}{a_str}x{subscr} "
            str_rep += row_str + "\n"
        return str_rep

    def pivot(self, var_enter, var_exit):
        """
        var_enter: the subscript for the entering variable
        var_exit : analogous
        """

        # enter_col: which column the entering variable was in
        # formerly
        assert var_enter in self.nonbasic
        enter_col = self.where_is[var_enter]
        assert enter_col < self.n

        # exit_loc: which row the exiting variable was in formerly
        assert var_exit in self.basic
        exit_row = self.where_is[var_exit]
        assert exit_row >= self.n
        exit_row -= self.n  # Mod to actually use

        enter_coeff = -1 * self.A[exit_row][enter_col]
        assert enter_coeff != 0

        self.nonbasic = [
            (v == var_enter) * var_exit + (v != var_enter) * v for v in self.nonbasic
        ]

        self.basic = [
            (v == var_exit) * var_enter + (v != var_exit) * v for v in self.basic
        ]

        # keep rational
        self.b[exit_row] = QQ(self.b[exit_row] / enter_coeff)

        new_row = [a_ij for a_ij in self.A[exit_row]]
        new_row[enter_col] = -1
        new_row = [QQ(a_ij / enter_coeff) for a_ij in new_row]
        self.A[exit_row] = new_row

        for (i, row) in enumerate(self.A):
            if i == exit_row:
                pass
            else:
                coeff = row[enter_col]
                self.b[i] += coeff * self.b[exit_row]
                this_row = [old + new * coeff for (old, new) in zip(row, new_row)]
                this_row[enter_col] -= coeff
                self.A[i] = this_row

        self.z_val += self.b[exit_row] * self.z[enter_col][0]

        # Need to add entering variable contributions before use
        row_coeff = self.z[enter_col][0]
        new_c = [(v != var_enter) * c_coeff for (c_coeff, v) in self.z]
        for (i, c_coeff) in enumerate(new_c):
            new_c[i] = QQ(new_c[i] + row_coeff * self.A[exit_row][i])
        self.c = new_c
        self.z = list(zip(self.c, self.nonbasic))

        self.where_is[var_enter] = exit_row + self.n
        self.where_is[var_exit] = enter_col

        return

    def max_inds(self, some_dumb_list):
        maxind = 0
        biggest = []
        for i in range(len(some_dumb_list)):
            if some_dumb_list[i] > some_dumb_list[maxind]:
                biggest = []
                maxind = i
                biggest += [i]
            elif some_dumb_list[i] == some_dumb_list[maxind]:
                biggest += [i]
        return biggest

    def simplex_method(self, noprint=False):
        if not noprint:
            print("Starting dictionary:\n")
            print(self)
            print("\n")
        while any([c_coeff > 0 for c_coeff in self.c]):
            enter_inds = self.max_inds(self.c)

            # Do anstee's rule
            enter_var = min([self.nonbasic[i] for i in enter_inds])
            enter_ind = self.nonbasic.index(enter_var)

            exit_constraints = []
            all_unbounded = True
            for (b_el, row) in zip(self.b, self.A):
                a_coeff = row[enter_ind]
                if a_coeff < 0:
                    all_unbounded = False
                    exit_constraints += [b_el / a_coeff]
                else:  # No constraint
                    exit_constraints += [-Infinity]
                # elif a_coeff >= 0:
                # # if b_el < 0:
                # #     # TODO: Figure out what to do here
                # #     assert False
                # else:

            if all_unbounded and not noprint:
                print(self)
                print(70 * "=")
                print(f"Problem unbounded with entering variable {enter_var}")
                return

            # If nonempty, exit_constraints should be filled with
            # negative numbers. We want the largest ones
            exit_inds = self.max_inds(exit_constraints)
            # Do anstee's rule
            exit_var = min([self.basic[i] for i in exit_inds])
            exit_ind = self.basic.index(exit_var)

            if not noprint:
                subscript_chars = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")

                print(
                    f"Entering: x{enter_var}".translate(subscript_chars),
                    "     ",
                    f"Exiting: x{exit_var}".translate(subscript_chars),
                    "\n",
                )
            self.pivot(enter_var, exit_var)
            if not noprint:
                print(self)
                print(2 * "\n")
        if not noprint:
            print(70 * "=")
            print(f"Optimal value {self.z_val}")

    def sort_by_inds(self, noprint=False):
        sort_b = lambda enum_tuple: self.basic[enum_tuple[0]]
        bnew = [b_val for (_, b_val) in sorted(list(enumerate(self.b)), key=sort_b)]

        sort_c = lambda enum_tuple: self.nonbasic[enum_tuple[0]]
        cnew = [c_coeff for (_, c_coeff) in sorted(list(enumerate(self.c)), key=sort_c)]

        sort_A_rows = lambda enum_tuple: self.basic[enum_tuple[0]]
        Anew = [row for (_, row) in sorted(list(enumerate(self.A)), key=sort_A_rows)]

        for (row_ind, row) in enumerate(Anew):
            sort_row_cols = lambda enum_tuple: self.nonbasic[enum_tuple[0]]
            rownew = [
                var for (_, var) in sorted(list(enumerate(row)), key=sort_row_cols)
            ]
            Anew[row_ind] = rownew

        self.b = bnew
        self.c = cnew
        self.A = Anew
        self.basic = sorted(self.basic)
        self.nonbasic = sorted(self.nonbasic)
        self.z = list(zip(self.c, self.nonbasic))

        if not noprint:
            print(70 * "=" + "\n")
            print("Sorting output rows / columns. New dictionary is")
            print(self)

    def get_aux(self, A, b):
        aux_c = [-1] + [0 for _ in range(self.n)]
        aux_A = [[-1] + row for row in A]
        aux_b = b
        return myLP(aux_c, aux_A, aux_b, check_twophase=False, start_index=0)

    def special_pivot(self, noprint=False):
        if not noprint:
            print("Aux dictionary:\n")
            print(self)

        enter_var = 0
        exit_var = self.basic[self.b.index(min(self.b))]
        if not noprint:
            subscript_chars = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")
            print(
                f"(Special pivot)\nEntering: x{enter_var}      Exiting: x{exit_var}".translate(
                    subscript_chars
                )
            )
        self.pivot(enter_var, exit_var)


def test_p13_autopivot():
    c = [5, 4, 3]
    b = [5, 11, 8]
    A = [[2, 3, 1], [4, 1, 2], [3, 4, 2]]
    lp = myLP(c, A, b)
    lp.simplex_method(noprint=True)
    return lp


def test_p19():
    """
    Linear program from Chvatal, page 19
    """
    c = [5, 5, 3]
    b = [3, 2, 4, 2]
    A = [[1, 3, 1], [-1, 0, 3], [2, -1, 2], [2, 3, -1]]
    lp = myLP(c, A, b)
    # print(lp)
    lp.pivot(1, 7)
    # print(lp)
    assert lp.z_val == 5
    assert lp.c == [-5 / 2, -5 / 2, 11 / 2]
    assert lp.basic == [4, 5, 6, 1]
    assert lp.nonbasic == [7, 2, 3]
    assert lp.b == [2, 3, 2, 1]
    assert lp.A == [
        [1 / 2, -3 / 2, -3 / 2],
        [-1 / 2, -3 / 2, -5 / 2],
        [1, 4, -3],
        [-1 / 2, -3 / 2, 1 / 2],
    ]
    lp.pivot(3, 6)
    # print(lp)
    assert lp.z_val == 26 / 3
    assert lp.c == [-2 / 3, 29 / 6, -11 / 6]
    assert lp.b == [1, 4 / 3, 2 / 3, 4 / 3]
    assert lp.A == [
        [0, -7 / 2, 1 / 2],
        [-4 / 3, -29 / 6, 5 / 6],
        [1 / 3, 4 / 3, -1 / 3],
        [-1 / 3, -5 / 6, -1 / 6],
    ]
    lp.pivot(2, 5)
    # print(lp)
    assert lp.z_val == 10
    assert lp.c == [-2, -1, -1]
    assert lp.b == [1 / 29, 8 / 29, 30 / 29, 32 / 29]
    assert lp.A == [
        [28 / 29, 21 / 29, -3 / 29],
        [-8 / 29, -6 / 29, 5 / 29],
        [-1 / 29, -8 / 29, -3 / 29],
        [-3 / 29, 5 / 29, -9 / 29],
    ]
    return lp


def test_p19_autopivot():
    c = [5, 5, 3]
    b = [3, 2, 4, 2]
    A = [[1, 3, 1], [-1, 0, 3], [2, -1, 2], [2, 3, -1]]
    lp = myLP(c, A, b)
    lp.simplex_method(noprint=True)
    return lp


def test_p39():
    """
    Tests auxiliary problem
    """
    c = [1, -1, 1]
    b = [4, -5, -1]
    A = [[2, -1, 2], [2, -3, 1], [-1, 1, -2]]
    lp = myLP(c, A, b)
    lp.simplex_method(noprint=True)

    assert lp.aux.c == [0, 0, 0, -1]
    assert lp.aux.z_val == 0
    assert lp.aux.b == [3, 8 / 5, 11 / 5]
    assert lp.aux.A == [
        [0, -1, -1, 2],
        [1 / 5, -1 / 5, 3 / 5, -4 / 5],
        [2 / 5, 3 / 5, 1 / 5, -3 / 5],
    ]
    assert lp.first_feasible.c == [-1 / 5, 1 / 5, 2 / 5]
    assert lp.first_feasible.b == [3, 8 / 5, 11 / 5]
    assert lp.first_feasible.A == [
        [0, -1, -1],
        [1 / 5, -1 / 5, 3 / 5],
        [2 / 5, 3 / 5, 1 / 5],
    ]
    assert lp.first_feasible.z_val == -3 / 5

    return lp


def do_some_tests():
    p19_m = test_p19()

    p19_a = test_p19_autopivot()

    assert p19_m.A == p19_a.A
    assert p19_m.c == p19_a.c
    assert p19_m.b == p19_a.b

    p13 = test_p13_autopivot()
    p13.sort_by_inds(noprint=True)
    assert p13.c == [-3, -1, -1]
    assert p13.b == [2, 1, 1]
    assert p13.A == [[-2, -2, 1], [1, 3, -2], [5, 2, 0]]
    assert p13.z_val == 13

    p39 = test_p39()
    p39.sort_by_inds(noprint=True)


if __name__ == "__main__":
    do_some_tests()

    c = [2, -1, 3]
    A = [[1, 1, 1], [1, -1, 0], [-1, 2, -1]]
    b = [2, -1, 3]
    lp = myLP(c, A, b, noprint=False)
    lp.simplex_method(noprint=False)
    print(lp.first_feasible)
    lp.first_feasible.sort_by_inds()
    print(lp.first_feasible)
