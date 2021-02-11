from sage.rings.rational_field import QQ


class myLP:
    def __init__(self, c, A, b, check_twophase=True, start_index=1):
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
        self.A = [[-1 * a_ij for a_ij in row] for row in A]
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
        # This is the case where we _are_ the auxiliary problem
        elif not self.feasible:
            self.special_pivot()
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
        assert enter_col < self.start_index + self.n

        # exit_loc: which row the exiting variable was in formerly
        assert var_exit in self.basic
        exit_row = self.where_is[var_exit]
        assert exit_row >= self.start_index + self.n
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

        self.where_is[var_enter] = exit_row
        self.where_is[var_exit] = enter_col

        return

    # def get_aux(self, A, b):
    #     assert self.two_step
    #     aux_c = [-1] + [0 for _ in range(self.n)]
    #     aux_A = []
    #     for i in range(self.m):
    #         aux_A += [[-1] + A[i]]
    #     aux_b = b
    #     return myLP(aux_c, aux_A, aux_b, check_twophase=False, start_index=0)


def test_chvatal_pg_19():
    c = [5, 5, 3]
    b = [3, 2, 4, 2]
    A = [[1, 3, 1], [-1, 0, 3], [2, -1, 2], [2, 3, -1]]
    lp = myLP(c, A, b)
    print(lp)
    lp.pivot(1, 7)
    print(lp)
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
    print(lp)
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
    print(lp)
    assert lp.z_val == 10
    assert lp.c == [-2, -1, -1]
    assert lp.b == [1 / 29, 8 / 29, 30 / 29, 32 / 29]
    assert lp.A == [
        [28 / 29, 21 / 29, -3 / 29],
        [-8 / 29, -6 / 29, 5 / 29],
        [-1 / 29, -8 / 29, -3 / 29],
        [-3 / 29, 5 / 29, -9 / 29],
    ]


if __name__ == "__main__":
    test_chvatal_pg_19()

# c = [-1, 0, 0, 0]
# A = [[-1, 1, 1, 1], [-1, 1, -1, 0], [-1, -1, 2, -1]]
# b = [2, -1, 3]
# lp = myLP(c, A, b, start_index=0)
# print(lp)
# lp.pivot(0, 5)
# print(lp)
