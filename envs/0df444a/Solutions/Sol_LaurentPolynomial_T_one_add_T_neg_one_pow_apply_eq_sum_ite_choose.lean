-- Prove2me | solution 1 for LaurentPolynomial.T_one_add_T_neg_one_pow_apply_eq_sum_ite_choose
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/fcedd06a-ab1e-516e-bd02-cb9a43dff7bf

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LaurentPolynomial_T_one_add_T_neg_one_pow_apply_eq_sum_ite_choose

set_option autoImplicit false

theorem solution (R : Type*) [CommSemiring R] (k : ℕ) (m : ℤ) :
    ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial R).coeff m =
      ∑ i ∈ Finset.range (k + 1), if (2 * (i : ℤ) - k = m) then ((k.choose i : ℕ) : R) else 0 := by
  classical
  have hcomm : Commute (LaurentPolynomial.T 1 : LaurentPolynomial R) (LaurentPolynomial.T (-1)) :=
    Commute.all _ _
  have hterm : ∀ i ∈ Finset.range (k + 1),
      ((LaurentPolynomial.T 1 : LaurentPolynomial R) ^ i * LaurentPolynomial.T (-1) ^ (k - i) *
          (k.choose i : LaurentPolynomial R)) =
        AddMonoidAlgebra.single (2 * (i : ℤ) - k) ((k.choose i : ℕ) : R) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [LaurentPolynomial.T_pow, LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add]
    have hexp : (i : ℤ) * 1 + ((k - i : ℕ) : ℤ) * (-1) = 2 * (i : ℤ) - k := by
      push_cast [hik]; ring
    rw [hexp, show ((k.choose i : ℕ) : LaurentPolynomial R) = LaurentPolynomial.C ((k.choose i : ℕ) : R) by
      simp [map_natCast]]
    rw [LaurentPolynomial.single_eq_C_mul_T]
    exact mul_comm _ _
  have hsum : ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial R) =
      ∑ i ∈ Finset.range (k + 1), AddMonoidAlgebra.single (2 * (i : ℤ) - k) ((k.choose i : ℕ) : R) := by
    rw [hcomm.add_pow]
    exact Finset.sum_congr rfl hterm
  rw [hsum, AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

end S_LaurentPolynomial_T_one_add_T_neg_one_pow_apply_eq_sum_ite_choose
end P2MW
export P2MW.S_LaurentPolynomial_T_one_add_T_neg_one_pow_apply_eq_sum_ite_choose (solution)
