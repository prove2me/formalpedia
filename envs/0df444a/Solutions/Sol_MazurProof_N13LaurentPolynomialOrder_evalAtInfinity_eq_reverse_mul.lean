-- Prove2me | solution 1 for MazurProof.N13LaurentPolynomialOrder.evalAtInfinity_eq_reverse_mul
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:33:47.781489+00:00
-- url     : https://prove2.me/submissions/b9422a28-5bc9-4f8d-8e20-02566dc313d9

import Mathlib
import Definitions.Def_MazurN13_L0
import Theorems.Thm_MazurProof_N13LaurentPolynomialOrder_parameter_inv

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

-- ===== FLT.Assumptions.MazurProof.N13LaurentPolynomialOrder =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13LaurentPolynomialOrder =====
section
/-!
# The order at infinity of a polynomial

The substitution `X = s⁻¹` reverses a polynomial.  Its leading
coefficient becomes the constant coefficient of the reversed polynomial,
so the latter has order zero; the factor `s⁻ⁿ` accounts for the whole
order.  This is the formal local calculation used at the cusps of `X₁(13)`.
-/
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof
namespace N13LaurentPolynomialOrder
noncomputable section
universe u
variable (K : Type u) [Field K]
lemma evalAtInfinity_eq_reverse_mul (p : K[X]) :
    evalAtInfinity K p =
      p.reverse.eval₂ (algebraMap K (LaurentSeries K)) (parameter K) *
        (parameter K)⁻¹ ^ p.natDegree := by
  letI : Invertible ((parameter K)⁻¹) :=
    invertibleOfNonzero (inv_ne_zero (parameter_ne_zero K))
  symm
  unfold evalAtInfinity parameter
  simpa [Polynomial.reverse, HahnSeries.inv_single, invOf_eq_inv] using
    (Polynomial.eval₂_reflect_mul_pow (algebraMap K (LaurentSeries K))
      ((parameter K)⁻¹) p.natDegree p le_rfl)
end
end N13LaurentPolynomialOrder
end MazurProof
end

end

theorem solution : type_of% @MazurProof.N13LaurentPolynomialOrder.evalAtInfinity_eq_reverse_mul := @MazurProof.N13LaurentPolynomialOrder.evalAtInfinity_eq_reverse_mul
