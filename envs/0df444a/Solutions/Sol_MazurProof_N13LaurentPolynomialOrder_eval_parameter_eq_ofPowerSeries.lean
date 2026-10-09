-- Prove2me | solution 1 for MazurProof.N13LaurentPolynomialOrder.eval_parameter_eq_ofPowerSeries
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:30:27.079909+00:00
-- url     : https://prove2.me/submissions/8e53799b-7810-43dc-ac4d-54fd27bf7384

import Mathlib
import Definitions.Def_MazurN13_L0

set_option maxHeartbeats 1000000

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
lemma eval_parameter_eq_ofPowerSeries (p : K[X]) :
    p.eval₂ (algebraMap K (LaurentSeries K)) (parameter K) =
      HahnSeries.ofPowerSeries ℤ K p := by
  have h : Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K)) (parameter K) =
      algebraMap K[X] (LaurentSeries K) := by
    apply Polynomial.ringHom_ext
    · intro a
      change Polynomial.eval₂ (algebraMap K (LaurentSeries K)) (parameter K) (C a) = _
      rw [Polynomial.eval₂_C, Polynomial.algebraMap_hahnSeries_apply]
      simp [HahnSeries.algebraMap_apply']
    · change Polynomial.eval₂ (algebraMap K (LaurentSeries K)) (parameter K) X = _
      rw [Polynomial.eval₂_X, Polynomial.algebraMap_hahnSeries_apply]
      simp [parameter, HahnSeries.ofPowerSeries_X]
  change (Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K)) (parameter K)) p = _
  rw [h, Polynomial.algebraMap_hahnSeries_apply]
end
end N13LaurentPolynomialOrder
end MazurProof
end

end

theorem solution : type_of% @MazurProof.N13LaurentPolynomialOrder.eval_parameter_eq_ofPowerSeries := @MazurProof.N13LaurentPolynomialOrder.eval_parameter_eq_ofPowerSeries
