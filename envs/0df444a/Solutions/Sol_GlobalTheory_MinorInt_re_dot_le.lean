-- Prove2me | solution 1 for GlobalTheory.MinorInt.re_dot_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:58:23.967694+00:00
-- url     : https://prove2.me/submissions/02bb878b-2ef1-4a7e-9bd7-5a05049d2bda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder
open GlobalTheory GlobalTheory.MinorInt
namespace GlobalTheory.MinorInt
theorem _root_.solution {ι : Type*} [Fintype ι] (c : ℝ) (hc : 0 < c) (x y : ι → ℂ) :
    (star x ⬝ᵥ y).re ≤ c * ∑ i, ‖x i‖ ^ 2 + (∑ i, ‖y i‖ ^ 2) / (4 * c) := by
  rw [dotProduct, Complex.re_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => (Complex.re_le_norm _).trans ?_
  rw [norm_mul, Pi.star_apply, norm_star]
  have : ‖y i‖ ^ 2 / (4 * c) = c * (‖y i‖ / (2 * c)) ^ 2 := by field_simp; ring
  have h2 : ‖x i‖ * ‖y i‖ = c * (2 * ‖x i‖ * (‖y i‖ / (2 * c))) := by field_simp
  rw [this, h2, ← mul_add]
  gcongr
  nlinarith [sq_nonneg (‖x i‖ - ‖y i‖ / (2 * c))]
end GlobalTheory.MinorInt
