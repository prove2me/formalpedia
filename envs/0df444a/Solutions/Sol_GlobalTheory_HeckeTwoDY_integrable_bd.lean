-- Prove2me | solution 1 for GlobalTheory.HeckeTwoDY.integrable_bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:17.976275+00:00
-- url     : https://prove2.me/submissions/eb46cbf3-f8a0-4957-adc2-5173279cd612

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtY

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoDY
open MeasureTheory
namespace GlobalTheory.HeckeTwoDY
theorem _root_.solution {k c : ℝ} (hk : 1 < k) (hc : c ≠ 0) :
    Integrable (fun t : ℝ => Real.exp (-(k / 2) * Real.log (t ^ 2 + c ^ 2))) := by
  have h := (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := k) (by simp; linarith)).comp_div hc
  have h2 := h.const_mul ((c ^ 2) ^ (-k / 2))
  refine h2.congr (Filter.Eventually.of_forall fun t => ?_)
  have hc2 : 0 < c ^ 2 := by positivity
  have he : c ^ 2 * (1 + ‖t / c‖ ^ 2) = t ^ 2 + c ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs, div_pow]; field_simp; ring
  simp only
  rw [← Real.mul_rpow hc2.le (by positivity), he, Real.rpow_def_of_pos (by positivity)]
  congr 1; ring
end GlobalTheory.HeckeTwoDY
