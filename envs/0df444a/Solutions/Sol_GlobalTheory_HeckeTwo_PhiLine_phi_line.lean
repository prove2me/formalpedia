-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.PhiLine.phi_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:01:10.599152+00:00
-- url     : https://prove2.me/submissions/a7cf1162-3480-4069-9b25-5452505e220e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoKernelPhiLineContinuousIntegrable
import Theorems.Thm_GlobalTheory_HeckeTwo_PhiLine_abs_le_norm_line
import Theorems.Thm_GlobalTheory_HeckeTwo_PhiLine_line_ne_zero
import Theorems.Thm_GlobalTheory_HeckeTwo_PhiLine_norm_phi_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex MeasureTheory
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.PhiLine
namespace GlobalTheory.HeckeTwo.PhiLine
theorem _root_.solution (σ : ℂ) (hσ : 0 < σ.re) (y : ℝ) (hy : y ≠ 0) :
    Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) ∧
      MeasureTheory.Integrable (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) := by
  have hw : Continuous (fun t : ℝ => ((t : ℂ) + (y : ℂ) * Complex.I)) := by fun_prop
  have hcont : Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) := by
    unfold GlobalTheory.HeckeTwo.phi
    refine Continuous.mul ((hw.inv₀ fun t => line_ne_zero t y hy).pow 2) ?_
    refine Continuous.cpow (Complex.continuous_ofReal.comp hw.norm) continuous_const ?_
    intro t
    exact Complex.ofReal_mem_slitPlane.2
      (lt_of_lt_of_le (abs_pos.2 hy) (abs_le_norm_line t y))
  refine ⟨hcont, ?_⟩
  refine MeasureTheory.Integrable.mono' (integrable_inv_one_add_sq.const_mul
    (|y| ^ (-2 * σ.re) * (min 1 (y ^ 2))⁻¹)) hcont.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t => norm_phi_le σ hσ y hy t
end GlobalTheory.HeckeTwo.PhiLine
