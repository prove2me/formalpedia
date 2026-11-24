-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.HDecay.wSpan_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:36:27.713735+00:00
-- url     : https://prove2.me/submissions/9789a181-f3d9-450e-9281-312a13f5bff0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_wF_integrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex MeasureTheory
open scoped ContDiff FourierTransform
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.HDecay
variable (σ : ℂ) (y : ℝ)
variable {σ y}
namespace GlobalTheory.HeckeTwo.HDecay
theorem _root_.solution (hy : y ≠ 0) (hσ : 0 < σ.re) {F : ℝ → ℂ} (hF : F ∈ wSpan σ y) :
    Integrable F := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hF
    exact wF_integrable hy hσ a b
  | zero => exact integrable_zero _ _ _
  | add F G _ _ hF hG => exact hF.add hG
  | smul c F _ hF => exact hF.smul c
end GlobalTheory.HeckeTwo.HDecay
