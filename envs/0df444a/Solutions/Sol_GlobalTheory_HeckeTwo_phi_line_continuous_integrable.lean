-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.phi_line_continuous_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:21:07.782582+00:00
-- url     : https://prove2.me/submissions/32bc75e7-c5f4-46fc-a922-d6f3f8e2bd89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoKernelPhiLineContinuousIntegrable
import Theorems.Thm_GlobalTheory_HeckeTwo_PhiLine_phi_line

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex MeasureTheory
namespace GlobalTheory.HeckeTwo
theorem _root_.solution : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 →
    Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) ∧
      MeasureTheory.Integrable (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) :=
  fun σ hσ y hy => GlobalTheory.HeckeTwo.PhiLine.phi_line σ hσ y hy
end GlobalTheory.HeckeTwo
