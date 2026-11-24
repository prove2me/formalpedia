-- Prove2me | solution 1 for GlobalTheory.T.heckeWeightTwoKernelPhi_line_continuous_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:12:20.867047+00:00
-- url     : https://prove2.me/submissions/d74d1ea2-03d4-463c-820a-7bc6ed5d8cad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoKernelPhiLineContinuousIntegrable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoKernelPhiLineContinuousIntegrableStatement
import Theorems.Thm_GlobalTheory_HeckeTwo_phi_line_continuous_integrable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 → Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) ∧ MeasureTheory.Integrable (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) := by
  first | exact @GlobalTheory.HeckeTwo.phi_line_continuous_integrable | exact GlobalTheory.HeckeTwo.phi_line_continuous_integrable | (intros; apply GlobalTheory.HeckeTwo.phi_line_continuous_integrable <;> assumption)
end _root_.GlobalTheory.T
