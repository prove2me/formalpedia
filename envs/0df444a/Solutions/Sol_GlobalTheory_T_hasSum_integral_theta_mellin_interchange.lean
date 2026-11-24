-- Prove2me | solution 1 for GlobalTheory.T.hasSum_integral_theta_mellin_interchange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:12:30.32524+00:00
-- url     : https://prove2.me/submissions/9283205f-ca5f-40d9-b9e6-0b403001fc48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumIntegralThetaMellinInterchange
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumIntegralThetaMellinInterchangeStatement
import Theorems.Thm_GlobalTheory_HeckeMellin_hasSum_integral_theta


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (I : Type) [Fintype I] (ι : Type) [Countable ι] (e : ι → I → ℂ) (a : ι → ℂ) (C : ℝ), (∀ j, ‖a j‖ ≤ C) → ∀ (n : I → ℤ) (s : ℂ) (p : (I → ℝ) → ℝ), Measurable p → (∀ y, 0 ≤ p y) → (∀ y, p y ≤ 1) → (∀ j, Integrable (GlobalTheory.HeckeMellin.term n s (e j))) → Summable (fun j => ∫ y, p y * ‖GlobalTheory.HeckeMellin.term n s (e j) y‖) → HasSum (fun j => a j * ∫ y, (p y : ℂ) * GlobalTheory.HeckeMellin.term n s (e j) y) (∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) := by
  first | exact @GlobalTheory.HeckeMellin.hasSum_integral_theta | exact GlobalTheory.HeckeMellin.hasSum_integral_theta | (intros; apply GlobalTheory.HeckeMellin.hasSum_integral_theta <;> assumption)
end _root_.GlobalTheory.T
