-- Prove2me | solution 1 for GlobalTheory.T.inverse_transform_recovers_function
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:34:02.476066+00:00
-- url     : https://prove2.me/submissions/21878b2e-acbd-476f-ba30-23779d7ed250

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformRecoversFunction
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformRecoversFunctionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_PhiInv_inv_phi_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (G : ℂ × ℂ → X) (x : ℝ × ℝ), Continuous (fun y => G (pt x y)) → (∃ M : ℝ, ∀ y : ℝ × ℝ, ‖G (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) → Continuous (phi G x) → (∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ t : ℝ × ℝ, ‖phi G x t‖ ≤ M * Real.exp (-rdot x t) * Real.exp (-ε * (|t.1| + |t.2|))) → ∀ y : ℝ × ℝ, inv (phi G x) (pt x y) = G (pt x y) := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.PhiInv.inv_phi_eq | exact GlobalTheory.CompanionTheory.TubeFourier.PhiInv.inv_phi_eq | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.PhiInv.inv_phi_eq <;> assumption)
end _root_.GlobalTheory.T
