-- Prove2me | solution 1 for GlobalTheory.T.inverse_transform_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:39:46.214973+00:00
-- url     : https://prove2.me/submissions/60513010-a104-42e4-b50c-ad0b4afe697f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformContinuous
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformContinuousStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_inv_continuous_joint


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
theorem _root_.solution : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type) [TopologicalSpace T] [FirstCountableTopology T] (φ : ℝ × ℝ → T → X), ExpDecay φ → Continuous (fun p : (ℝ × ℝ) × T => φ p.1 p.2) → Continuous (fun y : (ℂ × ℂ) × T => inv (fun t => φ t y.2) y.1) := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.inv_continuous_joint | exact GlobalTheory.CompanionTheory.TubeFourier.inv_continuous_joint | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.inv_continuous_joint <;> assumption)
end _root_.GlobalTheory.T
