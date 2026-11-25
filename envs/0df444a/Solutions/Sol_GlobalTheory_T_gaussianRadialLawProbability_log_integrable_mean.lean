-- Prove2me | solution 1 for GlobalTheory.T.gaussianRadialLawProbability_log_integrable_mean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:42:02.239183+00:00
-- url     : https://prove2.me/submissions/a2f38f97-47c8-4592-9b51-b5985019872d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianRadialLawProbabilityLogIntegrableMean
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianRadialLawProbabilityLogIntegrableMeanStatement
import Theorems.Thm_GlobalTheory_SphereMeanDrop_radProb_log_mean


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ), 0 < n → IsProbabilityMeasure (radProb n) ∧ Integrable (fun r : Ioi (0:ℝ) => Real.log r) (radProb n) ∧ ∫ r, Real.log (r : ℝ) ∂(radProb n) = radK (2 * n - 1) / radJ (2 * n - 1) := by
  first | exact @GlobalTheory.SphereMeanDrop.radProb_log_mean | exact GlobalTheory.SphereMeanDrop.radProb_log_mean | (intros; apply GlobalTheory.SphereMeanDrop.radProb_log_mean <;> assumption)
end _root_.GlobalTheory.T
