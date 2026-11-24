-- Prove2me | solution 1 for GlobalTheory.T.measurePreserving_polar_gaussianProbabilityComplexSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:06:46.525197+00:00
-- url     : https://prove2.me/submissions/b3cc39ea-bb49-4a3d-b142-60a24b464576

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPolarGaussianProbabilityComplex
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPolarGaussianProbabilityComplexStatement
import Theorems.Thm_GlobalTheory_SphereMeanDrop_measurePreserving_polar_gaussProb


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
theorem _root_.solution : ∀ (n : ℕ), 0 < n → MeasurePreserving (fun p : UnitSphereC n × Ioi (0:ℝ) => (p.2 : ℝ) • (p.1 : EuclideanSpace ℂ (Fin n))) ((sphereProb n).prod (radProb n)) (gaussProb n) := by
  first | exact @GlobalTheory.SphereMeanDrop.measurePreserving_polar_gaussProb | exact GlobalTheory.SphereMeanDrop.measurePreserving_polar_gaussProb | (intros; apply GlobalTheory.SphereMeanDrop.measurePreserving_polar_gaussProb <;> assumption)
end _root_.GlobalTheory.T
