-- Prove2me | solution 1 for GlobalTheory.SphereMeanDrop.isProbabilityMeasure_gaussProb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:52:25.231007+00:00
-- url     : https://prove2.me/submissions/c7070252-8276-4434-ad3f-1da2b5aed04c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPolarGaussianProbabilityComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianRadialLawProbabilityLogIntegrableMeanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianFirstCoordsMeasurePreservingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BlockSphereProbZeroSetEqZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsMultiHomogeneousRenameCastLE
import Theorems.Thm_GlobalTheory_T_gaussianRadialLawProbability_log_integrable_mean
import Theorems.Thm_GlobalTheory_T_measurePreserving_polar_gaussianProbabilityComplexSpace
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_isProbabilityMeasure_sphereProb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SphereMeanDrop
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights
namespace GlobalTheory.SphereMeanDrop
theorem _root_.solution {n : ℕ} (hn : 0 < n) : IsProbabilityMeasure (gaussProb n) := by
  have hp := GlobalTheory.T.measurePreserving_polar_gaussianProbabilityComplexSpace n hn
  haveI := (GlobalTheory.T.gaussianRadialLawProbability_log_integrable_mean n hn).1
  haveI : IsProbabilityMeasure (sphereProb n) := isProbabilityMeasure_sphereProb hn
  rw [← hp.map_eq]
  exact Measure.isProbabilityMeasure_map hp.measurable.aemeasurable
end GlobalTheory.SphereMeanDrop
