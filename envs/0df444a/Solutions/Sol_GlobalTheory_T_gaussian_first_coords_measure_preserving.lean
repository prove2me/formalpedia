-- Prove2me | solution 1 for GlobalTheory.T.gaussian_first_coords_measure_preserving
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:10:54.873978+00:00
-- url     : https://prove2.me/submissions/91971a98-5b7e-40b9-8c40-2d8270b6a756

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianFirstCoordsMeasurePreserving
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianFirstCoordsMeasurePreservingStatement
import Theorems.Thm_GlobalTheory_GaussMarginal_measurePreserving_firstCoords_gaussProb


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
theorem _root_.solution : ∀ (N n : ℕ) (h : N ≤ n), MeasurePreserving (firstCoords h) (gaussProb n) (gaussProb N) := by
  first | exact @GlobalTheory.GaussMarginal.measurePreserving_firstCoords_gaussProb | exact GlobalTheory.GaussMarginal.measurePreserving_firstCoords_gaussProb | (intros; apply GlobalTheory.GaussMarginal.measurePreserving_firstCoords_gaussProb <;> assumption)
end _root_.GlobalTheory.T
