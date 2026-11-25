-- Prove2me | solution 1 for GlobalTheory.AffinePoints.hasAlgebraicCharts_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:25:38.878282+00:00
-- url     : https://prove2.me/submissions/0a2dd058-a39f-474b-ab7c-6a9e15ee59e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_exists_isAlgebraicChart_of_isSmoothAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial MeasureTheory Module
open scoped Manifold ContDiff
variable {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}
namespace GlobalTheory.AffinePoints
theorem _root_.solution [IsDomain A] [Algebra.Smooth ℂ A]
    (hd : ringKrullDim A = d) : HasAlgebraicCharts ℂ A d := fun p =>
  exists_isAlgebraicChart_of_isSmoothAt hd p inferInstance
end GlobalTheory.AffinePoints
