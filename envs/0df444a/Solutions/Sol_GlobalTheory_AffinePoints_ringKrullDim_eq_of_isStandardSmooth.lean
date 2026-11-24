-- Prove2me | solution 1 for GlobalTheory.AffinePoints.ringKrullDim_eq_of_isStandardSmooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:56:40.216304+00:00
-- url     : https://prove2.me/submissions/3b9301a1-e2d8-478b-bb8f-e4d5bd9aebd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_trdeg_eq_of_etale

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
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A] {d : ℕ}
namespace GlobalTheory.AffinePoints
theorem _root_.solution [IsDomain A]
    [Algebra.IsStandardSmoothOfRelativeDimension d K A] : ringKrullDim A = d := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d K A
  haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (R := K) (S := A) d
  exact ringKrullDim_eq_of_trdeg_eq K A (trdeg_eq_of_etale g hg)
end GlobalTheory.AffinePoints
