-- Prove2me | solution 1 for GlobalTheory.AffinePoints.hasAlgebraicCharts_of_isStandardSmooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:48.866585+00:00
-- url     : https://prove2.me/submissions/e4eb899e-b525-44b6-b653-e14847b689b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Theorems.Thm_GlobalTheory_AffinePoints_exists_isAlgebraicChart_of_away

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial
open scoped Manifold ContDiff
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {A : Type*} [CommRing A] [Algebra 𝕜 A] {d : ℕ}
variable [CompleteSpace 𝕜]
namespace GlobalTheory.AffinePoints
theorem _root_.solution
    [Algebra.IsStandardSmoothOfRelativeDimension d 𝕜 A] : HasAlgebraicCharts 𝕜 A d := by
  intro p
  haveI : IsLocalization.Away (1 : A) A :=
    IsLocalization.away_of_isUnit_of_bijective A isUnit_one Function.bijective_id
  exact exists_isAlgebraicChart_of_away (1 : A) A p (by simp)
end GlobalTheory.AffinePoints
