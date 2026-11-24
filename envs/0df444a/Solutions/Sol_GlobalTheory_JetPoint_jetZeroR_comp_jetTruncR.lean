-- Prove2me | solution 1 for GlobalTheory.JetPoint.jetZeroR_comp_jetTruncR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:10:11.207296+00:00
-- url     : https://prove2.me/submissions/6523467e-801e-4133-b422-2b6b20714a9f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsJetPointsOfIsLieBasis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetPoint
open GlobalTheory.SqZero
variable {R : Type} [CommRing R]
namespace GlobalTheory.JetPoint
theorem _root_.solution (κ : Type) (m : ℕ) :
    (jetZeroR R κ m).comp (jetTruncR R κ m) = jetZeroR R κ (m + 1) :=
  jet_ext fun _ => rfl
end GlobalTheory.JetPoint
