-- Prove2me | solution 1 for GlobalTheory.AbLaw.SecOn.chart_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:38:30.290626+00:00
-- url     : https://prove2.me/submissions/392003fb-0660-4177-923d-b0dd78a992fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Theorems.Thm_GlobalTheory_LB_chartEquiv_change


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
open GlobalTheory.AbLaw.SecOn
open GlobalTheory.LB
variable {L M H : LB X} {V W : X.Opens}
namespace GlobalTheory.AbLaw.SecOn
theorem _root_.solution (hM : M.IsLB) (i j : M.ι) (hi : V ≤ M.U i) (hj : V ≤ M.U j) (s : SecOn M V) :
    chart hM i hi s = rs X (le_inf hi hj) (M.g i j).val * chart hM j hj s :=
  chartEquiv_change hM i j hi hj s
end GlobalTheory.AbLaw.SecOn
