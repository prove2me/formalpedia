-- Prove2me | solution 1 for GlobalTheory.AbLaw.SecOn.chart_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:14:56.003265+00:00
-- url     : https://prove2.me/submissions/fac0caed-8ec5-483f-81e6-9ad28b29f981

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Theorems.Thm_GlobalTheory_LB_chartEquiv_map


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
theorem _root_.solution (hM : M.IsLB) (i : M.ι) (h : V ≤ M.U i) (h' : W ≤ V) (s : SecOn M V) :
    chart hM i (h'.trans h) (restrict M h' s) = rs X h' (chart hM i h s) :=
  chartEquiv_map hM i h h' s
end GlobalTheory.AbLaw.SecOn
