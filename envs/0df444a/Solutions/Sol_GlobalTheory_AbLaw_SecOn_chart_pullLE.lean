-- Prove2me | solution 1 for GlobalTheory.AbLaw.SecOn.chart_pullLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:39:06.061342+00:00
-- url     : https://prove2.me/submissions/e114eaf6-f574-4ecd-bf57-28638a475cfc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_chart_apply
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_coord_pullLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_pull


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
theorem _root_.solution (hM : M.IsLB) (π : X' ⟶ X) {V' : X'.Opens} (e : V' ≤ π ⁻¹ᵁ V)
    (j : (M.pull π).ι) (h : V ≤ M.U (j PUnit.unit)) (h' : V' ≤ (M.pull π).U j) (s : SecOn M V) :
    chart (LB.isLB_pull hM π) j h' (pullLE M π V V' e s) =
      (π.appLE V V' e).hom (chart hM (j PUnit.unit) h s) := by
  rw [chart_apply, chart_apply, coord_pullLE, resG_appLE, appLE_resG]
end GlobalTheory.AbLaw.SecOn
