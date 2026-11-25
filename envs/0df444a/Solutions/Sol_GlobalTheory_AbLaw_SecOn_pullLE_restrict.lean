-- Prove2me | solution 1 for GlobalTheory.AbLaw.SecOn.pullLE_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:11:59.803998+00:00
-- url     : https://prove2.me/submissions/374fc4f7-53b3-4d2b-ba34-3315325dd2a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_pull_restrict

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
theorem _root_.solution (π : X' ⟶ X) {W' : X'.Opens} (h : W ≤ V) (e : W' ≤ π ⁻¹ᵁ W)
    (s : SecOn M V) :
    pullLE M π W W' e (restrict M h s) = pullLE M π V W' (e.trans (π.preimage_mono h)) s :=
  (congrArg (restrict (M.pull π) e) (pull_restrict π h s)).trans (restrict_restrict _ _ _)
end GlobalTheory.AbLaw.SecOn
