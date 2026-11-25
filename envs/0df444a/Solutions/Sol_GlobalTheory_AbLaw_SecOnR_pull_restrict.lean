-- Prove2me | solution 1 for GlobalTheory.AbLaw.SecOnR.pull_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:26:55.718959+00:00
-- url     : https://prove2.me/submissions/5a659ba6-17b6-4bdb-a36a-aedfa240c71b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_restrict_pullLE
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_pullLE_restrict

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
open GlobalTheory.AbLaw.SecOnR
variable (f : X ⟶ Spec (CommRingCat.of R)) {L M H : LB X} {V W : X.Opens}
variable {f}
variable (f)
variable {f} {f' : X' ⟶ Spec (CommRingCat.of R')} {π : X' ⟶ X} {g : R →+* R'}
  (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g))
namespace GlobalTheory.AbLaw.SecOnR
theorem _root_.solution {V' W' : X'.Opens} (h : W ≤ V) (h' : W' ≤ V') (e : V' ≤ π ⁻¹ᵁ V)
    (e' : W' ≤ π ⁻¹ᵁ W) (s : SecOnR f M V) :
    pull M w W W' e' (restrict f M h s) = restrict f' _ h' (pull M w V V' e s) :=
  (SecOn.pullLE_restrict π h e' _).trans (SecOn.restrict_pullLE π e h' _).symm
end GlobalTheory.AbLaw.SecOnR
