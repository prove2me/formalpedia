-- Prove2me | solution 1 for GlobalTheory.SS.free_localizedModule_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:23:20.849799+00:00
-- url     : https://prove2.me/submissions/6920fe36-a926-461e-a5d7-8168f4992cb5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothFreeAway

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS
namespace GlobalTheory.SS
theorem _root_.solution {C : Type} [CommRing C] (M : Type) [AddCommGroup M] [Module C M]
    (r g : C) (h : Module.Free (Localization.Away r) (LocalizedModule (Submonoid.powers r) M)) :
    Module.Free (Localization.Away (r * g)) (LocalizedModule (Submonoid.powers (r * g)) M) := by
  let _ : Algebra (Localization.Away r) (Localization.Away (r * g)) :=
    (IsLocalization.Away.awayToAwayRight (S := Localization.Away r) r g).toAlgebra
  have _ : IsScalarTower C (Localization.Away r) (Localization.Away (r * g)) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      (IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away r) r g c).symm
  let _ : Module (Localization.Away r) (LocalizedModule (Submonoid.powers (r * g)) M) :=
    Module.compHom _ (algebraMap (Localization.Away r) (Localization.Away (r * g)))
  have _ : IsScalarTower (Localization.Away r) (Localization.Away (r * g))
      (LocalizedModule (Submonoid.powers (r * g)) M) :=
    ⟨fun a b x => by
      show (a • b) • x = algebraMap _ (Localization.Away (r * g)) a • b • x
      rw [Algebra.smul_def, mul_smul]⟩
  have _ : IsScalarTower C (Localization.Away r) (LocalizedModule (Submonoid.powers (r * g)) M) :=
    ⟨fun c a x => by
      show algebraMap _ (Localization.Away (r * g)) (c • a) • x =
        c • algebraMap _ (Localization.Away (r * g)) a • x
      rw [Algebra.smul_def, map_mul, mul_smul,
        ← IsScalarTower.algebraMap_apply C (Localization.Away r) (Localization.Away (r * g)),
        algebraMap_smul]⟩
  have hr := LocalizedModule.isBaseChange (Submonoid.powers r) M
  have hrg := LocalizedModule.isBaseChange (Submonoid.powers (r * g)) M
  rw [← hr.lift_comp (LocalizedModule.mkLinearMap (Submonoid.powers (r * g)) M)] at hrg
  exact Module.Free.of_equiv (hr.of_comp hrg).equiv
end GlobalTheory.SS
