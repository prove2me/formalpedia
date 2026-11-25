-- Prove2me | solution 1 for GlobalTheory.Unif.exists_finFlat_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:22:57.961892+00:00
-- url     : https://prove2.me/submissions/88fcf10f-06f4-4957-9ffa-94d705592cf0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FinFlatChartOfOpenImmersion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct
open GlobalTheory GlobalTheory.Unif
namespace GlobalTheory.Unif
theorem _root_.solution (R A : Type) [CommRing R] [CommRing A] [IsDomain R]
    [IsNoetherianRing R] (φ : R →+* A) (hφ : φ.Finite) (hi : Function.Injective φ) :
    ∃ (Y Z : Scheme.{0}) (j : Y ⟶ Spec (CommRingCat.of A)) (i : Z ⟶ Spec (CommRingCat.of R))
      (p : Y ⟶ Z), IsOpenImmersion j ∧ IsOpenImmersion i ∧ IsFinite p ∧ Flat p ∧ Surjective p ∧
      Nonempty Z ∧ p ≫ i = j ≫ Spec.map (CommRingCat.ofHom φ) := by
  algebraize [φ]
  have : Module.FinitePresentation R A := Module.finitePresentation_of_finite R A
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors R) (LocalizedModule.mkLinearMap (nonZeroDivisors R) A) (FractionRing R)
  have hfree' : Module.Free (Localization.Away r) (Localization.Away r ⊗[R] A) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers r) A)
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R (Localization.Away r) A)
  have h1 : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
    rw [IsFinite.SpecMap_iff]; exact hφ
  have h2 : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    ⟨hφ.to_isIntegral.comap_surjective hi⟩
  have h3 : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) :=
    inferInstance
  have hd : IsDomain (Localization.Away r) :=
    IsLocalization.isDomain_localization (Submonoid.powers_le.mpr hr)
  refine ⟨_, _, _, _, _, MorphismProperty.of_isPullback hpb h3, h3,
    MorphismProperty.of_isPullback hpb.flip h1, ?_, MorphismProperty.of_isPullback hpb.flip h2,
    inferInstanceAs (Nonempty (PrimeSpectrum (Localization.Away r))), hpb.w⟩
  rw [Flat.SpecMap_iff]
  exact (RingHom.flat_algebraMap_iff (R := Localization.Away r)
    (S := Localization.Away r ⊗[R] A)).mpr inferInstance
end GlobalTheory.Unif
