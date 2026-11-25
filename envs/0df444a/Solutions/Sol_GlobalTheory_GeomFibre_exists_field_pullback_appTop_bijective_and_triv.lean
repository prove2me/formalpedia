-- Prove2me | solution 1 for GlobalTheory.GeomFibre.exists_field_pullback_appTop_bijective_and_triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:45:25.514862+00:00
-- url     : https://prove2.me/submissions/d34a7863-7fb0-4dd1-9bd8-3e55b8438c36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFieldPullbackAppTopBijectiveAndTriv
import Theorems.Thm_GlobalTheory_GeomFibre_bijective_appTop
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_pullGen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.GeomFibre
namespace GlobalTheory.GeomFibre
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → IsProper f → GeometricallyIntegral f → ∀ (K : Type) [Field K] (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → Triv (M.pull π) → ∃ (K₀ : Type) (_ : Field K₀) (g₀ : R →+* K₀) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K₀)), RingHom.ker g₀ = RingHom.ker g ∧ IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) ∧ Function.Bijective f₀.appTop.hom ∧ Triv (M.pull π₀) := by
  intro R _ X f M _ _ _ K _ g X' π f' h ⟨t, ht⟩
  let a : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have h₁ := IsPullback.of_hasPullback f' (Spec.map (CommRingCat.ofHom a))
  have h₂ : IsPullback (pullback.fst f' (Spec.map (CommRingCat.ofHom a)) ≫ π)
      (pullback.snd f' (Spec.map (CommRingCat.ofHom a))) f (Spec.map (CommRingCat.ofHom (a.comp g))) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact h₁.paste_horiz h
  have : IsIntegral (pullback f' (Spec.map (CommRingCat.ofHom a))) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ h₂
  have : IsProper (pullback.snd f' (Spec.map (CommRingCat.ofHom a))) :=
    MorphismProperty.of_isPullback (P := @IsProper) h₂ inferInstance
  refine ⟨AlgebraicClosure K, inferInstance, a.comp g, _, _, _, RingHom.ker_comp_of_injective g a.injective,
    h₂, bijective_appTop _ _, ?_⟩
  exact ⟨_, LB.isGen_pullGen M _ _ t ht _⟩
end GlobalTheory.GeomFibre
