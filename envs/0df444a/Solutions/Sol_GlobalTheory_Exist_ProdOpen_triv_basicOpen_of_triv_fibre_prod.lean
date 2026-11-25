-- Prove2me | solution 1 for GlobalTheory.Exist.ProdOpen.triv_basicOpen_of_triv_fibre_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:34:26.593323+00:00
-- url     : https://prove2.me/submissions/c8c9937c-1202-4db4-b091-7aee07baa55e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivBasicOpenOfTrivFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TrivProdOfSmallExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LineBundleTrivialBasicOpenOfTrivialFibreProduct
import Theorems.Thm_GlobalTheory_Exist_ProdOpen_isPullback_prodMap
import Theorems.Thm_GlobalTheory_Exist_ProdOpen_triv_lift_prod
import Theorems.Thm_GlobalTheory_Exist_ProdOpen_surjective_prod
import Theorems.Thm_GlobalTheory_AbLaw_CubeOpen_exists_ann
import Theorems.Thm_GlobalTheory_AbLaw_CubeOpen_triv_comp
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_seesaw


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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.AbLaw.CubeOpen
noncomputable section
open GlobalTheory GlobalTheory.Exist GlobalTheory.Exist.ProdOpen
namespace GlobalTheory.Exist.ProdOpen
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (x₀ : 𝟙_ (Over (Sp R)) ⟶ X) (y₀ : 𝟙_ (Over (Sp R)) ⟶ Y), Flat X.hom → Flat Y.hom → IsProper X.hom → IsProper Y.hom → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X ⊗ Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → ∀ M : LB (X ⊗ Y).left, M.IsLB → Nonempty (Perf (X ⊗ Y).hom M) → Triv (M.pull (lift (𝟙 X) (toUnit X ≫ y₀)).left) → Triv (M.pull (lift (toUnit Y ≫ x₀) (𝟙 Y)).left) → ∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ (X ⊗ Y).left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π₀ f₀ (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom g₀)) → Triv (M.pull π₀) → ∃ r : R, g₀ r ≠ 0 ∧ Triv (M.pull ((X ⊗ Y).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen r)).ι) := by
  intro R _ X Y x₀ y₀ _ _ _ _ hX hY hXY M hM hP h₁ h₂ K _ g₀ X₀ π₀ f₀ h₀ ht₀
  haveI : IsProper (X ⊗ Y).hom := inferInstanceAs (IsProper (pullback.fst X.hom Y.hom ≫ X.hom))
  obtain ⟨r, I, hr, hI, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R _ (X ⊗ Y).hom M hM hP inferInstance
    (surjective_prod X Y x₀ y₀) K g₀ X₀ π₀ f₀ h₀ (hXY K g₀ X₀ π₀ f₀ h₀) ht₀
  haveI : (RingHom.ker g₀).IsPrime := RingHom.ker_isPrime g₀
  obtain ⟨c, hc, hcI⟩ := exists_ann (RingHom.ker g₀) I hI
    ((H K g₀ X₀ π₀ f₀ h₀ (Ne.isUnit hr)).1 ht₀) (fun T _ _ g e hu he he' hle => by
      refine (H T g _ _ _ (isPullback_prodMap (Spec.map (CommRingCat.ofHom g)) X Y) (hu r hr)).1 ?_
      refine triv_lift_prod X Y x₀ y₀ hX hY M hM h₁ h₂ T g e he he' fun X' π f' hp => ?_
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at hp
      exact (H _ _ X' π f' hp ((hu r hr).map (Ideal.Quotient.mk (Ideal.span {e})))).2 hle)
  refine ⟨r * c, by rw [map_mul]; exact mul_ne_zero hr hc, ?_⟩
  let L := Localization.Away (r * c)
  have hu : IsUnit (algebraMap R L (r * c)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul, IsUnit.mul_iff] at hu
  have hp := IsPullback.of_hasPullback (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom (algebraMap R L)))
  have ht := (H L (algebraMap R L) _ _ _ hp hu.1).2 fun x hx => by
    rw [RingHom.mem_ker, ← hu.2.mul_right_eq_zero, ← map_mul, hcI x hx, map_zero]
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R L))) :=
    IsOpenImmersion.of_isLocalization (r * c)
  have hsub : Set.range (((X ⊗ Y).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen (r * c))).ι ≫ (X ⊗ Y).hom) ⊆
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap R L))) := by
    rintro _ ⟨y, rfl⟩
    have := PrimeSpectrum.localization_away_comap_range L (r * c)
    change _ ∈ Set.range (PrimeSpectrum.comap (algebraMap R L))
    rw [this]
    exact y.2
  exact triv_comp (hp.lift _ _ (IsOpenImmersion.lift_fac _ _ hsub).symm) (hp.lift_fst _ _ _) ht
end GlobalTheory.Exist.ProdOpen
