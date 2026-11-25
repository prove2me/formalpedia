-- Prove2me | solution 1 for GlobalTheory.sec_eq_zero_of_sval_finite_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:59:08.448356+00:00
-- url     : https://prove2.me/submissions/a09211e2-cc5a-441b-ba34-b39131d07336

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfThickeningsOfSection
import Theorems.Thm_GlobalTheory_sec_eq_zero_of_thickenings_of_section
import Theorems.Thm_GlobalTheory_app_sec_eq_zero_of_sval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_isLB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] (I : Ideal R) (T B : Over (Spec (CommRingCat.of R))) [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] [GrpObj B] [Smooth B.hom] [GeometricallyConnected B.hom], (∀ r ∈ I, scal T.hom r ∈ Ideal.jacobson (⊥ : Ideal Γ(T.left, ⊤))) → ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → ((T ⊗ B).left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ (T ⊗ B).hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0) → ∀ j, d.f j = 0 := by
  intro R _ I T B _ _ _ _ _ hI X L hL K _ φ ε d hd j
  let ψ : CommRingCat.of R ⟶ Γ(T.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ T.hom.appTop
  have hψ : T.left.isoSpec.hom ≫ Spec.map ψ = T.hom := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  let H : Over (Spec (CommRingCat.of Γ(T.left, ⊤))) :=
    Over.mk (pullback.fst T.hom B.hom ≫ T.left.isoSpec.hom)
  have : Smooth H.hom := inferInstanceAs (Smooth (pullback.fst T.hom B.hom ≫ T.left.isoSpec.hom))
  have : GeometricallyConnected H.hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_iso (IsPullback.of_hasPullback T.hom B.hom).flip (Iso.refl _) (Iso.refl _)
        T.left.isoSpec (Iso.refl _) (fst' := pullback.snd T.hom B.hom) (snd' := H.hom)
        (f' := B.hom) (g' := Spec.map ψ) (by simp) (Category.id_comp _).symm (by simp)
        (by simp [hψ])) ‹GeometricallyConnected B.hom›
  let σ : T ⟶ T ⊗ B := lift (𝟙 T) (toUnit T ≫ η[B])
  have hσ : σ.left ≫ pullback.fst T.hom B.hom = 𝟙 _ :=
    congrArg CommaMorphism.left (lift_fst (𝟙 T) (toUnit T ≫ η[B]))
  let e : 𝟙_ _ ⟶ H := Over.homMk (T.left.isoSpec.inv ≫ σ.left) (by
    change (T.left.isoSpec.inv ≫ σ.left) ≫ pullback.fst T.hom B.hom ≫ T.left.isoSpec.hom = 𝟙 _
    rw [Category.assoc, reassoc_of% hσ, Iso.inv_hom_id])
  refine sec_eq_zero_of_thickenings_of_section Γ(T.left, ⊤) (I.map ψ.hom)
    (Ideal.map_le_iff_le_comap.2 hI) H e (LB.LinComb L φ ε) (DVR.linComb_isLB L hL φ ε) d
    (fun n j ↦ app_sec_eq_zero_of_sval hL d _ (hd n _ _ ⟨pullback.snd H.hom (thick _ (I.map ψ.hom) n) ≫
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((I.map ψ.hom) ^ (n + 1)) ψ.hom
          (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map))), ?_⟩) j) j
  change _ = pullback.fst H.hom (thick _ (I.map ψ.hom) n) ≫ pullback.fst T.hom B.hom ≫ T.hom
  have h1 : pullback.fst T.hom B.hom ≫ T.hom = H.hom ≫ Spec.map ψ :=
    (congrArg (pullback.fst T.hom B.hom ≫ ·) hψ.symm).trans (Category.assoc _ _ _).symm
  rw [h1, pullback.condition_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  rfl
end GlobalTheory
