-- Prove2me | solution 1 for GlobalTheory.SS.TorusSlice.exists_goodOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:49:10.498792+00:00
-- url     : https://prove2.me/submissions/fc9c4029-f34c-49b6-a46f-a54ed1741345

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnits
import Theorems.Thm_GlobalTheory_SS_TorusSlice_isOpenImmersion_sweep
import Theorems.Thm_GlobalTheory_SS_TorusSlice_goodOpen_of_equivar

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
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.TorusSlice
variable {S : Scheme.{0}}
variable {X : Type} [AddCommGroup X]
namespace GlobalTheory.SS.TorusSlice
theorem _root_.solution [IsAffine S] [Module.Finite ℤ X] {G Y : Over S} [GrpObj G] [QuasiSeparated G.hom]
    (i : splitTorus S X ⟶ G) [IsMonHom i] (j : Y ⟶ G) [IsOpenImmersion j.left] [IsAffine Y.left]
    (σ₀ : Y ⟶ splitTorus S X) (h₀ : Equivar i j σ₀) (y : 𝟙_ (Over S) ⟶ Y) :
    ∃ V, GoodOpen i V ∧ ∀ s, (y ≫ j).left s ∈ V := by
  let T := splitTorus S X
  let σ : Y ⟶ T := σ₀ * (toUnit Y ≫ (y ≫ σ₀)⁻¹)
  have hσ : Equivar i j σ := fun Z t a a' h => by
    simp only [σ, MonObj.comp_mul, h₀ Z t a a' h, _root_.mul_assoc]
    rw [← Category.assoc, ← Category.assoc a, toUnit_unique (a' ≫ toUnit Y) (a ≫ toUnit Y)]
  have hy : y ≫ σ = 1 := by
    simp only [σ, MonObj.comp_mul]
    rw [← Category.assoc, toUnit_unique (y ≫ toUnit Y) (𝟙 _), Category.id_comp, mul_inv_cancel]
  let Y₁ := pullback σ η[T]
  let e : Y₁ ⟶ Y := pullback.fst _ _
  have he : IsPullback e (toUnit Y₁) σ η[T] := by
    rw [toUnit_unique (toUnit Y₁) (pullback.snd σ η[T])]
    exact IsPullback.of_hasPullback _ _
  have he1 : e ≫ σ = 1 := he.w
  have : IsAffine T.left := isAffine_of_isAffineHom T.hom
  have : IsAffine (𝟙_ (Over S)).left := ‹IsAffine S›
  have : IsAffineHom e.left := MorphismProperty.of_isPullback (P := @IsAffineHom) (he.map (Over.forget S)).flip
    (inferInstanceAs (IsAffineHom (η[T]).left))
  have : IsAffine Y₁.left := isAffine_of_isAffineHom e.left
  have : IsAffineHom (snd T Y₁).left := inferInstanceAs (IsAffineHom (pullback.snd T.hom Y₁.hom))
  have : IsAffine (T ⊗ Y₁).left := isAffine_of_isAffineHom (snd T Y₁).left
  have : QuasiCompact (j.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact j.left := QuasiCompact.of_comp _ G.hom
  have := isOpenImmersion_sweep i j σ hσ e he
  refine ⟨_, goodOpen_of_equivar i ((fst T Y₁ ≫ i) * (snd T Y₁ ≫ e ≫ j)) (fst T Y₁) (fun Z t p p' h => ?_)
    (fun Z t p => ⟨lift (t * (p ≫ fst _ _)) (p ≫ snd _ _), ?_⟩), fun s => ?_⟩
  · have h1 : (p' ≫ snd T Y₁ ≫ e) ≫ j =
        (((p' ≫ fst T Y₁)⁻¹ * (t * (p ≫ fst T Y₁))) ≫ i) * ((p ≫ snd T Y₁ ≫ e) ≫ j) := by
      simp only [MonObj.comp_mul] at h
      rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, _root_.mul_assoc, eq_inv_mul_iff_mul_eq, _root_.mul_assoc]
      simpa using h
    have h2 := hσ _ _ _ _ h1
    simp only [Category.assoc, he1, MonObj.comp_one, _root_.mul_one] at h2
    exact (eq_inv_mul_iff_mul_eq.1 h2 ▸ (_root_.mul_one _).symm)
  · simp [MonObj.comp_mul, MonObj.mul_comp, _root_.mul_assoc]
  · obtain ⟨y₁, hy₁, -⟩ := he.exists_lift y (toUnit _) hy
    have : y ≫ j = lift 1 y₁ ≫ ((fst T Y₁ ≫ i) * (snd T Y₁ ≫ e ≫ j)) := by
      simp [MonObj.comp_mul, reassoc_of% hy₁]
    rw [this, Scheme.Hom.image_top_eq_opensRange, Over.comp_left, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
end GlobalTheory.SS.TorusSlice
