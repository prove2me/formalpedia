-- Prove2me | solution 1 for GlobalTheory.GrpSpread.exists_grpObj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:46:10.646668+00:00
-- url     : https://prove2.me/submissions/4fa939cf-fc2f-4c90-8c14-c26ade4eab91

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GrpObjDescendsToFgSubalgebra
import Theorems.Thm_GlobalTheory_GrpSpread_hom_ext_of_points
import Theorems.Thm_GlobalTheory_GrpSpread_eq_sq
import Theorems.Thm_GlobalTheory_GrpDense_hom_ext_of_points
import Theorems.Thm_GlobalTheory_GrpDense_pushPt_inv
import Theorems.Thm_GlobalTheory_GrpDense_pushPt_mul
import Theorems.Thm_GlobalTheory_GrpDense_pushPt_one
import Theorems.Thm_GlobalTheory_GrpDense_pushPt_surjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
namespace GlobalTheory.GrpSpread
open GrpDense
variable {Z U : Scheme.{0}} {j : U ⟶ Z}
variable {G : Over Z} {A : Over U} {φ : A.left ⟶ G.left}
private theorem flat_tensor_hom {S : Scheme.{0}} (X Y : Over S) [Flat X.hom] [Flat Y.hom] :
    Flat (X ⊗ Y).hom := by
  rw [Over.tensorObj_hom]
  infer_instance
private theorem flat_tensorUnit_hom {S : Scheme.{0}} : Flat (𝟙_ (Over S)).hom := by
  show Flat (𝟙 S)
  have : IsOpenImmersion (𝟙 S) := inferInstance
  infer_instance
end GlobalTheory.GrpSpread
namespace GlobalTheory
open GrpSpread
end GlobalTheory
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.GrpSpread
open GrpDense
variable {Z U : Scheme.{0}} {j : U ⟶ Z}
variable {G : Over Z} {A : Over U} {φ : A.left ⟶ G.left}
namespace GlobalTheory.GrpSpread
theorem _root_.solution (j : U ⟶ Z) [QuasiCompact j] [IsSchemeTheoreticallyDominant j] [Flat G.hom]
    [IsSeparated G.hom] [GrpObj A] [IsCommMonObj A] (h : IsPullback φ A.hom G.hom j)
    (m : G ⊗ G ⟶ G) (i : G ⟶ G) (e : 𝟙_ (Over Z) ⟶ G)
    (hm : sq h.w ≫ m.left = (μ[A]).left ≫ φ) (hi : φ ≫ i.left = (ι[A]).left ≫ φ)
    (he : j ≫ e.left = (η[A]).left ≫ φ) : ∃ _ : GrpObj G, IsCommMonObj G ∧ IsGrpPullback A G j φ := by
  have hm' : ∀ φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ :=
    fun φ₂ hφ => by rw [eq_sq h.w hφ, hm]
  have pmul : ∀ {T : Over U} (x y : T ⟶ A),
      lift (pushPt h.w x) (pushPt h.w y) ≫ m = pushPt h.w (x * y) :=
    fun x y => GrpDense.pushPt_mul h.w hm' x y
  have pinv : ∀ {T : Over U} (x : T ⟶ A), pushPt h.w x ≫ i = pushPt h.w x⁻¹ :=
    fun x => GrpDense.pushPt_inv h.w hi x
  have pone : ∀ (T : Over U), toUnit _ ≫ e = pushPt h.w (1 : T ⟶ A) :=
    fun T => GrpDense.pushPt_one h.w he T
  have psurj : ∀ (T : Over U) (x₀ : Over.mk (T.hom ≫ j) ⟶ G), ∃ x : T ⟶ A, pushPt h.w x = x₀ :=
    GrpDense.pushPt_surjective h
  have : Flat (𝟙_ (Over Z)).hom := flat_tensorUnit_hom
  have : Flat (G ⊗ G).hom := flat_tensor_hom G G
  have : Flat ((G ⊗ G) ⊗ G).hom := flat_tensor_hom _ G
  have : Flat (𝟙_ (Over Z) ⊗ G).hom := flat_tensor_hom _ G
  have : Flat (G ⊗ 𝟙_ (Over Z)).hom := flat_tensor_hom G _
  letI inst : GrpObj G :=
    { one := e
      mul := m
      inv := i
      one_mul := by
        apply hom_ext_of_points j
        intro T t
        obtain ⟨x, hx⟩ := psurj T (t ≫ snd _ _)
        have ht : t ≫ e ▷ G = lift (pushPt h.w 1) (pushPt h.w x) := by
          apply CartesianMonoidalCategory.hom_ext
          · rw [Category.assoc, whiskerRight_fst, ← Category.assoc, toUnit_unique (t ≫ fst _ _) (toUnit _),
              pone, lift_fst]
          · rw [Category.assoc, whiskerRight_snd, hx, lift_snd]
        rw [← Category.assoc, ht, pmul, _root_.one_mul, hx, leftUnitor_hom]
      mul_one := by
        apply hom_ext_of_points j
        intro T t
        obtain ⟨x, hx⟩ := psurj T (t ≫ fst _ _)
        have ht : t ≫ G ◁ e = lift (pushPt h.w x) (pushPt h.w 1) := by
          apply CartesianMonoidalCategory.hom_ext
          · rw [Category.assoc, whiskerLeft_fst, hx, lift_fst]
          · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, toUnit_unique (t ≫ snd _ _) (toUnit _),
              pone, lift_snd]
        rw [← Category.assoc, ht, pmul, _root_.mul_one, hx, rightUnitor_hom]
      mul_assoc := by
        apply hom_ext_of_points j
        intro T t
        obtain ⟨x, hx⟩ := psurj T (t ≫ fst _ _ ≫ fst _ _)
        obtain ⟨y, hy⟩ := psurj T (t ≫ fst _ _ ≫ snd _ _)
        obtain ⟨z, hz⟩ := psurj T (t ≫ snd _ _)
        have ht : t = lift (lift (pushPt h.w x) (pushPt h.w y)) (pushPt h.w z) := by
          apply CartesianMonoidalCategory.hom_ext
          · apply CartesianMonoidalCategory.hom_ext
            · simp only [Category.assoc, lift_fst]
              exact hx.symm
            · simp only [Category.assoc, lift_fst_assoc, lift_snd]
              exact hy.symm
          · simp only [lift_snd]
            exact hz.symm
        rw [ht, lift_whiskerRight_assoc, pmul, pmul, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc,
          pmul, pmul, _root_.mul_assoc]
      left_inv := by
        apply hom_ext_of_points j
        intro T t
        obtain ⟨x, hx⟩ := psurj T t
        rw [← hx, ← Category.assoc, comp_lift, pinv, Category.comp_id, pmul, _root_.inv_mul_cancel,
          ← Category.assoc, toUnit_unique (pushPt h.w x ≫ toUnit _) (toUnit _), pone]
      right_inv := by
        apply hom_ext_of_points j
        intro T t
        obtain ⟨x, hx⟩ := psurj T t
        rw [← hx, ← Category.assoc, comp_lift, pinv, Category.comp_id, pmul, _root_.mul_inv_cancel,
          ← Category.assoc, toUnit_unique (pushPt h.w x ≫ toUnit _) (toUnit _), pone] }
  refine ⟨inst, ⟨?_⟩, ⟨h, ?_⟩⟩
  · apply hom_ext_of_points j
    intro T t
    obtain ⟨x, hx⟩ := psurj T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := psurj T (t ≫ snd _ _)
    have ht : t = lift (pushPt h.w x) (pushPt h.w y) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [hx, lift_fst]
      · rw [hy, lift_snd]
    show t ≫ (β_ G G).hom ≫ m = t ≫ m
    rw [ht, lift_braiding_hom_assoc, pmul, pmul, _root_.mul_comm]
  · intro T x y x₀ y₀ hx hy
    have ex : x₀ = pushPt h.w x := Over.OverMorphism.ext hx
    have ey : y₀ = pushPt h.w y := Over.OverMorphism.ext hy
    rw [ex, ey]
    show (lift (pushPt h.w x) (pushPt h.w y) ≫ m).left = _
    rw [pmul]
    rfl
end GlobalTheory.GrpSpread
