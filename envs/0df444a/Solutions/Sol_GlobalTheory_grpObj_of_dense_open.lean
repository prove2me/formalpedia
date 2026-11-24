-- Prove2me | solution 1 for GlobalTheory.grpObj_of_dense_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:38:37.851606+00:00
-- url     : https://prove2.me/submissions/eb6e91f5-7cf0-4a7d-93b2-6e1ba4fd809f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Theorems.Thm_GlobalTheory_GrpDense_hom_ext_of_points
import Theorems.Thm_GlobalTheory_GrpDense_pushPt_surjective
import Theorems.Thm_GlobalTheory_GrpDense_pushPt_mul
import Theorems.Thm_GlobalTheory_GrpDense_pushPt_inv
import Theorems.Thm_GlobalTheory_GrpDense_pushPt_one
import Theorems.Thm_GlobalTheory_ExtUnique_flat_tensorObj
import Theorems.Thm_GlobalTheory_ExtUnique_flat_tensorUnit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GrpDense
namespace GlobalTheory
theorem _root_.solution :
    ∀ (Z U : Scheme.{0}) [IsIntegral Z] [Nonempty U] (j : U ⟶ Z) [IsOpenImmersion j] (G : Over Z) [Smooth G.hom]
      [IsSeparated G.hom] (A : Over U) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left),
      IsPullback φ A.hom G.hom j → ∀ (m : G ⊗ G ⟶ G) (i : G ⟶ G) (e : 𝟙_ (Over Z) ⟶ G),
      (∀ φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) →
      φ ≫ i.left = (ι[A]).left ≫ φ → j ≫ e.left = (η[A]).left ≫ φ →
      ∃ _ : GrpObj G, μ[G] = m ∧ η[G] = e ∧ ι[G] = i ∧ IsCommMonObj G ∧ IsGrpPullback A G j φ := by
  intro Z U _ _ j _ G _ _ A _ _ φ h m i e hm hi he
  have : Flat G.hom := inferInstance
  have : Flat (𝟙_ (Over Z)).hom := GlobalTheory.ExtUnique.flat_tensorUnit
  have : Flat (G ⊗ G).hom := GlobalTheory.ExtUnique.flat_tensorObj G G
  have : Flat ((G ⊗ G) ⊗ G).hom := GlobalTheory.ExtUnique.flat_tensorObj (G ⊗ G) G
  have : Flat (𝟙_ (Over Z) ⊗ G).hom := GlobalTheory.ExtUnique.flat_tensorObj _ G
  have : Flat (G ⊗ 𝟙_ (Over Z)).hom := GlobalTheory.ExtUnique.flat_tensorObj G _
  have hext : ∀ {X : Over Z} [Flat X.hom] (f g : X ⟶ G),
      (∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) → f = g :=
    fun f g H => hom_ext_of_points j H
  have mulP : ∀ {T : Over U} (x y : T ⟶ A),
      lift (pushPt h.w x) (pushPt h.w y) ≫ m = pushPt h.w (x * y) :=
    fun x y => pushPt_mul h.w hm x y
  have invP : ∀ {T : Over U} (x : T ⟶ A), pushPt h.w x ≫ i = pushPt h.w x⁻¹ :=
    fun x => pushPt_inv h.w hi x
  have oneP : ∀ (T : Over U), toUnit _ ≫ e = pushPt h.w (1 : T ⟶ A) :=
    fun T => pushPt_one h.w he T
  have surj := pushPt_surjective h
  letI inst : GrpObj G :=
    { one := e
      mul := m
      inv := i
      one_mul := by
        apply hext
        intro T t
        obtain ⟨y, hy⟩ := surj T (t ≫ snd _ _)
        have ht : t = lift (toUnit _) (pushPt h.w y) :=
          hom_ext _ _ (toUnit_unique _ _) (by rw [lift_snd, hy])
        rw [ht]
        simp only [lift_whiskerRight_assoc, lift_leftUnitor_hom]
        rw [oneP, mulP, _root_.one_mul]
      mul_one := by
        apply hext
        intro T t
        obtain ⟨x, hx⟩ := surj T (t ≫ fst _ _)
        have ht : t = lift (pushPt h.w x) (toUnit _) :=
          hom_ext _ _ (by rw [lift_fst, hx]) (toUnit_unique _ _)
        rw [ht]
        simp only [lift_whiskerLeft_assoc, lift_rightUnitor_hom]
        rw [oneP, mulP, _root_.mul_one]
      mul_assoc := by
        apply hext
        intro T t
        obtain ⟨x, hx⟩ := surj T (t ≫ fst _ _ ≫ fst _ _)
        obtain ⟨y, hy⟩ := surj T (t ≫ fst _ _ ≫ snd _ _)
        obtain ⟨z, hz⟩ := surj T (t ≫ snd _ _)
        have ht : t = lift (lift (pushPt h.w x) (pushPt h.w y)) (pushPt h.w z) := by
          refine hom_ext _ _ ?_ (by rw [lift_snd, hz])
          rw [lift_fst]
          exact hom_ext _ _ (by rw [lift_fst, hx, Category.assoc]) (by rw [lift_snd, hy, Category.assoc])
        rw [ht]
        simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc,
          mulP, _root_.mul_assoc]
      left_inv := by
        apply hext
        intro T t
        obtain ⟨x, rfl⟩ := surj T t
        simp only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc, invP, mulP, _root_.inv_mul_cancel, oneP]
      right_inv := by
        apply hext
        intro T t
        obtain ⟨x, rfl⟩ := surj T t
        simp only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc, invP, mulP, _root_.mul_inv_cancel, oneP] }
  refine ⟨inst, rfl, rfl, rfl, ⟨?_⟩, ?_⟩
  · change (β_ G G).hom ≫ m = m
    apply hext
    intro T t
    obtain ⟨x, hx⟩ := surj T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := surj T (t ≫ snd _ _)
    have ht : t = lift (pushPt h.w x) (pushPt h.w y) :=
      hom_ext _ _ (by rw [lift_fst, hx]) (by rw [lift_snd, hy])
    rw [ht, lift_braiding_hom_assoc, mulP, mulP, _root_.mul_comm]
  · unfold IsGrpPullback
    refine ⟨h, ?_⟩
    intro T x y x₀ y₀ hx hy
    have e₀ : x₀ = pushPt h.w x := Over.OverMorphism.ext hx
    have e₁ : y₀ = pushPt h.w y := Over.OverMorphism.ext hy
    subst e₀ e₁
    rw [Hom.mul_def]
    exact congrArg (fun t => t.left) (mulP x y)
end GlobalTheory
