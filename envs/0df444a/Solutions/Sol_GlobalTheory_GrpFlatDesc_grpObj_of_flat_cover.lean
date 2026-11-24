-- Prove2me | solution 1 for GlobalTheory.GrpFlatDesc.grpObj_of_flat_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:09:43.035191+00:00
-- url     : https://prove2.me/submissions/9b20cdd1-28c1-41f2-a9a3-6e3a47610562

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupSchemeMorphismDescends
import Theorems.Thm_GlobalTheory_GrpFlatDesc_hom_ext_of_points
import Theorems.Thm_GlobalTheory_GrpDense_hom_ext_of_points
import Theorems.Thm_GlobalTheory_GrpDense_pushPt_inv
import Theorems.Thm_GlobalTheory_GrpDense_pushPt_mul
import Theorems.Thm_GlobalTheory_GrpDense_pushPt_one
import Theorems.Thm_GlobalTheory_GrpDense_pushPt_surjective


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
open GlobalTheory GlobalTheory.GrpFlatDesc
open GrpDense MorphismProperty
variable {Z U : Scheme.{0}}
namespace GlobalTheory.GrpFlatDesc
theorem _root_.solution (j : U ⟶ Z) [Flat j] [Surjective j] (G : Over Z) (A : Over U) [GrpObj A]
    [IsCommMonObj A] (φ : A.left ⟶ G.left) (h : IsPullback φ A.hom G.hom j) (m : G ⊗ G ⟶ G) (i : G ⟶ G)
    (e : 𝟙_ (Over Z) ⟶ G)
    (hm : ∀ φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ)
    (hi : φ ≫ i.left = (ι[A]).left ≫ φ) (he : j ≫ e.left = (η[A]).left ≫ φ) :
    ∃ _ : GrpObj G, μ[G] = m ∧ η[G] = e ∧ ι[G] = i ∧ IsCommMonObj G ∧ IsGrpPullback A G j φ := by
  have hM := fun {T : Over U} => pushPt_mul h.w hm (T := T)
  have hI := fun {T : Over U} => pushPt_inv h.w hi (T := T)
  have hE := pushPt_one h.w he
  letI : MonObj G :=
    { one := e
      mul := m
      one_mul := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (toUnit _) (pushPt h.w x) :=
          CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (by rw [lift_snd, hx])
        rw [lift_whiskerRight_assoc, hE, hM, _root_.one_mul, lift_leftUnitor_hom]
      mul_one := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _)
        obtain rfl : t = lift (pushPt h.w x) (toUnit _) :=
          CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (toUnit_unique _ _)
        rw [lift_whiskerLeft_assoc, hE, hM, _root_.mul_one, lift_rightUnitor_hom]
      mul_assoc := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ fst _ _)
        obtain ⟨y, hy⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ snd _ _)
        obtain ⟨z, hz⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (lift (pushPt h.w x) (pushPt h.w y)) (pushPt h.w z) := by
          ext <;> simp [hx, hy, hz]
        rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, hM, hM, hM, hM,
          _root_.mul_assoc] }
  letI : GrpObj G :=
    { inv := i
      left_inv := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, inv_mul_cancel, comp_toUnit_assoc, hE]
      right_inv := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, mul_inv_cancel, comp_toUnit_assoc, hE] }
  refine ⟨inferInstance, rfl, rfl, rfl, ⟨GrpFlatDesc.hom_ext_of_points j fun T t => ?_⟩, h, fun T x y x₀ y₀ hx hy => ?_⟩
  · obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := pushPt_surjective h T (t ≫ snd _ _)
    obtain rfl : t = lift (pushPt h.w x) (pushPt h.w y) := by ext <;> simp [hx, hy]
    change _ ≫ _ ≫ m = _ ≫ m
    rw [lift_braiding_hom_assoc, hM, hM, _root_.mul_comm]
  · obtain rfl : x₀ = pushPt h.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = pushPt h.w y := Over.OverMorphism.ext hy
    exact congrArg (fun z => z.left) (hM x y)
end GlobalTheory.GrpFlatDesc
