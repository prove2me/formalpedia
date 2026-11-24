-- Prove2me | solution 1 for GlobalTheory.ThetaModelGroup.grpObj_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:31:12.671562+00:00
-- url     : https://prove2.me/submissions/80517caa-7b9e-451c-971d-17bde6f03b99

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LocallyOfFiniteTypeTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaModelGroup
namespace GlobalTheory.ThetaModelGroup
theorem _root_.solution {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C] (X : C)
    {A : Type*} [AddCommGroup A] (ex : A → (𝟙_ C ⟶ X)) (hs : Function.Surjective ex) (m : X ⊗ X ⟶ X) (i : X ⟶ X)
    (hm : ∀ z w, lift (ex z) (ex w) ≫ m = ex (z + w)) (hi : ∀ z, ex z ≫ i = ex (-z))
    (e1 : ∀ f g : X ⟶ X, (∀ y : 𝟙_ C ⟶ X, y ≫ f = y ≫ g) → f = g)
    (e2 : ∀ f g : X ⊗ X ⟶ X, (∀ y : 𝟙_ C ⟶ X ⊗ X, y ≫ f = y ≫ g) → f = g)
    (e3 : ∀ f g : (X ⊗ X) ⊗ X ⟶ X, (∀ y : 𝟙_ C ⟶ (X ⊗ X) ⊗ X, y ≫ f = y ≫ g) → f = g) :
    ∃ (_ : GrpObj X), IsCommMonObj X ∧ ∀ z w, ex (z + w) = ex z * ex w := by
  have hu : ∀ y : 𝟙_ C ⟶ X, y ≫ toUnit X = 𝟙 _ := fun y => Subsingleton.elim _ _
  have p2 : ∀ y : 𝟙_ C ⟶ X ⊗ X, ∃ z w, y = lift (ex z) (ex w) := fun y => by
    obtain ⟨z, hz⟩ := hs (y ≫ fst _ _)
    obtain ⟨w, hw⟩ := hs (y ≫ snd _ _)
    exact ⟨z, w, by rw [hz, hw]; ext <;> simp⟩
  have p3 : ∀ y : 𝟙_ C ⟶ (X ⊗ X) ⊗ X, ∃ z w v, y = lift (lift (ex z) (ex w)) (ex v) := fun y => by
    obtain ⟨z, w, hz⟩ := p2 (y ≫ fst _ _)
    obtain ⟨v, hw⟩ := hs (y ≫ snd _ _)
    exact ⟨z, w, v, by rw [← hz, hw]; ext <;> simp⟩
  let G : GrpObj X :=
    { one := ex 0
      mul := m
      inv := i
      one_mul := by
        rw [← cancel_epi (λ_ X).inv, Iso.inv_hom_id]
        refine e1 _ _ fun y => ?_
        obtain ⟨z, rfl⟩ := hs y
        have : ex z ≫ (λ_ X).inv ≫ ex 0 ▷ X = lift (ex 0) (ex z) := by
          ext
          · simp [reassoc_of% hu]
          · simp
        rw [reassoc_of% this, hm, zero_add, Category.comp_id]
      mul_one := by
        rw [← cancel_epi (ρ_ X).inv, Iso.inv_hom_id]
        refine e1 _ _ fun y => ?_
        obtain ⟨z, rfl⟩ := hs y
        have : ex z ≫ (ρ_ X).inv ≫ X ◁ ex 0 = lift (ex z) (ex 0) := by
          ext
          · simp
          · simp [reassoc_of% hu]
        rw [reassoc_of% this, hm, add_zero, Category.comp_id]
      mul_assoc := by
        refine e3 _ _ fun y => ?_
        obtain ⟨z, w, v, rfl⟩ := p3 y
        rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, hm, hm, hm, hm,
          add_assoc]
      left_inv := by
        refine e1 _ _ fun y => ?_
        obtain ⟨z, rfl⟩ := hs y
        rw [comp_lift_assoc, hi, Category.comp_id, hm, reassoc_of% hu, neg_add_cancel]
      right_inv := by
        refine e1 _ _ fun y => ?_
        obtain ⟨z, rfl⟩ := hs y
        rw [comp_lift_assoc, hi, Category.comp_id, hm, reassoc_of% hu, add_neg_cancel] }
  refine ⟨G, ⟨e2 _ _ fun y => ?_⟩, fun z w => (hm z w).symm⟩
  obtain ⟨z, w, rfl⟩ := p2 y
  change _ ≫ _ ≫ m = _ ≫ m
  rw [lift_braiding_hom_assoc, hm, hm, add_comm]
end GlobalTheory.ThetaModelGroup
