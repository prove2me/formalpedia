-- Prove2me | solution 1 for GlobalTheory.CosetQuotient.exists_grpObj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:00:03.687851+00:00
-- url     : https://prove2.me/submissions/e5904c3f-8b7d-4566-a6c0-cc05297b74fc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGroupQuotientPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open GlobalTheory
open GlobalTheory.CosetQuotient
universe v u
namespace GlobalTheory.CosetQuotient
theorem _root_.solution {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    [BraidedCategory C] {G T B : C} [GrpObj G] [IsCommMonObj G] [GrpObj T]
    (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [Mono i]
    [EffectiveEpi q] [EffectiveEpi (q ⊗ₘ q)] [Epi ((q ⊗ₘ q) ⊗ₘ q)]
    (h : ∀ (Z : C) (g g' : Z ⟶ G), g ≫ q = g' ≫ q ↔ ∃ t : Z ⟶ T, g' = (t ≫ i) * g) :
    ∃ (_ : GrpObj B), IsCommMonObj B ∧ IsMonHom q ∧ IsPullback i (toUnit _) q (η[B]) := by
  classical
  have same : ∀ {Z : C} (t : Z ⟶ T) (g : Z ⟶ G), ((t ≫ i) * g) ≫ q = g ≫ q :=
    fun t g => ((h _ _ _).2 ⟨t, rfl⟩).symm
  have hw2 : ∀ {Z : C} (g₁ g₂ : Z ⟶ G ⊗ G), g₁ ≫ (q ⊗ₘ q) = g₂ ≫ (q ⊗ₘ q) →
      g₁ ≫ μ[G] ≫ q = g₂ ≫ μ[G] ≫ q := by
    intro Z g₁ g₂ hg
    have h1 : (g₁ ≫ fst G G) ≫ q = (g₂ ≫ fst G G) ≫ q := by
      simpa using hg =≫ fst B B
    have h2 : (g₁ ≫ snd G G) ≫ q = (g₂ ≫ snd G G) ≫ q := by
      simpa using hg =≫ snd B B
    obtain ⟨t, ht⟩ := (h _ _ _).1 h1
    obtain ⟨s, hs⟩ := (h _ _ _).1 h2
    have e : ∀ g : Z ⟶ G ⊗ G, g ≫ μ[G] = (g ≫ fst G G) * (g ≫ snd G G) := by
      intro g
      rw [MonObj.mul_eq_mul, MonObj.comp_mul]
    rw [← Category.assoc, ← Category.assoc, e g₁, e g₂, ht, hs, _root_.mul_mul_mul_comm,
      ← MonObj.mul_comp, same]
  have hw1 : ∀ {Z : C} (g₁ g₂ : Z ⟶ G), g₁ ≫ q = g₂ ≫ q →
      g₁ ≫ ι[G] ≫ q = g₂ ≫ ι[G] ≫ q := by
    intro Z g₁ g₂ hg
    obtain ⟨t, ht⟩ := (h _ _ _).1 hg
    rw [← Category.assoc, ← Category.assoc, ← Hom.inv_def, ← Hom.inv_def, ht, _root_.mul_inv,
      ← GrpObj.inv_comp, same]
  let mB : B ⊗ B ⟶ B := EffectiveEpi.desc (q ⊗ₘ q) (μ[G] ≫ q) hw2
  have hmB : (q ⊗ₘ q) ≫ mB = μ[G] ≫ q := EffectiveEpi.fac _ _ _
  let iB : B ⟶ B := EffectiveEpi.desc q (ι[G] ≫ q) hw1
  have hiB : q ≫ iB = ι[G] ≫ q := EffectiveEpi.fac _ _ _
  let eB : 𝟙_ C ⟶ B := η[G] ≫ q
  have key : ∀ {Z : C} (a b : Z ⟶ G), lift (a ≫ q) (b ≫ q) ≫ mB = (a * b) ≫ q := by
    intro Z a b
    rw [← CartesianMonoidalCategory.lift_map, Category.assoc, hmB, ← Category.assoc]
    rfl
  have keyL : ∀ {Z : C} (f : Z ⟶ 𝟙_ C) (b : Z ⟶ G), lift (f ≫ eB) (b ≫ q) ≫ mB = b ≫ q := by
    intro Z f b
    have e : f ≫ eB = (f ≫ η[G]) ≫ q := (Category.assoc _ _ _).symm
    rw [e, key, toUnit_unique f (toUnit Z), ← Hom.one_def, _root_.one_mul]
  have keyR : ∀ {Z : C} (a : Z ⟶ G) (f : Z ⟶ 𝟙_ C), lift (a ≫ q) (f ≫ eB) ≫ mB = a ≫ q := by
    intro Z a f
    have e : f ≫ eB = (f ≫ η[G]) ≫ q := (Category.assoc _ _ _).symm
    rw [e, key, toUnit_unique f (toUnit Z), ← Hom.one_def, _root_.mul_one]
  have epiL : Epi (𝟙_ C ◁ q) := by
    have e : 𝟙_ C ◁ q = (λ_ G).hom ≫ q ≫ (λ_ B).inv := by
      rw [← Category.assoc, ← MonoidalCategory.leftUnitor_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    rw [e]
    infer_instance
  have epiR : Epi (q ▷ 𝟙_ C) := by
    have e : q ▷ 𝟙_ C = (ρ_ G).hom ≫ q ≫ (ρ_ B).inv := by
      rw [← Category.assoc, ← MonoidalCategory.rightUnitor_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    rw [e]
    infer_instance
  have invL : lift (ι[G] ≫ q) q ≫ mB = (ι[G] * 𝟙 G) ≫ q := by
    have e := key ι[G] (𝟙 G)
    rwa [Category.id_comp] at e
  have invR : lift q (ι[G] ≫ q) ≫ mB = (𝟙 G * ι[G]) ≫ q := by
    have e := key (𝟙 G) ι[G]
    rwa [Category.id_comp] at e
  let inst : GrpObj B :=
    { one := eB
      mul := mB
      inv := iB
      one_mul := by
        apply (cancel_epi (𝟙_ C ◁ q)).1
        have e : 𝟙_ C ◁ q = lift (fst _ _) (snd _ _ ≫ q) := by
          ext
          simp [CartesianMonoidalCategory.leftUnitor_hom]
        rw [e, lift_whiskerRight_assoc, keyL, lift_leftUnitor_hom]
      mul_one := by
        apply (cancel_epi (q ▷ 𝟙_ C)).1
        have e : q ▷ 𝟙_ C = lift (fst _ _ ≫ q) (snd _ _) := by
          ext
          simp [CartesianMonoidalCategory.rightUnitor_hom]
        rw [e, lift_whiskerLeft_assoc, keyR, lift_rightUnitor_hom]
      mul_assoc := by
        apply (cancel_epi ((q ⊗ₘ q) ⊗ₘ q)).1
        have e : (q ⊗ₘ q) ⊗ₘ q = lift (lift ((fst _ _ ≫ fst _ _) ≫ q) ((fst _ _ ≫ snd _ _) ≫ q))
            (snd _ _ ≫ q) := by ext <;> simp
        rw [e]
        simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc,
          lift_whiskerLeft_assoc, key]
        rw [_root_.mul_assoc]
      left_inv := by
        apply (cancel_epi q).1
        rw [← Category.assoc, comp_lift, hiB, Category.comp_id, invL, ← Category.assoc q,
          toUnit_unique (q ≫ toUnit B) (toUnit G), GrpObj.inv_eq_inv, inv_mul_cancel,
          Hom.one_def, Category.assoc]
      right_inv := by
        apply (cancel_epi q).1
        rw [← Category.assoc, comp_lift, hiB, Category.comp_id, invR, ← Category.assoc q,
          toUnit_unique (q ≫ toUnit B) (toUnit G), GrpObj.inv_eq_inv, mul_inv_cancel,
          Hom.one_def, Category.assoc] }
  refine ⟨inst, ⟨?_⟩, ⟨rfl, hmB.symm⟩, ?_⟩
  · show (β_ B B).hom ≫ mB = mB
    apply (cancel_epi (q ⊗ₘ q)).1
    have e : q ⊗ₘ q = lift (fst G G ≫ q) (snd G G ≫ q) := by ext <;> simp
    rw [e, ← Category.assoc, lift_braiding_hom, key, key, _root_.mul_comm]
  · have hsq : i ≫ q = toUnit T ≫ eB := by
      have e := same (𝟙 T) 1
      rw [Category.id_comp, _root_.mul_one] at e
      rw [e, Hom.one_def, Category.assoc]
    have ex : ∀ s : PullbackCone q eB, ∃ t : s.pt ⟶ T, s.fst = t ≫ i := by
      intro s
      have hs : (1 : s.pt ⟶ G) ≫ q = s.fst ≫ q := by
        rw [s.condition, Hom.one_def, toUnit_unique s.snd (toUnit s.pt), Category.assoc]
      obtain ⟨t, ht⟩ := (h _ _ _).1 hs
      exact ⟨t, by rw [ht, _root_.mul_one]⟩
    exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk hsq (fun s => Classical.choose (ex s))
      (fun s => (Classical.choose_spec (ex s)).symm) (fun s => toUnit_unique _ _)
      (fun s m hm _ => by
        rw [← cancel_mono i, hm]
        exact Classical.choose_spec (ex s)))
end GlobalTheory.CosetQuotient
