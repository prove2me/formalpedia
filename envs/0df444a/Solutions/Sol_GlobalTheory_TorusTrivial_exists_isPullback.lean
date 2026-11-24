-- Prove2me | solution 1 for GlobalTheory.TorusTrivial.exists_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:37:16.562539+00:00
-- url     : https://prove2.me/submissions/fb7334f7-940e-494f-8a47-eead75bfe6db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusTrivial
namespace GlobalTheory.TorusTrivial
theorem _root_.solution {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {T G B W V : C} [GrpObj T] [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : T ⟶ G)
    [IsMonHom q] [IsMonHom i] (hk : IsPullback i (toUnit _) q η[B])
    {j : W ⟶ G} {k : V ⟶ B} {q' : W ⟶ V} (hW : IsPullback j q' q k) [Mono j] (τ : W ⟶ T)
    (hτ : ∀ (Z : C) (t : Z ⟶ T) (g g' : Z ⟶ W), g' ≫ j = (t ≫ i) * (g ≫ j) →
      g' ≫ τ = t * (g ≫ τ)) :
    ∃ a : T ⊗ W ⟶ W, IsPullback (𝟙 _) a (T ◁ q') (lift τ q') := by
  have hiq : ∀ {Z : C} (t : Z ⟶ T), (t ≫ i) ≫ q = 1 := by
    intro Z t
    rw [Category.assoc, hk.w, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  let s : T ⊗ W ⟶ T := fst T W * (snd T W ≫ τ)⁻¹
  have hw : ((s ≫ i) * (snd T W ≫ j)) ≫ q = (snd T W ≫ q') ≫ k := by
    rw [MonObj.mul_comp, hiq, _root_.one_mul, Category.assoc, Category.assoc, hW.w]
  let a : T ⊗ W ⟶ W := hW.lift _ _ hw
  have ha₁ : a ≫ j = (s ≫ i) * (snd T W ≫ j) := hW.lift_fst _ _ _
  have ha₂ : a ≫ q' = snd T W ≫ q' := hW.lift_snd _ _ _
  have ha₃ : a ≫ τ = fst T W := by
    rw [hτ _ _ _ _ ha₁]
    simp [s]
  have hsq : 𝟙 _ ≫ T ◁ q' = a ≫ lift τ q' := by
    ext <;> simp [ha₂, ha₃]
  refine ⟨a, ⟨hsq⟩, ⟨PullbackCone.IsLimit.mk hsq (fun c => c.fst) (fun c => by simp)
    (fun c => ?_) (fun c m h _ => by simpa using h)⟩⟩
  have h₁ : c.fst ≫ fst T W = c.snd ≫ τ := by
    simpa using c.condition =≫ fst _ _
  have h₂ : c.fst ≫ snd T W ≫ q' = c.snd ≫ q' := by
    simpa using c.condition =≫ snd _ _
  have h₃ : ((c.snd ≫ j) * (c.fst ≫ snd T W ≫ j)⁻¹) ≫ q = toUnit _ ≫ η[B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, ← Hom.one_def]
    simp only [Category.assoc, hW.w]
    rw [reassoc_of% h₂, mul_inv_cancel]
  let r : c.pt ⟶ T := hk.lift _ _ h₃
  have hr : r ≫ i = (c.snd ≫ j) * (c.fst ≫ snd T W ≫ j)⁻¹ := hk.lift_fst _ _ _
  have h₄ : c.snd ≫ j = (r ≫ i) * ((c.fst ≫ snd T W) ≫ j) := by
    rw [hr]; simp
  have h₅ := hτ _ _ _ _ h₄
  have h₆ : c.fst ≫ s = r := by
    simp only [s, MonObj.comp_mul, GrpObj.comp_inv, h₁, h₅, Category.assoc, mul_inv_cancel_right]
  rw [← cancel_mono j, Category.assoc, ha₁, MonObj.comp_mul, reassoc_of% h₆, h₄, Category.assoc]
end GlobalTheory.TorusTrivial
