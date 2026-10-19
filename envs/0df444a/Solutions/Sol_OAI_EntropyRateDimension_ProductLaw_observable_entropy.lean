-- Prove2me | solution 1 for OAI.EntropyRateDimension.ProductLaw.observable_entropy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:35:07.248992+00:00
-- url     : https://prove2.me/submissions/6c52d723-7e4c-4c60-97d2-7a2fcbe904ee

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.ProductLaw
universe uι uα uβ uγ
open scoped BigOperators ENNReal
open MeasureTheory
variable {ι : Type uι} {α : Type uα} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {β : Type uβ} [DecidableEq β]
theorem h44_nml_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → ℝ) :
    Real.negMulLog (∏ i, y i) = ∑ i, ∏ j, (if j = i then Real.negMulLog (y j) else y j) := by
  by_cases hz : ∃ k, y k = 0
  · obtain ⟨k, hk⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ k) hk, Real.negMulLog_zero]
    symm
    refine Finset.sum_eq_zero fun i _ => Finset.prod_eq_zero (Finset.mem_univ k) ?_
    split_ifs <;> simp [hk]
  · push Not at hz
    have e : ∀ i, ∏ j, (if j = i then Real.negMulLog (y j) else y j) =
        -(∏ j, y j) * Real.log (y i) := by
      intro i
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), if_pos rfl,
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      rw [Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))]
      simp only [Real.negMulLog]; ring
    rw [Finset.sum_congr rfl (fun i _ => e i), ← Finset.mul_sum,
      ← Real.log_prod (s := Finset.univ) (f := y) (fun i _ => hz i), Real.negMulLog]

theorem h44_ent_pi {ι κ : Type*} [Fintype ι] [DecidableEq ι] (T : Finset κ) (q : ι → κ → ℝ) :
    ∑ x ∈ Fintype.piFinset (fun _ : ι => T), Real.negMulLog (∏ i, q i (x i)) =
      ∑ i, (∏ j ∈ Finset.univ.erase i, ∑ b ∈ T, q j b) * ∑ b ∈ T, Real.negMulLog (q i b) := by
  simp only [h44_nml_prod]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_prod_piFinset T (fun j b => if j = i then Real.negMulLog (q j b) else q j b),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [if_pos rfl]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  simp only [if_neg (Finset.ne_of_mem_erase hj)]

theorem solution [Nonempty α] [Nonempty β]
    (p : α → ℝ) (g : α → β) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    FiniteEntropy.observableEntropy Finset.univ (weight (fun _ : ι => p)) (fun x i => g (x i)) =
      Fintype.card ι * FiniteEntropy.observableEntropy Finset.univ p g := by
  classical
  unfold FiniteEntropy.observableEntropy FiniteEntropy.entropy
  have hm : ∀ c : ι → β, FiniteEntropy.mass Finset.univ (weight (fun _ : ι => p))
      (fun x i => g (x i)) c = ∏ i, FiniteEntropy.mass Finset.univ p g (c i) := by
    intro c
    unfold FiniteEntropy.mass weight
    rw [Finset.sum_filter]
    have e : ∀ x : ι → α, (if (fun i => g (x i)) = c then ∏ i, p (x i) else 0) =
        ∏ i, (if g (x i) = c i then p (x i) else 0) := by
      intro x
      by_cases h : (fun i => g (x i)) = c
      · rw [if_pos h]
        exact Finset.prod_congr rfl fun i _ => (if_pos (congrFun h i)).symm
      · rw [if_neg h]
        have : ∃ i, g (x i) ≠ c i := by
          by_contra hc; push Not at hc; exact h (funext hc)
        obtain ⟨i, hi⟩ := this
        exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm
    simp only [e]
    have h := Finset.sum_prod_piFinset (Finset.univ : Finset α)
      (fun i a => if g a = c i then p a else 0)
    rw [Fintype.piFinset_univ] at h
    rw [h]
    exact Finset.prod_congr rfl fun i _ => (Finset.sum_filter _ _).symm
  simp only [hm]
  rw [Finset.sum_subset (s₂ := Fintype.piFinset fun _ : ι => Finset.univ.image g)]
  · rw [h44_ent_pi (Finset.univ.image g) (fun _ => FiniteEntropy.mass Finset.univ p g)]
    simp only [FiniteEntropy.mass_sum, hp1, Finset.prod_const_one, one_mul,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · intro c hc
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hc
    exact Fintype.mem_piFinset.mpr fun i => Finset.mem_image_of_mem g (Finset.mem_univ _)
  · intro c _ hc
    rw [← hm, FiniteEntropy.mass_eq_zero_of_not_mem _ _ _ hc, Real.negMulLog_zero]

