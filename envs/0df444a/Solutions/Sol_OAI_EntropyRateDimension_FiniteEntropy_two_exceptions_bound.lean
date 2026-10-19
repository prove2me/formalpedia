-- Prove2me | solution 1 for OAI.EntropyRateDimension.FiniteEntropy.two_exceptions_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:26:32.488237+00:00
-- url     : https://prove2.me/submissions/93fadf31-86d8-497e-8dcb-71ada4d5a713

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory
theorem h43_union {α : Type*} {κ : Type*} [Fintype κ]
    (s : Finset α) (p : α → ℝ) (E : κ → α → Prop)
    [∀ i, DecidablePred (E i)] (hp : ∀ a ∈ s, 0 ≤ p a) :
    (∑ a ∈ s, if ∃ i, E i a then p a else 0) ≤
      ∑ i, ∑ a ∈ s, if E i a then p a else 0 := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun a ha => ?_
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    have := Finset.single_le_sum (f := fun j => if E j a then p a else 0)
      (fun j _ => by split_ifs <;> simp [hp a ha]) (Finset.mem_univ i)
    simpa [hi] using this
  · exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp [hp a ha]

theorem solution {α : Type uα} {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (s : Finset α) (p : α → ℝ) (E : ι → α → Prop)
    [∀ i, DecidablePred (E i)] (hp : ∀ a ∈ s, 0 ≤ p a)
    (hind : ∀ i j, i ≠ j →
      (∑ a ∈ s, if E i a ∧ E j a then p a else 0) =
        (∑ a ∈ s, if E i a then p a else 0) *
        (∑ a ∈ s, if E j a then p a else 0)) :
    let t := ∑ i, ∑ a ∈ s, if E i a then p a else 0
    let q := ∑ a ∈ s, if ∃ i j, i ≠ j ∧ E i a ∧ E j a then p a else 0
    q ≤ t ^ 2 ∧ q ≤ t := by
  classical
  intro t q
  have hP : ∀ i, 0 ≤ ∑ a ∈ s, if E i a then p a else 0 :=
    fun i => Finset.sum_nonneg fun a ha => by split_ifs <;> simp [hp a ha]
  constructor
  · have h1 := h43_union s p (fun (ij : ι × ι) a => ij.1 ≠ ij.2 ∧ E ij.1 a ∧ E ij.2 a) hp
    have e : (∑ a ∈ s, if ∃ ij : ι × ι, ij.1 ≠ ij.2 ∧ E ij.1 a ∧ E ij.2 a then p a else 0) = q := by
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Prod.exists]
    rw [e] at h1
    refine h1.trans ?_
    rw [sq, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    by_cases hij : i = j
    · subst hij; simp only [ne_eq, not_true_eq_false, false_and, if_false, Finset.sum_const_zero]
      exact mul_nonneg (hP i) (hP i)
    · rw [← hind i j hij]
      exact le_of_eq (Finset.sum_congr rfl fun a _ => by simp [hij])
  · have h1 := h43_union s p E hp
    refine le_trans ?_ h1
    refine Finset.sum_le_sum fun a ha => ?_
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd ⟨_, h1.choose_spec.choose_spec.2.1⟩ h2
    · exact hp a ha
    · exact le_rfl

