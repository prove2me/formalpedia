-- Prove2me | solution 2 for OAI.EntropyRateDimension.FiniteEntropy.two_exceptions_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:36:59.692505+00:00
-- url     : https://prove2.me/submissions/2aebf81e-ef4f-4250-8927-13a1c87e732c

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean:L565-L610
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FiniteEntropy.two_exceptions_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_event_union_bound

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteEntropy

theorem two_exceptions_bound {α : Type uα} {ι : Type uι} [Fintype ι] [DecidableEq ι]
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
  dsimp only
  have hPi : ∀ i, 0 ≤ ∑ a ∈ s, if E i a then p a else 0 := by
    intro i
    apply Finset.sum_nonneg
    intro a ha
    split_ifs <;> first | exact hp a ha | exact le_rfl
  constructor
  · have hU := event_union_bound s p
      (fun ij : ι × ι => fun a => ij.1 ≠ ij.2 ∧ E ij.1 a ∧ E ij.2 a) hp
    have he : (∑ a ∈ s, if ∃ i j, i ≠ j ∧ E i a ∧ E j a then p a else 0) =
        ∑ a ∈ s, if ∃ ij : ι × ι, ij.1 ≠ ij.2 ∧ E ij.1 a ∧ E ij.2 a then p a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      exact propext ⟨fun ⟨i,j,h⟩ => ⟨(i,j),h⟩, fun ⟨⟨i,j⟩,h⟩ => ⟨i,j,h⟩⟩
    rw [he]
    apply le_trans hU
    rw [Fintype.sum_prod_type, sq, Finset.sum_mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · subst j
      simp only [ne_eq, not_true_eq_false, false_and, ite_false, Finset.sum_const_zero]
      exact mul_nonneg (hPi i) (hPi i)
    · simpa only [ne_eq, hij, not_false_eq_true, true_and] using (hind i j hij).le
  · apply le_trans _ (event_union_bound s p E hp)
    apply Finset.sum_le_sum
    intro a ha
    by_cases h : ∃ i j, i ≠ j ∧ E i a ∧ E j a
    · obtain ⟨i,j,hij,hi,hj⟩ := h
      rw [ite_eq_left ⟨i,j,hij,hi,hj⟩, ite_eq_left (show ∃ i, E i a from ⟨i,hi⟩)]
    · rw [ite_eq_right h]
      split_ifs <;> first | exact hp a ha | exact le_rfl

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uι,uα} : type_of% @_root_.OAI.EntropyRateDimension.FiniteEntropy.two_exceptions_bound.{uι,uα} := @_root_.OAI.EntropyRateDimension.FiniteEntropy.two_exceptions_bound.{uι,uα}
