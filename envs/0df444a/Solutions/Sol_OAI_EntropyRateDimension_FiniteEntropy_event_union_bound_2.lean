-- Prove2me | solution 2 for OAI.EntropyRateDimension.FiniteEntropy.event_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:35:27.729554+00:00
-- url     : https://prove2.me/submissions/aa68b742-a0ba-4c6b-b1e0-82916c3d7724

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean:L546-L563
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FiniteEntropy.event_union_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

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

theorem event_union_bound {α : Type uα} {ι : Type uι} [Fintype ι]
    (s : Finset α) (p : α → ℝ) (E : ι → α → Prop)
    [∀ i, DecidablePred (E i)] (hp : ∀ a ∈ s, 0 ≤ p a) :
    (∑ a ∈ s, if ∃ i, E i a then p a else 0) ≤
      ∑ i, ∑ a ∈ s, if E i a then p a else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  by_cases he : ∃ i, E i a
  · rw [ite_eq_left he]
    obtain ⟨i, hi⟩ := he
    apply le_trans _ (Finset.single_le_sum (fun j _ => by
      split_ifs <;> first | exact hp a ha | exact le_rfl) (Finset.mem_univ i))
    simp only [ite_eq_left hi, le_refl]
  · rw [ite_eq_right he]
    exact Finset.sum_nonneg (fun j _ => by
      split_ifs <;> first | exact hp a ha | exact le_rfl)

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uι,uα} : type_of% @_root_.OAI.EntropyRateDimension.FiniteEntropy.event_union_bound.{uι,uα} := @_root_.OAI.EntropyRateDimension.FiniteEntropy.event_union_bound.{uι,uα}
