-- Prove2me | solution 1 for OAI.EntropyRateDimension.FiniteEntropy.event_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:21:14.758766+00:00
-- url     : https://prove2.me/submissions/ebf2a9ab-56bf-457a-8682-6927ccdfb587

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution {α : Type uα} {ι : Type uι} [Fintype ι]
    (s : Finset α) (p : α → ℝ) (E : ι → α → Prop)
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

