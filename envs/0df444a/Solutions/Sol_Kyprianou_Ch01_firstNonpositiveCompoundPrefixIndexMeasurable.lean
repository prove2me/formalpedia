-- Prove2me | solution 1 for Kyprianou.Ch01.firstNonpositiveCompoundPrefixIndexMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:05:51.221239+00:00
-- url     : https://prove2.me/submissions/e79816b0-02e2-4b11-a453-af2ef5e0eaaf

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Characterise a least index, including an empty index set. -/
private theorem lc_nat_sInf_eq_iff (s : Set ℕ) (k : ℕ) :
    sInf s = k ↔ (k ∈ s ∧ ∀ j < k, j ∉ s) ∨ (s = ∅ ∧ k = 0) := by
  constructor
  · intro h
    rcases s.eq_empty_or_nonempty with hs | hs
    · exact Or.inr ⟨hs, by rw [hs, Nat.sInf_empty] at h; exact h.symm⟩
    · exact Or.inl ⟨h ▸ Nat.sInf_mem hs,
        fun j hj => Nat.notMem_of_lt_sInf (h ▸ hj)⟩
  · rintro (⟨hk, hlt⟩ | ⟨hs, hk⟩)
    · refine le_antisymm (Nat.sInf_le hk) ?_
      by_contra hlt'
      push Not at hlt'
      exact hlt _ hlt' (Nat.sInf_mem ⟨k, hk⟩)
    · rw [hs, hk]
      exact Nat.sInf_empty

/-- Countable first-hit selection for the compound-Poisson mark-prefix lattice. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (y : ℕ) (marks : ℕ → Ω → ℝ)
    (hMarks : ∀ n, Measurable (marks n)) :
    Measurable (fun ω : Ω =>
      sInf {n : ℕ |
        Int.floor ((y : ℝ) + ∑ i ∈ Finset.range n, marks i ω) ≤ 0}) := by
  have hZ : ∀ n : ℕ, Measurable (fun ω : Ω =>
      Int.floor ((y : ℝ) + ∑ i ∈ Finset.range n, marks i ω)) := by
    intro n
    apply Int.measurable_floor.comp
    exact measurable_const.add
      (Finset.measurable_sum _ fun i _ => hMarks i)
  have hA : ∀ n : ℕ, MeasurableSet {ω : Ω |
      Int.floor ((y : ℝ) + ∑ i ∈ Finset.range n, marks i ω) ≤ 0} := fun n =>
    measurableSet_le (hZ n) measurable_const
  refine measurable_to_countable' fun k => ?_
  have hset : (fun ω : Ω =>
        sInf {n : ℕ |
          Int.floor ((y : ℝ) + ∑ i ∈ Finset.range n, marks i ω) ≤ 0}) ⁻¹' {k}
      = ({ω : Ω |
          Int.floor ((y : ℝ) + ∑ i ∈ Finset.range k, marks i ω) ≤ 0}
          ∩ ⋂ j, ⋂ _ : j < k, {ω : Ω |
            ¬ Int.floor ((y : ℝ) +
              ∑ i ∈ Finset.range j, marks i ω) ≤ 0})
        ∪ ((⋂ n, {ω : Ω |
            ¬ Int.floor ((y : ℝ) +
              ∑ i ∈ Finset.range n, marks i ω) ≤ 0})
          ∩ {_ω : Ω | k = 0}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [lc_nat_sInf_eq_iff]
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq, Set.eq_empty_iff_forall_notMem]
  rw [hset]
  refine ((hA k).inter (MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => (hA j).compl)).union
      ((MeasurableSet.iInter fun n => (hA n).compl).inter ?_)
  exact MeasurableSet.const _
