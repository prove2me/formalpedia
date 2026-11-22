-- Prove2me | solution 1 for Kyprianou.Ch01.integerCompoundPoissonFixedTimeMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T16:54:47.532618+00:00
-- url     : https://prove2.me/submissions/1230eb36-1eb2-4e0d-bd37-42fc9e80b2b5

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A local copy of the accepted natural-number infimum characterisation. -/
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

/-- Accepted measurable jump-count proof, reproduced without a private import. -/
private theorem lc_measurable_jumpCount
    {Ω : Type*} [MeasurableSpace Ω]
    {τ : ℕ → Ω → ℝ} (hτ : ∀ n, Measurable (τ n)) (t : ℝ) :
    Measurable (fun ω => jumpCount (fun n => arrival τ n ω) t) := by
  have harr : ∀ n, Measurable (fun ω => arrival τ n ω) := fun n =>
    Finset.measurable_sum _ fun i _ => hτ i
  have hA : ∀ n, MeasurableSet {ω : Ω | t < arrival τ n ω} := fun n =>
    measurableSet_lt measurable_const (harr n)
  refine measurable_to_countable' fun k => ?_
  have hset : (fun ω => jumpCount (fun n => arrival τ n ω) t) ⁻¹' {k}
      = ({ω : Ω | t < arrival τ k ω} ∩
          ⋂ j, ⋂ _ : j < k, {ω : Ω | ¬ t < arrival τ j ω})
        ∪ ((⋂ n, {ω : Ω | ¬ t < arrival τ n ω}) ∩
          {_ω : Ω | k = 0}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, jumpCount]
    rw [lc_nat_sInf_eq_iff]
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq, Set.eq_empty_iff_forall_notMem]
  rw [hset]
  refine ((hA k).inter (MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => (hA j).compl)).union
      ((MeasurableSet.iInter fun n => (hA n).compl).inter ?_)
  exact MeasurableSet.const _

/-- Direct integer-valued fixed-time process measurability. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (y : ℕ) (τ marks : ℕ → Ω → ℝ)
    (hArrival : ∀ n, Measurable (τ n))
    (hMarks : ∀ n, Measurable (marks n))
    (t : ℝ≥0) :
    Measurable (integerCompoundPoisson y τ marks t) := by
  have hF : Measurable (fun p : Ω × ℕ =>
      ∑ n ∈ Finset.range p.2, marks n p.1) :=
    measurable_from_prod_countable_left fun k =>
      Finset.measurable_sum (Finset.range k) fun n _ => hMarks n
  have hCount : Measurable (fun ω : Ω =>
      jumpCount (fun n => arrival τ n ω) (t : ℝ)) :=
    lc_measurable_jumpCount hArrival (t : ℝ)
  have hSum : Measurable (fun ω : Ω =>
      ∑ n ∈ Finset.range
        (jumpCount (fun n => arrival τ n ω) (t : ℝ)),
          marks n ω) :=
    hF.comp (measurable_id.prodMk hCount)
  have hCp : Measurable (ProbabilityTheory.compoundPoisson
      (0 : ℝ) τ marks (t : ℝ)) := by
    change Measurable (fun ω : Ω =>
      0 + (0 : ℝ) * (t : ℝ) +
        ∑ n ∈ Finset.range
          (jumpCount (fun n => arrival τ n ω) (t : ℝ)),
          marks n ω)
    simpa using hSum
  have hReal : Measurable (fun ω : Ω =>
      (y : ℝ) + ProbabilityTheory.compoundPoisson
        (0 : ℝ) τ marks (t : ℝ) ω) :=
    measurable_const.add hCp
  change Measurable (fun ω : Ω =>
    Int.floor ((y : ℝ) + ProbabilityTheory.compoundPoisson
      (0 : ℝ) τ marks (t : ℝ) ω))
  exact Int.measurable_floor.comp hReal
