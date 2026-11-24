-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonOfMeasurableSequences
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T10:09:17.871916+00:00
-- url     : https://prove2.me/submissions/ac3c8c8a-8f24-4109-a6c1-96c1fbbc07ad

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 2000000

private theorem nat_sInf_eq_iff (s : Set ℕ) (k : ℕ) :
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

private theorem measurable_arrival
    {Ω : Type*} [MeasurableSpace Ω]
    {τ : ℕ → Ω → ℝ} (hτ : ∀ n, Measurable (τ n)) (n : ℕ) :
    Measurable (fun ω => arrival τ n ω) :=
  Finset.measurable_sum _ fun i _ => hτ i

/-- Joint measurability of the jump count in `(ω, t)`. -/
private theorem measurable_jumpCount_joint
    {Ω : Type*} [MeasurableSpace Ω]
    {τ : ℕ → Ω → ℝ} (hτ : ∀ n, Measurable (τ n)) :
    Measurable
      (fun p : Ω × ℝ≥0 =>
        jumpCount (fun n => arrival τ n p.1) (p.2 : ℝ)) := by
  have harr : ∀ n, Measurable (fun ω => arrival τ n ω) := fun n =>
    measurable_arrival hτ n
  have hA : ∀ n, MeasurableSet
      {p : Ω × ℝ≥0 | (p.2 : ℝ) < arrival τ n p.1} := by
    intro n
    exact measurableSet_lt
      (NNReal.continuous_coe.measurable.comp measurable_snd)
      ((harr n).comp measurable_fst)
  refine measurable_to_countable' fun k => ?_
  have hset :
      (fun p : Ω × ℝ≥0 =>
          jumpCount (fun n => arrival τ n p.1) (p.2 : ℝ)) ⁻¹' {k}
        =
      ({p : Ω × ℝ≥0 | (p.2 : ℝ) < arrival τ k p.1} ∩
          ⋂ j, ⋂ _ : j < k, {p : Ω × ℝ≥0 | ¬ (p.2 : ℝ) < arrival τ j p.1})
        ∪
      ((⋂ n, {p : Ω × ℝ≥0 | ¬ (p.2 : ℝ) < arrival τ n p.1}) ∩
          {_p : Ω × ℝ≥0 | k = 0}) := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, jumpCount]
    rw [nat_sInf_eq_iff]
    simp only [mem_union, mem_inter_iff, mem_iInter, mem_setOf_eq,
      eq_empty_iff_forall_notMem]
  rw [hset]
  refine ((hA k).inter (MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => (hA j).compl)).union
      ((MeasurableSet.iInter fun n => (hA n).compl).inter ?_)
  exact MeasurableSet.const _

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (τ Y : ℕ → Ω → ℝ)
    (hτ : ∀ n, Measurable (τ n))
    (hY : ∀ n, Measurable (Y n)) :
    Measurable
      (fun p : Ω × ℝ≥0 =>
        ProbabilityTheory.compoundPoisson 0 τ Y (p.2 : ℝ) p.1) := by
  -- Coordinate families are jointly measurable into `ℕ → ℝ`.
  have hτπ : Measurable (fun ω : Ω => fun n : ℕ => τ n ω) :=
    measurable_pi_lambda _ fun n => hτ n
  have hYπ : Measurable (fun ω : Ω => fun n : ℕ => Y n ω) :=
    measurable_pi_lambda _ fun n => hY n
  -- Finite-sum kernel over a countable jump index.
  have hF : Measurable (fun q : Ω × ℕ =>
      ∑ n ∈ Finset.range q.2, Y n q.1) :=
    measurable_from_prod_countable_left fun k =>
      Finset.measurable_sum (Finset.range k) fun n _ => hY n
  have hCount := measurable_jumpCount_joint hτ
  have hSum :
      Measurable
        (fun p : Ω × ℝ≥0 =>
          ∑ n ∈ Finset.range
              (jumpCount (fun n => arrival τ n p.1) (p.2 : ℝ)),
            Y n p.1) :=
    hF.comp (measurable_fst.prodMk hCount)
  -- `compoundPoisson 0` is the zero-drift piecewise path = mark sum.
  change Measurable
    (fun p : Ω × ℝ≥0 =>
      (0 : ℝ) + (0 : ℝ) * (p.2 : ℝ) +
        ∑ n ∈ Finset.range
            (jumpCount (fun n => arrival τ n p.1) (p.2 : ℝ)),
          Y n p.1)
  simpa using hSum
