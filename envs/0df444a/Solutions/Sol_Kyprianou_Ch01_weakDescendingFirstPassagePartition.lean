-- Prove2me | solution 1 for Kyprianou.Ch01.weakDescendingFirstPassagePartition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:12:44.647726+00:00
-- url     : https://prove2.me/submissions/976bf7cf-ed11-43aa-93ed-624a587e87d9

import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.Prod

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, Measurable (increment n))
    (B : Set ℝ) (hB : MeasurableSet B)
    (hsubset : B ⊆ Set.Iic (0 : ℝ)) :
    let S : ℕ → Ω → ℝ :=
      fun n ω => ∑ i ∈ Finset.range n, increment i ω
    P {ω | ∃ n : ℕ, 1 ≤ n ∧ S n ω ∈ B ∧
          ∀ j : ℕ, 1 ≤ j → j < n → 0 < S j ω} =
      ∑' n : ℕ, P {ω | S (n + 1) ω ∈ B ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < S j ω} := by
  intro S
  let A : ℕ → Set Ω := fun n =>
    {ω | S (n + 1) ω ∈ B ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < S j ω}
  have hS (n : ℕ) : Measurable (S n) := by
    change Measurable (fun ω => ∑ i ∈ Finset.range n, increment i ω)
    fun_prop
  have hprefix (n : ℕ) :
      MeasurableSet {ω | ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < S j ω} := by
    have hj (j : ℕ) :
        MeasurableSet {ω | 1 ≤ j → j ≤ n → 0 < S j ω} := by
      by_cases h1 : 1 ≤ j
      · by_cases h2 : j ≤ n
        · have heq :
              {ω | 1 ≤ j → j ≤ n → 0 < S j ω} =
              (S j) ⁻¹' Set.Ioi (0 : ℝ) := by
              ext ω
              simp [h1, h2]
          rw [heq]
          exact measurableSet_Ioi.preimage (hS j)
        · simp [h2]
      · simp [h1]
    simpa only [Set.setOf_forall] using MeasurableSet.iInter hj
  have hmA (n : ℕ) : MeasurableSet (A n) := by
    change MeasurableSet ({ω | S (n + 1) ω ∈ B} ∩
      {ω | ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < S j ω})
    exact (hB.preimage (hS (n + 1))).inter (hprefix n)
  have hpartition :
      {ω | ∃ n : ℕ, 1 ≤ n ∧ S n ω ∈ B ∧
        ∀ j : ℕ, 1 ≤ j → j < n → 0 < S j ω} =
      ⋃ n : ℕ, A n := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨n, hn, hBω, hprev⟩
      cases n with
      | zero => simp at hn
      | succ k =>
          refine ⟨k, ?_⟩
          change S (k + 1) ω ∈ B ∧
            ∀ j : ℕ, 1 ≤ j → j ≤ k → 0 < S j ω
          refine ⟨hBω, ?_⟩
          intro j hj1 hjle
          exact hprev j hj1 (Nat.lt_succ_iff.mpr hjle)
    · rintro ⟨n, hω⟩
      change S (n + 1) ω ∈ B ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < S j ω) at hω
      refine ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), hω.1, ?_⟩
      intro j hj1 hjlt
      exact hω.2 j hj1 (Nat.lt_succ_iff.mp hjlt)
  have hd (m n : ℕ) (hmn : m < n) : Disjoint (A m) (A n) := by
    apply Set.disjoint_left.mpr
    intro ω hm hn
    have hnonpos : S (m + 1) ω ≤ 0 := hsubset hm.1
    have hpositive : 0 < S (m + 1) ω :=
      hn.2 (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hmn
    linarith
  have hpair : Pairwise (fun m n : ℕ => Disjoint (A m) (A n)) := by
    intro m n hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hd m n hlt
    · exact (hd n m hgt).symm
  change P {ω | ∃ n : ℕ, 1 ≤ n ∧ S n ω ∈ B ∧
    ∀ j : ℕ, 1 ≤ j → j < n → 0 < S j ω} =
      ∑' n : ℕ, P (A n)
  rw [hpartition]
  exact measure_iUnion hpair hmA
