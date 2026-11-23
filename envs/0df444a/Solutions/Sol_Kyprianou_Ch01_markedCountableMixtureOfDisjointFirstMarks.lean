-- Prove2me | solution 1 for Kyprianou.Ch01.markedCountableMixtureOfDisjointFirstMarks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:58:13.038498+00:00
-- url     : https://prove2.me/submissions/92a86a7f-7a60-4b6e-8985-136c9a05cb5b

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (arrival marks : ℕ → Ω → ℝ)
    (h0 : Measurable (arrival 0))
    (h1 : Measurable (arrival 1))
    (hm : Measurable (marks 0))
    (u : ℝ) (v : ℕ → ℝ) (p : PMF ℕ) (q : ℕ → ℝ)
    (hAtom : ∀ k : ℕ,
      (Q {ω | arrival 0 ω ≤ u ∧ arrival 1 ω ≤ v k ∧
        marks 0 ω = (k : ℝ) - 1}).toReal =
      (Q {ω | arrival 0 ω ≤ u}).toReal *
        (p k).toReal * q k) :
    (Q {ω | ∃ k : ℕ,
        marks 0 ω = (k : ℝ) - 1 ∧
        arrival 0 ω ≤ u ∧ arrival 1 ω ≤ v k}).toReal =
      (Q {ω | arrival 0 ω ≤ u}).toReal *
        (∑' k : ℕ, (p k).toReal * q k) := by
  let E (k : ℕ) : Set Ω :=
    {ω | arrival 0 ω ≤ u ∧ arrival 1 ω ≤ v k ∧
      marks 0 ω = (k : ℝ) - 1}
  have hSet :
      {ω | ∃ k : ℕ,
        marks 0 ω = (k : ℝ) - 1 ∧
        arrival 0 ω ≤ u ∧ arrival 1 ω ≤ v k} =
        ⋃ k, E k := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨k, hmark, hfirst, hsecond⟩
      exact ⟨k, hfirst, hsecond, hmark⟩
    · rintro ⟨k, hfirst, hsecond, hmark⟩
      exact ⟨k, hmark, hfirst, hsecond⟩
  have hMeas (k : ℕ) : MeasurableSet (E k) := by
    dsimp [E]
    measurability
  have hDisj : Pairwise (fun k l => Disjoint (E k) (E l)) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro ω hk hl
    change arrival 0 ω ≤ u ∧ arrival 1 ω ≤ v k ∧
      marks 0 ω = (k : ℝ) - 1 at hk
    change arrival 0 ω ≤ u ∧ arrival 1 ω ≤ v l ∧
      marks 0 ω = (l : ℝ) - 1 at hl
    have hEq : (k : ℝ) = (l : ℝ) := by
      linarith [hk.2.2, hl.2.2]
    exact hkl (by exact_mod_cast hEq)
  have hUnion :
      (Q (⋃ k, E k)).toReal =
        ∑' k : ℕ, (Q (E k)).toReal := by
    rw [measure_iUnion hDisj hMeas]
    exact ENNReal.tsum_toReal_eq (fun k => measure_ne_top Q (E k))
  rw [hSet, hUnion]
  have hAtoms :
      (∑' k : ℕ, (Q (E k)).toReal) =
        ∑' k : ℕ, (Q {ω | arrival 0 ω ≤ u}).toReal *
          ((p k).toReal * q k) := by
    apply tsum_congr
    intro k
    have he := hAtom k
    change (Q (E k)).toReal =
      (Q {ω | arrival 0 ω ≤ u}).toReal *
        (p k).toReal * q k at he
    rw [he]
    ring
  rw [hAtoms, tsum_mul_left]

