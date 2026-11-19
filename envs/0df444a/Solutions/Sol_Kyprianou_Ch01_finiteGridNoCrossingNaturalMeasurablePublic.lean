-- Prove2me | solution 1 for Kyprianou.Ch01.finiteGridNoCrossingNaturalMeasurablePublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T10:05:53.683409+00:00
-- url     : https://prove2.me/submissions/12d3010a-114a-45c0-8f5b-4c7c942203fa

import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.NNReal.Defs
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_measurable_past
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Kyprianou.Ch01 Set
open scoped NNReal
set_option autoImplicit false

/-- The finite prefix non-crossing event is measurable at the final grid time. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (delta : ℝ≥0) (n : ℕ) :
    @MeasurableSet Ω (naturalSigma X ((n : ℝ≥0) * delta))
      {ω | ∀ k : ℕ, k ≤ n → X ((k : ℝ≥0) * delta) ω ≤ s} := by
  have heq :
      {ω : Ω | ∀ k : ℕ, k ≤ n → X ((k : ℝ≥0) * delta) ω ≤ s} =
        ⋂ k ∈ Finset.range (n+1),
          {ω : Ω | X ((k : ℝ≥0) * delta) ω ≤ s} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range, Nat.lt_succ_iff]
  rw [heq]
  apply Finset.measurableSet_biInter
  intro k hk
  have htime : (k : ℝ≥0) * delta ≤ (n : ℝ≥0) * delta := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact (measurableSet_Iic).preimage
    (naturalSigma_measurable_past X _ _ htime)
