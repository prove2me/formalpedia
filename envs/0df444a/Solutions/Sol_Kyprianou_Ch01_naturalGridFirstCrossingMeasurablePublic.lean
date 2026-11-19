-- Prove2me | solution 1 for Kyprianou.Ch01.naturalGridFirstCrossingMeasurablePublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T10:13:59.461244+00:00
-- url     : https://prove2.me/submissions/1f27c7e8-d061-4606-8d38-59f22fef7fe8

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Data.Nat.Find
import Mathlib.Data.NNReal.Defs
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_finiteGridNoCrossingNaturalMeasurablePublic
import Theorems.Thm_Kyprianou_Ch01_firstGridTriggerPrefixCharacterisationPublic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Kyprianou.Ch01 Set
open scoped NNReal
set_option autoImplicit false

/-- A sentinel-capped first grid crossing has observable continuation events. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (delta : ℝ≥0) (N : ℕ) :
    let τ : Ω → ℕ := fun ω => by
      classical
      exact Nat.find (show ∃ k : ℕ,
        k = N ∨ s < X ((k : ℝ≥0) * delta) ω from ⟨N, Or.inl rfl⟩)
    (∀ ω, τ ω ≤ N) ∧
      ∀ n, n < N →
        @MeasurableSet Ω (naturalSigma X ((n : ℝ≥0) * delta))
          {ω | n < τ ω} := by
  classical
  let p : ℕ → Ω → Prop := fun k ω => s < X ((k : ℝ≥0) * delta) ω
  let τ : Ω → ℕ := fun ω => by
    classical
    exact Nat.find (show ∃ k : ℕ, k = N ∨ p k ω from ⟨N, Or.inl rfl⟩)
  have hh : (∀ ω, τ ω ≤ N) ∧
      ∀ n : ℕ, n < N → ∀ ω : Ω,
        (n < τ ω ↔ ∀ k : ℕ, k ≤ n → ¬p k ω) := by
    simpa only [p, τ] using
      (firstGridTriggerPrefixCharacterisationPublic
        (fun k ω => s < X ((k : ℝ≥0) * delta) ω) N)
  constructor
  · exact hh.1
  · intro n hn
    have heq : {ω : Ω | n < τ ω} =
        {ω : Ω | ∀ k : ℕ, k ≤ n → X ((k : ℝ≥0) * delta) ω ≤ s} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h k hk
        exact le_of_not_gt ((hh.2 n hn ω).1 h k hk)
      · intro h
        apply (hh.2 n hn ω).2
        intro k hk
        exact not_lt_of_ge (h k hk)
    rw [heq]
    exact finiteGridNoCrossingNaturalMeasurablePublic X s delta n
