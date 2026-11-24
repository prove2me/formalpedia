-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_discount_sequence_properties
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:45:49.986483+00:00
-- url     : https://prove2.me/submissions/ed348598-b140-454c-9c64-3f8511e18bd5


import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
open Filter Topology
/-- Positive decreasing discount sequence. -/
theorem solution :
    let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    (∀ n, 0 < r n ∧ r n ≤ 1) ∧ Antitone r ∧ Tendsto r atTop (nhds 0) := by
  dsimp only
  refine ⟨?_, ?_, tendsto_one_div_add_atTop_nhds_zero_nat⟩
  · intro n
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < (n : ℝ)+1)).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · intro i j hij
    apply one_div_le_one_div_of_le (by positivity)
    have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    linarith
