-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41RampSequenceV11
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:48:06.196368+00:00
-- url     : https://prove2.me/submissions/9cfb60b9-536f-4711-b7f1-b02cacaae7d5

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41RampDerivativeV10
import Theorems.Thm_Kyprianou_Ch04_exercise41RampValueBoundsV10
import Theorems.Thm_Kyprianou_Ch04_exercise41RampPointwiseV11
import Theorems.Thm_Kyprianou_Ch04_exercise41RampDerivativeLimitV11
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology Interval
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution :
    ∃ p : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ 1 (p n)) ∧
      (∀ n x, 0 ≤ p n x ∧ p n x ≤ max 0 x) ∧
      (∀ x, Tendsto (fun n => p n x) atTop (𝓝 (max 0 x))) ∧
      (∀ n x, 0 ≤ deriv (p n) x ∧ deriv (p n) x ≤ 1) ∧
      (∀ x, Tendsto (fun n => deriv (p n) x) atTop (𝓝 (if 0 < x then 1 else 0))) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let r := fun (n : ℕ) (u : ℝ) => min 1 (max 0 (u / ε n))
  let p := fun (n : ℕ) (x : ℝ) => ∫ u in (0 : ℝ)..x, r n u
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hd (n : ℕ) := exercise41RampDerivativeV10 (ε n) (hε n)
  have hder (n : ℕ) (x : ℝ) : deriv (p n) x = r n x := ((hd n).2.1 x).deriv
  refine ⟨p,fun n => (hd n).1,?_,?_,?_,?_⟩
  · intro n x
    have h := exercise41RampValueBoundsV10 (ε n) (hε n) x
    exact ⟨h.2.1,h.2.2.1⟩
  · exact exercise41RampPointwiseV11 ε hε hlim
  · intro n x
    rw [hder]
    exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩
  · intro x
    simp only [hder]
    exact exercise41RampDerivativeLimitV11 ε hε hlim x
