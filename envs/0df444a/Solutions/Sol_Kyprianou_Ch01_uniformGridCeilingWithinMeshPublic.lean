-- Prove2me | solution 1 for Kyprianou.Ch01.uniformGridCeilingWithinMeshPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T09:43:43.283958+00:00
-- url     : https://prove2.me/submissions/5260b918-6daf-4f1a-973d-8ba59c22907d

import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

/-- Round upwards to a uniform grid point within one mesh interval. -/
theorem solution (delta t : ℝ) (hdelta : 0 < delta) (ht : 0 ≤ t) :
    ∃ n : ℕ, t ≤ (n : ℝ) * delta ∧
      (n : ℝ) * delta < t + delta := by
  classical
  let n : ℕ := Nat.ceil (t / delta)
  have hnonneg : 0 ≤ t / delta := div_nonneg ht hdelta.le
  have hlo : t / delta ≤ (n : ℝ) := Nat.le_ceil _
  have hhi : (n : ℝ) < t / delta + 1 :=
    Nat.ceil_lt_add_one hnonneg
  refine ⟨n, ?_, ?_⟩
  · have hmul : t ≤ (n : ℝ) * delta :=
      (div_le_iff₀ hdelta).mp hlo
    exact hmul
  · have hmul :=
      mul_lt_mul_of_pos_right hhi hdelta
    have hdiv : t / delta * delta = t :=
      div_mul_cancel₀ _ hdelta.ne'
    nlinarith
