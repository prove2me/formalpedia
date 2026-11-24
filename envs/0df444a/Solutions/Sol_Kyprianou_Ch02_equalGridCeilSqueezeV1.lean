-- Prove2me | solution 1 for Kyprianou.Ch02.equalGridCeilSqueezeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:47:41.500806+00:00
-- url     : https://prove2.me/submissions/915ba7d8-df50-495f-a09f-3a82d4eeb520

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (a b : ℝ≥0) (hab : a < b) :
    let g : ℕ → ℕ → ℝ≥0 := fun n k =>
      a + (b - a) * (k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let r : ℕ → ℝ≥0 → ℝ≥0 := fun n x =>
      g n ⌈(x - a) * ((n + 1 : ℕ) : ℝ≥0) / (b - a)⌉₊
    ∀ n x, x ∈ Icc a b →
      x ≤ r n x ∧ r n x ≤ x+(b-a)/((n+1 : ℕ) : ℝ≥0) := by
  dsimp only
  intro n x hx
  let N : ℝ≥0 := (n+1 : ℕ)
  let q : ℝ≥0 := (x-a)*N/(b-a)
  let k : ℕ := ⌈q⌉₊
  change x ≤ a+(b-a)*(k:ℝ≥0)/N ∧
    a+(b-a)*(k:ℝ≥0)/N ≤ x+(b-a)/N
  have hd : 0 < b-a := tsub_pos_of_lt hab
  have hN : 0 < N := by dsimp [N]; positivity
  have hmul : (b-a)*q = (x-a)*N := by dsimp [q]; field_simp
  have hlo := mul_le_mul_of_nonneg_left (Nat.le_ceil q) hd.le
  have hup := mul_le_mul_of_nonneg_left (Nat.ceil_lt_add_one (by positivity : 0 ≤ q)).le hd.le
  change (b-a)*q ≤ (b-a)*(k:ℝ≥0) at hlo
  change (b-a)*(k:ℝ≥0) ≤ (b-a)*(q+1) at hup
  rw [hmul] at hlo
  rw [mul_add, hmul, mul_one] at hup
  constructor
  · rw [← add_tsub_cancel_of_le hx.1]
    exact add_le_add_right ((le_div_iff₀ hN).2 hlo) _
  · calc
      _ ≤ a+(((x-a)*N+(b-a))/N) :=
        add_le_add_right ((div_le_div_iff_of_pos_right hN).2 hup) _
      _ = _ := by rw [add_div, mul_div_cancel_right₀ _ hN.ne', ← add_assoc,
        add_tsub_cancel_of_le hx.1]
