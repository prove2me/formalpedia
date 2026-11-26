-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_ceiling_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:19:41.700033+00:00
-- url     : https://prove2.me/submissions/e9cf045d-bd88-4453-be29-4475810164aa

import Mathlib
open Filter Set
open scoped Topology
set_option autoImplicit false

/-- Right grid rounding stays within one mesh of the original time and below the horizon. -/
theorem solution (T s : ℝ) (hT : 0 < T) (hs : s ∈ Icc 0 T)
    (n : ℕ) (hn : 0 < n) :
    let r := T * (Nat.ceil (s * (n : ℝ) / T) : ℝ) / (n : ℝ)
    s ≤ r ∧ r ≤ T ∧ r ≤ s + T / (n : ℝ) := by
  intro r
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have h0 : 0 ≤ s * (n : ℝ) / T := div_nonneg (mul_nonneg hs.1 hn'.le) hT.le
  have h1 := Nat.le_ceil (s * (n : ℝ) / T)
  have h2 := Nat.ceil_lt_add_one h0
  have h3 : Nat.ceil (s * (n : ℝ) / T) ≤ n := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hT).mpr
    nlinarith [mul_le_mul_of_nonneg_right hs.2 hn'.le]
  have h3' : (Nat.ceil (s * (n : ℝ) / T) : ℝ) ≤ n := by exact_mod_cast h3
  have h1' := (div_le_iff₀ hT).mp h1
  have h2' := mul_lt_mul_of_pos_right h2 hT
  rw [add_mul, div_mul_cancel₀ _ hT.ne'] at h2'
  dsimp [r]
  refine ⟨(le_div_iff₀ hn').mpr (by nlinarith), (div_le_iff₀ hn').mpr (by nlinarith),
    (div_le_iff₀ hn').mpr ?_⟩
  rw [add_mul, div_mul_cancel₀ _ hn'.ne']
  nlinarith
