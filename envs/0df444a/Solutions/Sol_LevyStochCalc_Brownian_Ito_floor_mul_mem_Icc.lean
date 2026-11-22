-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.floor_mul_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T04:06:23.075651+00:00
-- url     : https://prove2.me/submissions/1b2af755-781a-4a2e-8e2e-f1900802f0ec

import Mathlib
theorem solution {M x : ℝ} (m : ℕ) (hx : |x| ≤ M) :
    ⌊(2 : ℝ) ^ m * x⌋ ∈ Finset.Icc (-(⌈(2 : ℝ) ^ m * M⌉ + 1)) (⌈(2 : ℝ) ^ m * M⌉ + 1) := by
  simp only [Finset.mem_Icc]
  have hp : (0 : ℝ) ≤ (2 : ℝ)^m := by positivity
  have hx1 : -M ≤ x := (abs_le.mp hx).1
  have hx2 : x ≤ M := (abs_le.mp hx).2
  have hlow : -(2 : ℝ)^m * M ≤ (2 : ℝ)^m*x := by nlinarith
  have hhigh : (2 : ℝ)^m*x ≤ (2 : ℝ)^m*M := by nlinarith
  have hf := Int.floor_le ((2 : ℝ)^m*x)
  have hf' := Int.lt_floor_add_one ((2 : ℝ)^m*x)
  have hc := Int.le_ceil ((2 : ℝ)^m*M)
  constructor
  · have h : (-((⌈(2 : ℝ)^m*M⌉ : ℤ) + 1) : ℝ) ≤ (⌊(2 : ℝ)^m*x⌋ : ℝ) := by push_cast; linarith
    exact_mod_cast h
  · have h : (⌊(2 : ℝ)^m*x⌋ : ℝ) ≤ (((⌈(2 : ℝ)^m*M⌉ : ℤ) + 1) : ℝ) := by push_cast; linarith
    exact_mod_cast h
#print axioms solution
