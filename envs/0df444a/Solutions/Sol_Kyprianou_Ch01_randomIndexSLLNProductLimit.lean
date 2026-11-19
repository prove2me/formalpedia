-- Prove2me | solution 1 for Kyprianou.Ch01.randomIndexSLLNProductLimit
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:03:17.068621+00:00
-- url     : https://prove2.me/submissions/d2abdf08-c754-4e70-9f67-772ca58afe95

import Mathlib
open Filter
open scoped NNReal Topology
set_option autoImplicit false

theorem solution
    (S : ℕ → ℝ) (N : ℝ≥0 → ℕ) (mu rate : ℝ)
    (hS0 : S 0 = 0)
    (hS : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * S n) atTop (𝓝 mu))
    (hN : Tendsto N atTop atTop)
    (hRate : Tendsto (fun t : ℝ≥0 => (N t : ℝ) / (1 + (t : ℝ)))
      atTop (𝓝 rate)) :
    Tendsto (fun t : ℝ≥0 => S (N t) / (1 + (t : ℝ)))
      atTop (𝓝 (mu * rate)) := by
  have h1 : Tendsto (fun t : ℝ≥0 => (N t : ℝ)⁻¹ * S (N t)) atTop (𝓝 mu) :=
    hS.comp hN
  have h2 := h1.mul hRate
  refine h2.congr' ?_
  have hev : ∀ᶠ t in atTop, 1 ≤ N t := hN.eventually_ge_atTop 1
  filter_upwards [hev] with t ht
  have hNpos : (0 : ℝ) < N t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < 1 + (t : ℝ) := by positivity
  field_simp
