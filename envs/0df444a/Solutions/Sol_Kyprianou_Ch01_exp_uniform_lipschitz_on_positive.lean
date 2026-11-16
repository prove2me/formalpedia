-- Prove2me | solution 1 for Kyprianou.Ch01.exp_uniform_lipschitz_on_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T18:24:26.091324+00:00
-- url     : https://prove2.me/submissions/7f0db8c5-5a97-4a40-9700-cfeb60f7aafd

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_exp_scaled_derivative_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real Set
open scoped Topology
set_option autoImplicit false

/-- Exponential Laplace weights have a moment-independent local Lipschitz constant. -/
theorem solution
    (delta : ℝ) (hd : 0 < delta) (k : ℕ)
    (x y : ℝ) (hx : delta ≤ x) (hy : delta ≤ y) :
    |Real.exp (-y * (k : ℝ)) - Real.exp (-x * (k : ℝ))| ≤
      delta⁻¹ * |y - x| := by
  let f : ℝ → ℝ := fun z => Real.exp (-z * (k : ℝ))
  have hder (z : ℝ) :
      HasDerivAt f (-(k : ℝ) * Real.exp (-z * (k : ℝ))) z := by
    dsimp [f]
    have hinner := ((hasDerivAt_id z).neg.mul_const (k : ℝ))
    have houter := hinner.exp
    have heq :
        Real.exp (-z * (k : ℝ)) * ((-1 : ℝ) * (k : ℝ)) =
        -(k : ℝ) * Real.exp (-z * (k : ℝ)) := by ring
    exact houter.congr_deriv heq
  have hbound (z : ℝ) (hz : z ∈ Ici delta) :
      ‖deriv f z‖ ≤ delta⁻¹ := by
    have hn : ‖-(k : ℝ) * Real.exp (-z * (k : ℝ))‖ =
        (k : ℝ) * Real.exp (-z * (k : ℝ)) := by
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      rw [abs_of_nonneg (Nat.cast_nonneg k), abs_of_pos (Real.exp_pos _)]
    rw [(hder z).deriv, hn]
    exact Kyprianou.Ch01.exp_scaled_derivative_bound delta hd k z hz
  have h := (convex_Ici delta).norm_image_sub_le_of_norm_deriv_le
    (fun z (_ : z ∈ Ici delta) => (hder z).differentiableAt)
    hbound hx hy
  simpa only [Real.norm_eq_abs, f] using h
