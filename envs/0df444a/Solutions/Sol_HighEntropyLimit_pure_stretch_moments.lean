-- Prove2me | solution 1 for HighEntropyLimit.pure_stretch_moments
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:37:32.026696+00:00
-- url     : https://prove2.me/submissions/aba61d35-548e-4ecd-b16e-93a74c1c53b6

import Mathlib
import Definitions.Def_HighEntropyLimit_phase_space_stretch

open MeasureTheory HighEntropyLimit

theorem solution (lam : ℝ) (hlam : 1 < lam) (ρ : ℝ × ℝ → ℝ) (n m : ℕ) :
    ∫ z, z.1 ^ n * z.2 ^ m * pureStretch lam ρ z =
      Real.sqrt lam ^ (n + m) * ∫ z, z.1 ^ n * z.2 ^ m * ρ z := by
  have hl : 0 < lam := by linarith
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hl
  set s := Real.sqrt lam with hsdef
  have hss : s * s = lam := Real.mul_self_sqrt hl.le
  let h : ℝ × ℝ → ℝ := fun w => (s * w.1) ^ n * (s * w.2) ^ m * (lam⁻¹ * ρ w)
  have h1 : ∀ z : ℝ × ℝ, z.1 ^ n * z.2 ^ m * pureStretch lam ρ z = h (s⁻¹ • z) := by
    intro z
    simp only [h, pureStretch, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, ← hsdef]
    rw [mul_inv_cancel_left₀ hs.ne', mul_inv_cancel_left₀ hs.ne']
  simp_rw [h1]
  rw [Measure.integral_comp_smul, Module.finrank_prod, Module.finrank_self]
  simp only [h, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul]
  congr 1; funext w
  rw [inv_pow, inv_inv, abs_of_pos (by positivity), mul_pow, mul_pow, pow_add]
  field_simp
  rw [show s ^ 2 = lam by rw [sq, hss]]
  ring
