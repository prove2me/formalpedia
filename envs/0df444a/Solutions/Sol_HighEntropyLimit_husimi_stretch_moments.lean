-- Prove2me | solution 1 for HighEntropyLimit.husimi_stretch_moments
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:37:41.886052+00:00
-- url     : https://prove2.me/submissions/e9d79e1d-48d4-4a50-aedf-f4a2f1de8d80

import Mathlib
import Definitions.Def_HighEntropyLimit_phase_space_stretch

open MeasureTheory ComplexConjugate HighEntropyLimit

theorem solution (lam : ℝ) (hlam : 1 < lam) (Q : ℂ → ℝ) (n m : ℕ) :
    ∫ α : ℂ, α ^ n * (conj α) ^ m * (husimiStretch lam Q α : ℂ) =
      ((Real.sqrt lam : ℝ) : ℂ) ^ (n + m) * ∫ β : ℂ, β ^ n * (conj β) ^ m * (Q β : ℂ) := by
  have hl : 0 < lam := by linarith
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hl
  set s := Real.sqrt lam with hsdef
  have hss : s * s = lam := Real.mul_self_sqrt hl.le
  let h : ℂ → ℂ := fun w => ((s : ℂ) * w) ^ n * ((s : ℂ) * conj w) ^ m * ((lam⁻¹ * Q w : ℝ) : ℂ)
  have h1 : ∀ α : ℂ, α ^ n * (conj α) ^ m * (husimiStretch lam Q α : ℂ) = h (s⁻¹ • α) := by
    intro α
    simp only [h, husimiStretch, Complex.real_smul, ← hsdef, map_mul, Complex.conj_ofReal]
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    rw [mul_inv_cancel_left₀ hs', mul_inv_cancel_left₀ hs']
  simp_rw [h1]
  rw [Measure.integral_comp_smul, Complex.finrank_real_complex]
  simp only [h]
  rw [← integral_const_mul, Complex.real_smul, ← integral_const_mul]
  congr 1; funext w
  rw [inv_pow, inv_inv, abs_of_pos (by positivity), mul_pow, mul_pow, pow_add]
  have hs2 : (s : ℂ) ^ 2 = (lam : ℂ) := by rw [sq, ← Complex.ofReal_mul, hss]
  have hl' : (lam : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  push_cast
  rw [hs2]
  field_simp
