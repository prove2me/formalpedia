-- Prove2me | solution 1 for MasulloRH.global_collar_laplace_zero_projection_deficit
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T16:59:48.021492+00:00
-- url     : https://prove2.me/submissions/b55e343a-d718-4a0e-b649-6e1f62cf9b8b

import Mathlib
open MeasureTheory
open scoped InnerProductSpace
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (u k : H) (v : ℂ) (c d : ℝ) (hcd : c < d) (hv : 0 < v.re)
    (vanish : ∀ x ∈ U, ⟪k,x⟫_ℂ = 0)
    (pairing : ⟪k,u⟫_ℂ = ∫ x : ℝ in c..d, Complex.exp (-v * x)) :
    0 < Real.exp (-v.re*c) - Real.exp (-v.re*d) ∧
    (Real.exp (-v.re*c) - Real.exp (-v.re*d))^2 ≤
      (‖u‖^2 - ‖U.starProjection u‖^2) * (‖v‖ * ‖k‖)^2 ∧
    ‖U.starProjection u‖ < ‖u‖ := by
  have hv0 : v ≠ 0 := by intro e; simp [e] at hv
  have hp : 0 < Real.exp (-v.re*c) - Real.exp (-v.re*d) := by
    apply sub_pos.mpr
    apply Real.exp_lt_exp.mpr
    nlinarith [mul_pos hv (sub_pos.mpr hcd)]
  have hev : ⟪k,u⟫_ℂ * (-v) = Complex.exp (-v * d) - Complex.exp (-v * c) := by
    rw [pairing, integral_exp_mul_complex (c := -v) (neg_ne_zero.mpr hv0)]
    field_simp
  have hn (x : ℝ) : ‖Complex.exp (-v * x)‖ = Real.exp (-v.re*x) := by
    rw [Complex.norm_exp]
    simp
  have htri := norm_sub_norm_le (Complex.exp (-v * c)) (Complex.exp (-v * d))
  rw [hn, hn, norm_sub_rev, ← hev, norm_mul, norm_neg] at htri
  have hkill : ⟪k, Uᗮ.starProjection u⟫_ℂ = ⟪k,u⟫_ℂ := by
    conv_rhs => rw [← U.starProjection_add_starProjection_orthogonal u]
    rw [inner_add_right, vanish _ (U.starProjection_apply_mem u), zero_add]
  have hcs : ‖⟪k, Uᗮ.starProjection u⟫_ℂ‖ ≤ ‖k‖ * ‖Uᗮ.starProjection u‖ := norm_inner_le_norm k (Uᗮ.starProjection u)
  rw [hkill] at hcs
  have hb := htri.trans (mul_le_mul_of_nonneg_right hcs (norm_nonneg v))
  have hs := pow_le_pow_left₀ hp.le hb 2
  have he := U.norm_sq_eq_add_norm_sq_starProjection u
  have e : ‖u‖^2 - ‖U.starProjection u‖^2 = ‖Uᗮ.starProjection u‖^2 := by linarith
  refine ⟨hp, ?_, ?_⟩
  · rw [e]
    calc
      _ ≤ (‖k‖ * ‖Uᗮ.starProjection u‖ * ‖v‖)^2 := hs
      _ = _ := by ring
  · by_contra! h
    have hh := pow_le_pow_left₀ (norm_nonneg u) h 2
    have hz : ‖Uᗮ.starProjection u‖ = 0 := by nlinarith [sq_nonneg ‖Uᗮ.starProjection u‖]
    rw [hz] at hb
    simp only [mul_zero, zero_mul] at hb
    exact (not_lt_of_ge hb) hp
