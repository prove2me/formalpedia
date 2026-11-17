-- Prove2me | solution 1 for N25.bounded_of_nonnegative_exp
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:27:19.390394+00:00
-- url     : https://prove2.me/submissions/6f5d95c1-1615-4e62-9de6-0f63f68393ff

import Mathlib

set_option autoImplicit false

open Filter Topology

namespace N25

theorem _root_.solution (f : UpperHalfPlane → ℂ) (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (c : ℂ) (hlim : Tendsto
      (fun τ : UpperHalfPlane => f τ /
        Complex.exp (2 * Real.pi * Complex.I * (ℓ : ℂ) * (τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds c)) :
    UpperHalfPlane.IsBoundedAtImInfty f := by
  have hb : UpperHalfPlane.IsBoundedAtImInfty
      (fun τ : UpperHalfPlane => f τ /
        Complex.exp (2 * Real.pi * Complex.I * (ℓ : ℂ) * (τ : ℂ))) :=
    by
      have hz : ZeroAtFilter UpperHalfPlane.atImInfty
          (fun τ : UpperHalfPlane => f τ /
            Complex.exp (2 * Real.pi * Complex.I * (ℓ : ℂ) * (τ : ℂ)) - c) := by
        simpa only [ZeroAtFilter, sub_self] using hlim.sub_const c
      have hh := hz.boundedAtFilter.add (const_boundedAtFilter UpperHalfPlane.atImInfty c)
      have hadd :
          ((fun τ : UpperHalfPlane => f τ /
            Complex.exp (2 * Real.pi * Complex.I * (ℓ : ℂ) * (τ : ℂ)) - c) +
              Function.const UpperHalfPlane c) =
          (fun τ : UpperHalfPlane => f τ /
            Complex.exp (2 * Real.pi * Complex.I * (ℓ : ℂ) * (τ : ℂ))) := by
        funext τ
        exact sub_add_cancel _ c
      rw [hadd] at hh
      exact hh
  obtain ⟨M, A, hM⟩ := UpperHalfPlane.isBoundedAtImInfty_iff.mp hb
  refine UpperHalfPlane.isBoundedAtImInfty_iff.mpr ⟨M, A, ?_⟩
  intro τ hτ
  let E := Complex.exp (2 * Real.pi * Complex.I * (ℓ : ℂ) * (τ : ℂ))
  have hE : ‖E‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    have hp := mul_nonneg (mul_nonneg Real.pi_pos.le hℓ) τ.im_pos.le
    change 0 ≤ Real.pi * ℓ * (τ : ℂ).im at hp
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    norm_num
    change 0 ≤ Real.pi * ℓ * τ.im at hp
    nlinarith
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  calc
    ‖f τ‖ = ‖f τ / E‖ * ‖E‖ := by rw [← norm_mul, div_mul_cancel₀ _ hE0]
    _ ≤ ‖f τ / E‖ * 1 := mul_le_mul_of_nonneg_left hE (norm_nonneg _)
    _ = ‖f τ / E‖ := mul_one _
    _ ≤ M := hM τ hτ

end N25
