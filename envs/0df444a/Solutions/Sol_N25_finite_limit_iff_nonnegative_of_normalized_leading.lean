-- Prove2me | solution 1 for N25.finite_limit_iff_nonnegative_of_normalized_leading
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:10.437998+00:00
-- url     : https://prove2.me/submissions/01c814c8-fdc4-4ede-bde8-2695b815c755

import Mathlib

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open Filter Topology

namespace N25

private theorem positive_exponential_tendsto_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun τ : UpperHalfPlane =>
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds 0) := by
  have hi : Tendsto (fun τ : UpperHalfPlane => τ.im) UpperHalfPlane.atImInfty atTop := tendsto_comap
  have hp : 0 < 2 * Real.pi * a := mul_pos (mul_pos (by norm_num) Real.pi_pos) ha
  have ht := (tendsto_neg_atTop_atBot.comp (hi.const_mul_atTop hp))
  have he := Real.tendsto_exp_atBot.comp ht
  have hn (τ : UpperHalfPlane) :
      ‖Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (τ : ℂ))‖ =
        Real.exp (-(2 * Real.pi * a * τ.im)) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
    <;> ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [hn, Function.comp_def] using he

/-- A nonzero exponential leading limit determines whether the unnormalized cusp limit is finite. -/
theorem _root_.solution
    (f : UpperHalfPlane → ℂ) (a : ℝ) (L : ℂ) (hL : L ≠ 0)
    (hlead : Filter.Tendsto
      (fun τ : UpperHalfPlane => f τ /
        Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds L)) :
    (∃ c : ℂ, Filter.Tendsto f UpperHalfPlane.atImInfty (nhds c)) ↔ 0 ≤ a := by
  constructor
  · rintro ⟨c, hc⟩
    by_cases ha : 0 ≤ a
    · exact ha
    · have hn : 0 < -a := neg_pos.mpr (lt_of_not_ge ha)
      have hd := positive_exponential_tendsto_zero (-a) hn
      have he (τ : UpperHalfPlane) : f τ /
          Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (τ : ℂ)) =
          f τ * Complex.exp (2 * Real.pi * Complex.I * ((-a : ℝ) : ℂ) * (τ : ℂ)) := by
        rw [div_eq_mul_inv, ← Complex.exp_neg]
        congr 2
        push_cast
        ring
      have hz : Tendsto
          (fun τ : UpperHalfPlane => f τ /
            Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (τ : ℂ)))
          UpperHalfPlane.atImInfty (nhds 0) := by
        simp_rw [he]
        simpa only [mul_zero] using hc.mul hd
      exact False.elim (hL (tendsto_nhds_unique hlead hz))
  · intro ha
    rcases eq_or_lt_of_le ha with rfl | ha
    · refine ⟨L, ?_⟩
      simpa only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, div_one] using hlead
    · refine ⟨0, ?_⟩
      have ht := hlead.mul (positive_exponential_tendsto_zero a ha)
      simpa only [div_mul_cancel₀ _ (Complex.exp_ne_zero _), mul_zero] using ht

end N25
