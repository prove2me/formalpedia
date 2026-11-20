-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaStrictLeftIBPNearZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:56:25.434996+00:00
-- url     : https://prove2.me/submissions/0669637e-5dcc-4be3-9f4a-b6431897e60c

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftExpDerivative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set Filter
open scoped Topology
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hwre : w.re < 0) :
    Tendsto
      (fun r : ℝ => (Complex.exp (w * (r : ℂ)) - 1) *
        (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℂ)) := by
  have hder : HasDerivAt
      (fun r : ℝ => Complex.exp (w * (r : ℂ)) - 1) w 0 := by
    simpa using Kyprianou.Ch01.stableGammaStrictLeftExpDerivative w 0
  have hslope : Tendsto
      (fun r : ℝ => (((r⁻¹ : ℝ)) : ℂ) *
        (Complex.exp (w * (r : ℂ)) - 1))
      (𝓝[>] (0 : ℝ)) (nhds w) := by
    simpa [smul_eq_mul, Complex.real_smul, add_zero,
      Complex.exp_zero] using hder.tendsto_slope_zero_right
  have hpow : Tendsto (fun r : ℝ => r ^ (1 - alpha))
      (𝓝[>] (0 : ℝ)) (nhds (0 : ℝ)) := by
    have ht := (Real.continuous_rpow_const (show 0 ≤ 1 - alpha by linarith)).tendsto 0
    have hh : (0 : ℝ) ^ (1 - alpha) = 0 :=
      Real.zero_rpow (by linarith)
    simpa only [hh] using ht.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hcast : Tendsto
      (fun r : ℝ => (((r ^ (1 - alpha) / (-alpha) : ℝ)) : ℂ))
      (𝓝[>] (0 : ℝ)) (nhds (0 : ℂ)) := by
    have ht : Tendsto
        (fun r : ℝ => r ^ (1 - alpha) / (-alpha))
        (𝓝[>] (0 : ℝ)) (nhds (0 : ℝ)) := by
      simpa using hpow.div_const (-alpha)
    change Tendsto
      (Complex.ofReal ∘ (fun r : ℝ => r ^ (1 - alpha) / (-alpha)))
      (𝓝[>] (0 : ℝ)) (nhds (0 : ℂ))
    exact (Complex.continuous_ofReal.tendsto 0).comp ht
  have h := hslope.mul hcast
  have heq : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      (((r⁻¹ : ℝ)) : ℂ) *
        (Complex.exp (w * (r : ℂ)) - 1) *
        (((r ^ (1 - alpha) / (-alpha) : ℝ)) : ℂ) =
      (Complex.exp (w * (r : ℂ)) - 1) *
        (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
    have hp : r ^ (1 - alpha) = r * r ^ (-alpha) := by
      rw [show 1 - alpha = 1 + -alpha by ring, Real.rpow_add hr]
      simp
    rw [hp]
    push_cast
    field_simp [hr0]
  simpa using h.congr' heq
