-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaStrictLeftIntegrationByParts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:23:26.634185+00:00
-- url     : https://prove2.me/submissions/01d9e6b4-5a0b-4051-a881-6afc71135029

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftExpDerivative
import Theorems.Thm_Kyprianou_Ch01_stableGammaPositivePowerAntiderivative
import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftIBPBoundaryZero
import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftIBPProductIntegrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set Filter
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hwre : w.re < 0) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (w * (r : ℂ)) - 1) *
        ((r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume) =
      (w / (alpha : ℂ)) *
        (∫ r in Set.Ioi (0 : ℝ),
          Complex.exp (w * (r : ℂ)) *
            ((r ^ (-alpha) : ℝ) : ℂ) ∂volume) := by
  let u : ℝ → ℂ := fun r => Complex.exp (w * (r : ℂ)) - 1
  let v : ℝ → ℂ := fun r => ((r ^ (-alpha) / (-alpha) : ℝ) : ℂ)
  let u' : ℝ → ℂ := fun r => w * Complex.exp (w * (r : ℂ))
  let v' : ℝ → ℂ := fun r => ((r ^ (-alpha - 1) : ℝ) : ℂ)
  have hu : ∀ r ∈ Set.Ioi (0 : ℝ), HasDerivAt u (u' r) r := by
    intro r hr
    exact Kyprianou.Ch01.stableGammaStrictLeftExpDerivative w r
  have hv : ∀ r ∈ Set.Ioi (0 : ℝ), HasDerivAt v (v' r) r := by
    intro r hr
    exact (Kyprianou.Ch01.stableGammaPositivePowerAntiderivative
      alpha r h0 h1 hr).ofReal_comp
  obtain ⟨hprod, hother⟩ :=
    Kyprianou.Ch01.stableGammaStrictLeftIBPProductIntegrable alpha h0 h1 w hwre
  obtain ⟨hzero, hinfty⟩ :=
    Kyprianou.Ch01.stableGammaStrictLeftIBPBoundaryZero alpha h0 h1 w hwre
  have h := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (u := u) (v := v) (u' := u') (v' := v')
    hu hv hprod hother hzero hinfty
  have hα : (alpha : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  have hpoint (r : ℝ) :
      u' r * v r = (-(w / (alpha : ℂ))) *
        (Complex.exp (w * (r : ℂ)) * (((r ^ (-alpha) : ℝ)) : ℂ)) := by
    dsimp [u', v]
    push_cast
    field_simp [hα]
  have hint : (∫ r in Set.Ioi (0 : ℝ), u' r * v r ∂volume) =
      (-(w / (alpha : ℂ))) *
        (∫ r in Set.Ioi (0 : ℝ),
          Complex.exp (w * (r : ℂ)) *
            (((r ^ (-alpha) : ℝ)) : ℂ) ∂volume) := by
    simp_rw [hpoint]
    exact MeasureTheory.integral_const_mul _ _
  rw [hint] at h
  simpa only [u, v', Pi.mul_apply, sub_zero, zero_sub,
    neg_mul, neg_neg] using h
