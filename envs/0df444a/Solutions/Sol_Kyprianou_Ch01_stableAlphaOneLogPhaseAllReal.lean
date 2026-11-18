-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneLogPhaseAllReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:40:12.074646+00:00
-- url     : https://prove2.me/submissions/f32b7a4e-63c0-4d34-99ad-3c73ae8c6deb

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhase
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneComplexIntegralNegativeConjugate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Set Real
set_option autoImplicit false
/-! Source alpha-one log phase with its original cutoff, now at every positive, negative or zero frequency. -/
theorem solution : ∃ k : ℝ, ∀ xi : ℝ,
    (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) +
        Complex.I * (((xi * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume) =
      (((Real.pi * |xi| / 2 : ℝ) : ℂ) +
        Complex.I * (((xi * Real.log |xi| : ℝ) : ℂ)) -
        Complex.I * (((k * xi : ℝ) : ℂ))) := by
  obtain ⟨k, hPos⟩ := Kyprianou.Ch01.stableAlphaOneLogPhase
  refine ⟨k, ?_⟩
  intro xi
  by_cases hxi : 0 < xi
  · have h := (hPos xi hxi).2
    simpa only [abs_of_pos hxi] using h
  by_cases hxneg : xi < 0
  · have hw : 0 < -xi := neg_pos.mpr hxneg
    have h := (hPos (-xi) hw).2
    have hConj := Kyprianou.Ch01.stableAlphaOneComplexIntegralNegativeConjugate (-xi)
    have hEq : (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) +
        Complex.I * (((xi * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume) =
        star (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * ((((-xi) * r : ℝ) : ℂ))) +
        Complex.I * ((((-xi) * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume) := by
      simpa only [neg_neg] using hConj
    rw [hEq, h]
    apply Complex.ext
    · simp [Complex.star_def, Complex.conj_re, Complex.add_re,
        Complex.sub_re, Complex.mul_re, abs_of_neg hxneg]
    · simp [Complex.star_def, Complex.conj_im, Complex.add_im,
        Complex.sub_im, Complex.mul_im, abs_of_neg hxneg]
      ring
  have hzero : xi = 0 := le_antisymm (le_of_not_gt hxi) (le_of_not_gt hxneg)
  subst xi
  simp
