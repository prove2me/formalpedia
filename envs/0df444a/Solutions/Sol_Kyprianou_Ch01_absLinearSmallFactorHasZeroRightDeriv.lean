-- Prove2me | solution 1 for Kyprianou.Ch01.absLinearSmallFactorHasZeroRightDeriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:47:52.89839+00:00
-- url     : https://prove2.me/submissions/5f056352-f1a3-407c-b086-193253cefa7c

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.SetSemiring
open MeasureTheory Filter Set
set_option autoImplicit false

theorem solution
    (f h : ℝ → ℝ) (c : ℝ)
    (hSmall : Tendsto h
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hBound : ∀ t : ℝ, 0 ≤ t → |f t| ≤ c * t * h t) :
    HasDerivWithinAt f 0 (Set.Ici 0) 0 := by
  have hf0 : f 0 = 0 := by
    have hb := hBound 0 le_rfl
    have habs : |f 0| ≤ 0 := by simpa using hb
    exact abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : (Set.Ici (0 : ℝ) \ {0}) = Set.Ioi 0 := by
    ext t
    change (0 : ℝ) ≤ t ∧ t ≠ 0 ↔ 0 < t
    constructor
    · rintro ⟨hge, hne⟩
      exact lt_of_le_of_ne hge (Ne.symm hne)
    · intro ht
      exact ⟨ht.le, ne_of_gt ht⟩
  rw [hset]
  have hnorm :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ‖slope f 0 t‖ ≤ c * h t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change (0 : ℝ) < t at ht
    have hb := hBound t ht.le
    rw [slope_def_field, hf0, sub_zero, sub_zero,
      Real.norm_eq_abs, abs_div]
    rw [abs_of_pos ht]
    apply (div_le_iff₀ ht).2
    calc
      |f t| ≤ c * t * h t := hb
      _ = (c * h t) * t := by ring
  have htend :
      Tendsto (fun t : ℝ => c * h t)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa only [mul_zero] using hSmall.const_mul c
  exact squeeze_zero_norm' hnorm htend
