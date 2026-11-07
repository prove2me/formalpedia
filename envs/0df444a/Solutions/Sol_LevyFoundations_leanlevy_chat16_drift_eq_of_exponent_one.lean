-- Prove2me | solution 1 for LevyFoundations.leanlevy_chat16_drift_eq_of_exponent_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:06:56.430178+00:00
-- url     : https://prove2.me/submissions/316bd723-c249-4204-ae14-b7f6b994d8fd

import Mathlib
import Definitions.Def_levy_foundations_exponent
import Definitions.Def_levy_foundations_levyKhintchineTriple

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution {T T' : LevyFoundations.LevyKhintchineTriple}
    (hσ : T.gaussianVariance = T'.gaussianVariance)
    (hν : T.levyMeasure = T'.levyMeasure)
    (h : LevyFoundations.exponent T 1 = LevyFoundations.exponent T' 1) :
    T.drift = T'.drift := by
  unfold LevyFoundations.exponent at h
  rw [hσ, hν] at h
  have hI : (T.drift : ℂ) * Complex.I = (T'.drift : ℂ) * Complex.I := by
    have hcancel : (T.drift : ℂ) * ↑(1 : ℝ) * Complex.I
        = (T'.drift : ℂ) * ↑(1 : ℝ) * Complex.I := by
      linear_combination h
    simpa using hcancel
  exact Complex.ofReal_inj.mp (mul_right_cancel₀ Complex.I_ne_zero hI)
