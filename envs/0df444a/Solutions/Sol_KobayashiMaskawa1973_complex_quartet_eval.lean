-- Prove2me | solution 1 for KobayashiMaskawa1973.complex_quartet_eval
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T16:59:10.740251+00:00
-- url     : https://prove2.me/submissions/83ebb753-5583-4738-9e21-335c913111b0

import Mathlib

open Complex ComplexConjugate

theorem solution (s : ℝ) :
    (((1 / s : ℂ) * (1 / (2 * s) - I / 2) * star (-1 / 2 : ℂ) * star (1 / 2 : ℂ))).im =
      1 / (8 * s) := by
  have h4 : star (-1 / 2 : ℂ) = -1 / 2 := by
    rw [star_def]
    simpa using (conj_ofReal (-1 / 2 : ℝ))
  have h5 : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [star_def]
    simpa using (conj_ofReal (1 / 2 : ℝ))
  rw [h4, h5]
  have hval : (1 / s : ℂ) * (1 / (2 * s) - I / 2) * (-1 / 2) * (1 / 2) =
      ((-1 / (8 * s ^ 2) : ℝ) : ℂ) + ((1 / (8 * s) : ℝ) : ℂ) * I := by
    ring_nf
    apply Complex.ext <;>
      simp [add_re, add_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im] <;>
      ring
  rw [hval, add_im]
  have hL : (((-1 / (8 * s ^ 2) : ℝ) : ℂ)).im = 0 := ofReal_im _
  have hR : ((((1 / (8 * s) : ℝ) : ℂ) * I).im) = 1 / (8 * s) := by
    rw [mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  rw [hL, hR]
  ring
