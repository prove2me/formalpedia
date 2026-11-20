-- Prove2me | solution 1 for Kyprianou.Ch01.stableAboveOneUntruncatedFourierReflection
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:45:55.149022+00:00
-- url     : https://prove2.me/submissions/cdea41fa-3a4a-4505-a8de-2839a5bb0d32

import Mathlib
open MeasureTheory Set Real Complex
open scoped ComplexConjugate
set_option autoImplicit false

theorem solution
    (alpha xi : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (((-xi * r : ℝ) : ℂ))) - 1 -
        Complex.I * (((-xi * r : ℝ) : ℂ))) /
        (((r ^ (alpha + 1) : ℝ) : ℂ)) ∂volume) =
      conj
        (∫ r in Set.Ioi (0 : ℝ),
          (Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) - 1 -
            Complex.I * (((xi * r : ℝ) : ℂ))) /
            (((r ^ (alpha + 1) : ℝ) : ℂ)) ∂volume) := by
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hneg : (((-xi * r : ℝ) : ℂ)) =
      -(((xi * r : ℝ) : ℂ)) := by push_cast; ring
  dsimp only
  rw [hneg]
  simp only [map_div₀, map_sub, map_mul, conj_ofReal,
    ← Complex.exp_conj, map_one, conj_I]
  congr 1
  all_goals ring
