-- Prove2me | solution 1 for Kyprianou.Ch01.stableBelowOneWeightedGammaNegativeFrequency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:56:55.842601+00:00
-- url     : https://prove2.me/submissions/3fd41132-a9f2-4b21-8387-1504c84d88da

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableBelowOneWeightedGammaPositiveFrequency
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
set_option autoImplicit false

theorem solution
    (alpha cpos cneg xi : ℝ)
    (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hxi : xi < 0) (hnonzero : 0 < cpos + cneg) :
    let E : ℝ → ℂ := (fun z : ℝ => if z = 0 then (0 : ℂ) else
      Complex.exp ((alpha : ℂ) *
        Complex.log (-(Complex.I * (z : ℂ)))));
    -((Real.Gamma (-alpha) : ℝ) : ℂ) *
      ((cpos : ℂ) * E xi + (cneg : ℂ) * E (-xi)) =
      (((-Real.Gamma (-alpha) * Real.cos (Real.pi * alpha / 2) *
          (cpos + cneg)) * |xi| ^ alpha : ℝ) : ℂ) *
        (1 + Complex.I *
          (((((cpos - cneg) / (cpos + cneg)) *
            Real.tan (Real.pi * alpha / 2) : ℝ) : ℂ))) := by
  intro E
  have hp :=
    Kyprianou.Ch01.stableBelowOneWeightedGammaPositiveFrequency
      alpha cneg cpos (-xi) ha0 ha1 (by linarith)
      (by simpa only [add_comm] using hnonzero)
  dsimp only at hp
  have hrat : (cneg - cpos) / (cneg + cpos) =
      -((cpos - cneg) / (cpos + cneg)) := by
    rw [add_comm cneg cpos]
    ring
  calc
    -((Real.Gamma (-alpha) : ℝ) : ℂ) *
      ((cpos : ℂ) * E xi + (cneg : ℂ) * E (-xi)) =
      -((Real.Gamma (-alpha) : ℝ) : ℂ) *
      ((cneg : ℂ) * E (-xi) + (cpos : ℂ) * E (-(-xi))) := by
        simp only [neg_neg]
        ring
    _ = (((-Real.Gamma (-alpha) * Real.cos (Real.pi * alpha / 2) *
          (cneg + cpos)) * |(-xi)| ^ alpha : ℝ) : ℂ) *
        (1 - Complex.I *
          (((((cneg - cpos) / (cneg + cpos)) *
            Real.tan (Real.pi * alpha / 2) : ℝ) : ℂ))) := hp
    _ = _ := by rw [hrat]; simp only [abs_neg]; push_cast; ring
