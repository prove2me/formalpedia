-- Prove2me | solution 1 for Kyprianou.Ch01.stableAboveOneWeightedGammaCanonicalForm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:18:10.152597+00:00
-- url     : https://prove2.me/submissions/38042d00-33c1-4074-9523-bcdd6d4ffae2

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAboveOneWeightedGammaPositiveFrequency
import Theorems.Thm_Kyprianou_Ch01_stableAboveOneWeightedGammaNegativeFrequency
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
set_option autoImplicit false

theorem solution
    (alpha cpos cneg xi : ℝ)
    (ha1 : 1 < alpha) (ha2 : alpha < 2)
    (hnonzero : 0 < cpos + cneg) :
    let E : ℝ → ℂ := (fun z : ℝ => if z = 0 then (0 : ℂ) else
  Complex.exp ((alpha : ℂ) *
    Complex.log (-(Complex.I * (z : ℂ)))));
    let sgn : ℝ := if 0 < xi then 1 else if xi < 0 then -1 else 0;
    -((Real.Gamma (-alpha) : ℝ) : ℂ) *
      ((cpos : ℂ) * E xi + (cneg : ℂ) * E (-xi)) =
      (((-Real.Gamma (-alpha) * Real.cos (Real.pi * alpha / 2) *
          (cpos + cneg)) * |xi| ^ alpha : ℝ) : ℂ) *
        (1 - Complex.I *
          (((((cpos - cneg) / (cpos + cneg)) *
            Real.tan (Real.pi * alpha / 2) * sgn : ℝ) : ℂ))) := by
  intro E sgn
  by_cases hp : 0 < xi
  · have hpos :=
      Kyprianou.Ch01.stableAboveOneWeightedGammaPositiveFrequency
        alpha cpos cneg xi ha1 ha2 hp hnonzero
    have hsgn : sgn = 1 := by dsimp [sgn]; simp [hp]
    rw [hpos, hsgn]
    simp
  · by_cases hn : xi < 0
    · have hneg :=
        Kyprianou.Ch01.stableAboveOneWeightedGammaNegativeFrequency
          alpha cpos cneg xi ha1 ha2 hn hnonzero
      have hsgn : sgn = -1 := by
        dsimp [sgn]
        simp [hp, hn]
      rw [hneg, hsgn]
      push_cast
      ring
    · have hx : xi = 0 :=
        le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
      subst xi
      simp [E, sgn, Real.zero_rpow (ne_of_gt (lt_trans zero_lt_one ha1))]
