-- Prove2me | solution 1 for Kyprianou.Ch01.stableAboveOneUntruncatedGammaAll
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:57:02.511039+00:00
-- url     : https://prove2.me/submissions/525cda6b-7528-4d16-9bc7-ee94be549989

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAboveOneUntruncatedPositiveGammaValue
import Theorems.Thm_Kyprianou_Ch01_stableAboveOneUntruncatedFourierReflection
import Theorems.Thm_Kyprianou_Ch01_stableGammaPositiveFrequencyPhase
import Theorems.Thm_Kyprianou_Ch01_stableGammaNegativeFrequencyPhase
open MeasureTheory Set Real Complex
open scoped ComplexConjugate
set_option autoImplicit false

theorem solution
 (alpha xi : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
 (∫ r in Set.Ioi (0 : ℝ),
   (Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) - 1 -
    Complex.I * (((xi * r : ℝ) : ℂ))) /
   (((r ^ (alpha + 1) : ℝ) : ℂ)) ∂volume) =
 (if xi = 0 then (0 : ℂ) else
   (((Real.Gamma (-alpha) : ℝ) : ℂ)) *
     Complex.exp ((alpha : ℂ) *
       Complex.log (-(Complex.I * (xi : ℂ))))) := by
  by_cases hp : 0 < xi
  · rw [if_neg (ne_of_gt hp)]
    exact Kyprianou.Ch01.stableAboveOneUntruncatedPositiveGammaValue
      alpha xi ha1 ha2 hp
  · by_cases hn : xi < 0
    · have hx : 0 < -xi := by linarith
      have hxne : xi ≠ 0 := ne_of_lt hn
      rw [if_neg hxne]
      have hreflection :=
        Kyprianou.Ch01.stableAboveOneUntruncatedFourierReflection
          alpha (-xi)
      have hpositive :=
        Kyprianou.Ch01.stableAboveOneUntruncatedPositiveGammaValue
          alpha (-xi) ha1 ha2 hx
      have hphaseP :=
        Kyprianou.Ch01.stableGammaPositiveFrequencyPhase
          alpha (-xi) hx
      have hphaseN :=
        Kyprianou.Ch01.stableGammaNegativeFrequencyPhase
          alpha xi hn
      have hphase :
          conj
            (Complex.exp ((alpha : ℂ) *
              Complex.log (-(Complex.I * ((-xi : ℝ) : ℂ))))) =
          Complex.exp ((alpha : ℂ) *
              Complex.log (-(Complex.I * (xi : ℂ)))) := by
        rw [hphaseP, hphaseN]
        simp [← Complex.exp_conj, conj_I, abs_of_neg hn, map_ofNat]
      calc
        _ = conj (∫ r in Set.Ioi (0 : ℝ),
            (Complex.exp (Complex.I * (((-xi * r : ℝ) : ℂ))) - 1 -
              Complex.I * (((-xi * r : ℝ) : ℂ))) /
              (((r ^ (alpha + 1) : ℝ) : ℂ)) ∂volume) := by
                simpa only [neg_neg] using hreflection
        _ = conj
            ((((Real.Gamma (-alpha) : ℝ) : ℂ)) *
              Complex.exp ((alpha : ℂ) *
                Complex.log (-(Complex.I * ((-xi : ℝ) : ℂ))))) := by
                  rw [hpositive]
        _ = _ := by
          rw [map_mul, conj_ofReal, hphase]
    · have hx : xi = 0 :=
        le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
      subst xi
      simp
