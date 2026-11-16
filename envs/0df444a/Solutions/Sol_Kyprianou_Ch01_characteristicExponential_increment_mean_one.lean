-- Prove2me | solution 1 for Kyprianou.Ch01.characteristicExponential_increment_mean_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:46:00.135458+00:00
-- url     : https://prove2.me/submissions/b5d26f14-de01-495a-befd-bb508e9de4e3

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_levyIncrement_charFun
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Every normalised Lévy increment characteristic exponential has mean one. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hmeas : ∀ t : ℝ≥0, Measurable (X t))
    (theta : ℝ) (Psi : ℂ)
    (hchar : ∀ u : ℝ≥0,
      charFun (P.map (X u)) theta =
        Complex.exp (-((u : ℝ) : ℂ) * Psi))
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, Complex.exp
      (Complex.I * (theta : ℂ) * ((X t ω - X s ω) : ℂ) +
        (((t - s : ℝ≥0) : ℝ) : ℂ) * Psi) ∂P) = 1 := by
  have hY : Measurable (fun ω => X t ω - X s ω) :=
    (hmeas t).sub (hmeas s)
  have hI :
      (∫ ω, Complex.exp (Complex.I * (theta : ℂ) *
        ((X t ω - X s ω) : ℂ)) ∂P) =
        Complex.exp (-(((t - s : ℝ≥0) : ℝ) : ℂ) * Psi) := by
    rw [← Kyprianou.Ch01.levyIncrement_charFun
      P X hX theta Psi hchar s t hst, charFun_apply_real]
    rw [integral_map hY.aemeasurable (by fun_prop)]
    congr 1
    funext ω
    congr 1
    rw [Complex.ofReal_sub]
    ring
  calc
    (∫ ω, Complex.exp
      (Complex.I * (theta : ℂ) * ((X t ω - X s ω) : ℂ) +
        (((t - s : ℝ≥0) : ℝ) : ℂ) * Psi) ∂P) =
      (∫ ω, Complex.exp
        (Complex.I * (theta : ℂ) * ((X t ω - X s ω) : ℂ)) ∂P) *
        Complex.exp ((((t - s : ℝ≥0) : ℝ) : ℂ) * Psi) := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [Complex.exp_add]
    _ = 1 := by
      rw [hI, ← Complex.exp_add]
      simp
