-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulLevyTripleExponentAlgebraV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:04:23.912955+00:00
-- url     : https://prove2.me/submissions/987057cc-14f6-464b-ad24-44faa2ad6995

import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulLevyExponentSmallLargeSplitV1
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou
noncomputable section

theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure] :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      (Complex.exp ((((t : ℝ) : ℂ)) *
          (-Complex.I * (a : ℂ) * (ξ : ℂ) -
            (((σ : ℝ) ^ 2 * ξ ^ 2 / 2 : ℝ) : ℂ)))) * (Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in {x : ℝ | 1 ≤ |x|},
            (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂levyMeasure)) * (Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in Set.Ioo (-1 : ℝ) 1,
            ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure)) = (Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) := by
  intro t ξ
  let small : Set ℝ := Set.Ioo (-1 : ℝ) 1
  let large : Set ℝ := {x : ℝ | 1 ≤ |x|}
  have hsmall : small = {x : ℝ | |x| < 1} := by
    ext x
    change (-1 : ℝ) < x ∧ x < 1 ↔ |x| < 1
    constructor
    · rintro ⟨hl, hr⟩
      exact abs_lt.mpr ⟨by linarith, hr⟩
    · intro hx
      rcases abs_lt.mp hx with ⟨hl, hr⟩
      exact ⟨by linarith, hr⟩
  have hlarge : large = smallᶜ := by
    ext x
    simp [large, hsmall, not_lt]
  have hLargeMeas : MeasurableSet large := by
    change MeasurableSet {x : ℝ | (1 : ℝ) ≤ |x|}
    exact (isClosed_le continuous_const continuous_abs).measurableSet
  have hEqOn : Set.EqOn
      (ProbabilityTheory.levyCompensatedIntegrand ξ)
      (fun x : ℝ =>
        Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1)
      large := by
    intro x hx
    have hxnot : ¬ |x| < 1 := not_lt.mpr hx
    have hmul : ((x : ℂ) * (ξ : ℂ) * Complex.I) =
        Complex.I * (((ξ * x : ℝ) : ℂ)) := by
      push_cast
      ring
    simp [ProbabilityTheory.levyCompensatedIntegrand, hxnot, hmul]
  have hLargeIntegral :
      (∫ x in smallᶜ,
        ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure) =
      (∫ x in large,
        (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂levyMeasure) := by
    calc
      (∫ x in smallᶜ,
          ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure) =
        ∫ x in large,
          ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure := by
        rw [hlarge]
      _ = _ := MeasureTheory.setIntegral_congr_fun hLargeMeas hEqOn
  have hexponent :=
    Kyprianou.Ch02.sourceFaithfulLevyExponentSmallLargeSplitV1
      a σ levyMeasure hlevyMeasure ξ
  dsimp [small, large] at hLargeIntegral
  rw [hexponent, hLargeIntegral]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring
