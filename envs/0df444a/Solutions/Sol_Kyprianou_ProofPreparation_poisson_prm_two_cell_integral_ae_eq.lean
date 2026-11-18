-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_two_cell_integral_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:26:38.318729+00:00
-- url     : https://prove2.me/submissions/f3bf61dd-ad78-47b4-b06a-212415d4e7bb

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A two-cell Poisson integral is almost surely a weighted sum of finite counts. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤)
    (a b : ℝ) :
    ∀ᵐ ω ∂P,
      (∫ x, (a * A.indicator (fun _ => (1 : ℝ)) x +
        b * B.indicator (fun _ => (1 : ℝ)) x) ∂
        (ProbabilityTheory.poissonRandomMeasure K Y ω)) =
          a * (ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal +
            b * (ProbabilityTheory.poissonRandomMeasure K Y ω B).toReal := by
  have hfa : ∀ᵐ ω ∂P, poissonRandomMeasure K Y ω A < ⊤ :=
    ae_poissonRandomMeasure_apply_lt_top hd hA hfinA
  have hfb : ∀ᵐ ω ∂P, poissonRandomMeasure K Y ω B < ⊤ :=
    ae_poissonRandomMeasure_apply_lt_top hd hB hfinB
  filter_upwards [hfa, hfb] with ω hAω hBω
  let Q : Measure E := poissonRandomMeasure K Y ω
  have hIA : Integrable (A.indicator (fun _ => (1 : ℝ))) Q :=
    (integrableOn_const (μ := Q) hAω.ne).integrable_indicator hA
  have hIB : Integrable (B.indicator (fun _ => (1 : ℝ))) Q :=
    (integrableOn_const (μ := Q) hBω.ne).integrable_indicator hB
  change (∫ x, a * A.indicator (fun _ => (1 : ℝ)) x +
    b * B.indicator (fun _ => (1 : ℝ)) x ∂Q) =
    a * (Q A).toReal + b * (Q B).toReal
  calc
    (∫ x, a * A.indicator (fun _ => (1 : ℝ)) x +
      b * B.indicator (fun _ => (1 : ℝ)) x ∂Q) =
        (∫ x, a * A.indicator (fun _ => (1 : ℝ)) x ∂Q) +
          (∫ x, b * B.indicator (fun _ => (1 : ℝ)) x ∂Q) :=
      integral_add (hIA.const_mul a) (hIB.const_mul b)
    _ = a * (Q A).toReal + b * (Q B).toReal := by
      rw [integral_const_mul, integral_const_mul]
      have hEA : (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂Q) =
          (Q A).toReal := integral_indicator_one hA
      have hEB : (∫ x, B.indicator (fun _ => (1 : ℝ)) x ∂Q) =
          (Q B).toReal := integral_indicator_one hB
      exact congrArg₂ (fun u v : ℝ => a * u + b * v) hEA hEB
