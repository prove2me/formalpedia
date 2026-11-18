-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_two_cell_integral_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:10:43.90022+00:00
-- url     : https://prove2.me/submissions/e142f751-1052-4c00-a88c-51da7e7dc693

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_two_cell_integral_ae_eq
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_real_first_moment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Signed two-cell Campbell formula for the original Poisson integral. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤)
    (a b : ℝ) :
    (∫ ω, (∫ x, (a * A.indicator (fun _ => (1 : ℝ)) x +
      b * B.indicator (fun _ => (1 : ℝ)) x) ∂
      (ProbabilityTheory.poissonRandomMeasure K Y ω)) ∂P) =
      a * (m A).toReal + b * (m B).toReal := by
  let ZA : Ω → ℝ := fun ω => (poissonRandomMeasure K Y ω A).toReal
  let ZB : Ω → ℝ := fun ω => (poissonRandomMeasure K Y ω B).toReal
  have hA1 := Kyprianou.ProofPreparation.poisson_prm_eval_real_first_moment
    P m K Y hd A hA hfinA
  have hB1 := Kyprianou.ProofPreparation.poisson_prm_eval_real_first_moment
    P m K Y hd B hB hfinB
  have hAE := Kyprianou.ProofPreparation.poisson_prm_two_cell_integral_ae_eq
    P m K Y hd A B hA hB hfinA hfinB a b
  calc
    (∫ ω, (∫ x, (a * A.indicator (fun _ => (1 : ℝ)) x +
      b * B.indicator (fun _ => (1 : ℝ)) x) ∂
      (poissonRandomMeasure K Y ω)) ∂P) =
        ∫ ω, a * ZA ω + b * ZB ω ∂P := by
      apply integral_congr_ae
      exact hAE
    _ = a * (∫ ω, ZA ω ∂P) + b * (∫ ω, ZB ω ∂P) := by
      rw [integral_add (hA1.1.const_mul a) (hB1.1.const_mul b),
        integral_const_mul, integral_const_mul]
    _ = a * (m A).toReal + b * (m B).toReal := by
      rw [hA1.2, hB1.2]
