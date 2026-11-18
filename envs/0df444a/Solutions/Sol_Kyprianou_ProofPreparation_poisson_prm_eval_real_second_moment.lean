-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_eval_real_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:24:51.739242+00:00
-- url     : https://prove2.me/submissions/db30cb67-55ed-405c-9e75-7f751d173e77

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_indicator_integral_second_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Finite-region real Poisson counts have second moment λ² + λ. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A : Set E) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    (∫ ω, ((ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal) ^ 2 ∂P) =
      (m A).toReal ^ 2 + (m A).toReal := by
  have hE : ∀ ω, (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂
      (poissonRandomMeasure K Y ω)) =
      (poissonRandomMeasure K Y ω A).toReal :=
    fun ω => integral_indicator_one hA
  calc
    (∫ ω, ((poissonRandomMeasure K Y ω A).toReal) ^ 2 ∂P) =
        (∫ ω, (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂
          (poissonRandomMeasure K Y ω)) ^ 2 ∂P) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω =>
        congrArg (fun z : ℝ => z ^ 2) (hE ω).symm
    _ = _ :=
      Kyprianou.ProofPreparation.poisson_prm_indicator_integral_second_moment
        P m K Y hd A hA hfin
