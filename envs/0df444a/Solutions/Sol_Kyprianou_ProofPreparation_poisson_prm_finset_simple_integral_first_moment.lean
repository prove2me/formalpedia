-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_finset_simple_integral_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:39:27.114247+00:00
-- url     : https://prove2.me/submissions/fa9f1ab6-3445-42c7-b51f-7c2c67b5a86f

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_integral_ae_eq
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_weighted_count_first_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The finite signed simple Poisson integral satisfies the Campbell formula. -/
theorem solution
    {Ω E ι : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [DecidableEq ι] [Nonempty E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (F : Finset ι) (A : ι → Set E) (a : ι → ℝ)
    (hA : ∀ i ∈ F, MeasurableSet (A i))
    (hfin : ∀ i ∈ F, m (A i) < ⊤) :
    (∫ ω, (∫ x, (∑ i ∈ F, a i *
      (A i).indicator (fun _ => (1 : ℝ)) x) ∂
        (ProbabilityTheory.poissonRandomMeasure K Y ω)) ∂P) =
      ∑ i ∈ F, a i * (m (A i)).toReal := by
  have hAE := Kyprianou.ProofPreparation.poisson_prm_finset_integral_ae_eq
    P m K Y hd F A a hA hfin
  calc
    (∫ ω, (∫ x, (∑ i ∈ F, a i *
      (A i).indicator (fun _ => (1 : ℝ)) x) ∂
        (poissonRandomMeasure K Y ω)) ∂P) =
        ∫ ω, ∑ i ∈ F, a i *
          (poissonRandomMeasure K Y ω (A i)).toReal ∂P := by
      exact integral_congr_ae hAE
    _ = _ := Kyprianou.ProofPreparation.poisson_prm_finset_weighted_count_first_moment
      P m K Y hd F A a hA hfin
