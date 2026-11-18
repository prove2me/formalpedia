-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_finset_weighted_count_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:22:38.755228+00:00
-- url     : https://prove2.me/submissions/2f4e98a5-9803-4c66-abd6-c6fdd0e2a535

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_real_first_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Linearity of expectation for finitely many real weighted PRM region counts. -/
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
    (∫ ω, ∑ i ∈ F, a i *
      (ProbabilityTheory.poissonRandomMeasure K Y ω (A i)).toReal ∂P) =
      ∑ i ∈ F, a i * (m (A i)).toReal := by
  have hint : ∀ i ∈ F, Integrable
      (fun ω => a i * (poissonRandomMeasure K Y ω (A i)).toReal) P := by
    intro i hi
    exact ((Kyprianou.ProofPreparation.poisson_prm_eval_real_first_moment
      P m K Y hd (A i) (hA i hi) (hfin i hi)).1).const_mul (a i)
  calc
    (∫ ω, ∑ i ∈ F, a i * (poissonRandomMeasure K Y ω (A i)).toReal ∂P) =
        ∑ i ∈ F, (∫ ω, a i * (poissonRandomMeasure K Y ω (A i)).toReal ∂P) :=
      integral_finset_sum F hint
    _ = ∑ i ∈ F, a i * (m (A i)).toReal := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul,
        (Kyprianou.ProofPreparation.poisson_prm_eval_real_first_moment
          P m K Y hd (A i) (hA i hi) (hfin i hi)).2]
