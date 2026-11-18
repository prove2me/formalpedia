-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_eval_real_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:21:52.079489+00:00
-- url     : https://prove2.me/submissions/1086b99c-ff83-4753-9bd0-aed66bc60d39

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_Ch02_nonnegativePoissonIntegralFirstMoment
import Theorems.Thm_Kyprianou_Ch02_nonnegativePoissonIntegralOuterIntegrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The public nonnegative Campbell formula gives the count mean and integrability. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A : Set E) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    Integrable (fun ω => (ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal) P ∧
    (∫ ω, (ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal ∂P) =
      (m A).toReal := by
  let f : E → ℝ := A.indicator (fun _ => (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator hA
  have hfn : ∀ x, 0 ≤ f x := by
    intro x
    by_cases hx : x ∈ A
    · simp [f, Set.indicator_of_mem hx]
    · simp [f, Set.indicator_of_notMem hx]
  have hfi : Integrable f m :=
    (integrableOn_const hfin.ne).integrable_indicator hA
  have houter := Kyprianou.Ch02.nonnegativePoissonIntegralOuterIntegrable
    P m K Y hd f hf hfn hfi
  have hmean := Kyprianou.Ch02.nonnegativePoissonIntegralFirstMoment
    P m K Y hd f hf hfn hfi
  constructor
  · convert houter using 1
    funext ω
    exact (integral_indicator_one hA).symm
  · calc
      (∫ ω, (poissonRandomMeasure K Y ω A).toReal ∂P) =
          ∫ ω, (∫ x, f x ∂(poissonRandomMeasure K Y ω)) ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω =>
          (integral_indicator_one (μ := poissonRandomMeasure K Y ω) hA).symm
      _ = ∫ x, f x ∂m := hmean.2
      _ = (m A).toReal := integral_indicator_one (μ := m) hA
