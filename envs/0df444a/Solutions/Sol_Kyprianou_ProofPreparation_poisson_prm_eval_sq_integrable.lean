-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_eval_sq_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:14:11.655941+00:00
-- url     : https://prove2.me/submissions/1924f913-feb3-4b85-85fc-fa0f3f1fd324

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_lintegral_sq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The finite Poisson count-square mean gives real square integrability. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A : Set E) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    Integrable (fun ω =>
      ((ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal) ^ 2) P := by
  have hZ : Measurable (fun ω => (poissonRandomMeasure K Y ω A).toReal) :=
    ENNReal.measurable_toReal.comp
      (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA)
  refine ⟨(hZ.pow_const 2).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun ω =>
      sq_nonneg ((poissonRandomMeasure K Y ω A).toReal))).2
  rw [Kyprianou.ProofPreparation.poisson_prm_eval_lintegral_sq
    P m K Y hd A hA hfin]
  exact ENNReal.ofReal_lt_top
