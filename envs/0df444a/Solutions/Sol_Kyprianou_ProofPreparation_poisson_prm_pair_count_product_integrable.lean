-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_pair_count_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:29:39.16784+00:00
-- url     : https://prove2.me/submissions/1f09cd2a-5ef9-4f48-9c11-34b45b7fba84

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_sq_integrable
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_real_first_moment
import Theorems.Thm_ProbabilityTheory_indepFun_poissonRandomMeasure_apply
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The product of two Poisson region counts is integrable. -/
theorem solution
    {Ω E ι : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [DecidableEq ι] [Nonempty E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A : ι → Set E) (i j : ι)
    (hi : MeasurableSet (A i)) (hj : MeasurableSet (A j))
    (hfi : m (A i) < ⊤) (hfj : m (A j) < ⊤)
    (hdisj : i ≠ j → Disjoint (A i) (A j)) :
    Integrable (fun ω =>
      (ProbabilityTheory.poissonRandomMeasure K Y ω (A i)).toReal *
      (ProbabilityTheory.poissonRandomMeasure K Y ω (A j)).toReal) P := by
  by_cases hij : i = j
  · subst j
    simpa only [pow_two] using
      (Kyprianou.ProofPreparation.poisson_prm_eval_sq_integrable
        P m K Y hd (A i) hi hfi)
  · have hind : IndepFun
        (fun ω => (poissonRandomMeasure K Y ω (A i)).toReal)
        (fun ω => (poissonRandomMeasure K Y ω (A j)).toReal) P :=
      (indepFun_poissonRandomMeasure_apply hd hi hj hfi hfj (hdisj hij)).comp
        ENNReal.measurable_toReal ENNReal.measurable_toReal
    have hia := (Kyprianou.ProofPreparation.poisson_prm_eval_real_first_moment
      P m K Y hd (A i) hi hfi).1
    have hib := (Kyprianou.ProofPreparation.poisson_prm_eval_real_first_moment
      P m K Y hd (A j) hj hfj).1
    exact hind.integrable_mul hia hib
