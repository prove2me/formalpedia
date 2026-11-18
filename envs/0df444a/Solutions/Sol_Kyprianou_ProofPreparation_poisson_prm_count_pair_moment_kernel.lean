-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_count_pair_moment_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:33:30.136184+00:00
-- url     : https://prove2.me/submissions/34442052-5c86-4762-a056-775482c841e3

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_real_second_moment
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_disjoint_cross_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every pair of disjoint-region Poisson counts has the diagonal intensity correction. -/
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
    (∫ ω, (ProbabilityTheory.poissonRandomMeasure K Y ω (A i)).toReal *
      (ProbabilityTheory.poissonRandomMeasure K Y ω (A j)).toReal ∂P) =
      (m (A i)).toReal * (m (A j)).toReal +
        if i = j then (m (A i)).toReal else 0 := by
  by_cases hij : i = j
  · subst j
    have hm := Kyprianou.ProofPreparation.poisson_prm_eval_real_second_moment
      P m K Y hd (A i) hi hfi
    simpa [pow_two] using hm
  · have hc := Kyprianou.ProofPreparation.poisson_prm_disjoint_cross_moment
      P m K Y hd (A i) (A j) hi hj hfi hfj (hdisj hij)
    simpa [hij] using hc
