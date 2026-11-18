-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_finset_counts_ae_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:22:43.19404+00:00
-- url     : https://prove2.me/submissions/4f164756-378d-45cb-9f37-dfe4a202c614

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every count in a finite list of finite-intensity sets is a.s. finite. -/
theorem solution
    {Ω E ι : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (F : Finset ι) (A : ι → Set E)
    (hA : ∀ i ∈ F, MeasurableSet (A i))
    (hfin : ∀ i ∈ F, m (A i) < ⊤) :
    ∀ᵐ ω ∂P, ∀ i ∈ F,
      ProbabilityTheory.poissonRandomMeasure K Y ω (A i) < ⊤ := by
  apply (Filter.eventually_all_finset F).2
  intro i hi
  exact ae_poissonRandomMeasure_apply_lt_top hd (hA i hi) (hfin i hi)
