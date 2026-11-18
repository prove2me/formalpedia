-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_finset_simple_integral_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T13:02:45.818936+00:00
-- url     : https://prove2.me/submissions/1a137e1a-ce97-4694-91ec-74281d48fa77

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_integral_ae_eq
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_weighted_count_second_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The actual Poisson integral of a finite disjoint simple function has the exact L2 moment. -/
theorem solution
    {Ω E ι : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [DecidableEq ι] [Nonempty E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (F : Finset ι) (A : ι → Set E) (a : ι → ℝ)
    (hA : ∀ i ∈ F, MeasurableSet (A i))
    (hfin : ∀ i ∈ F, m (A i) < ⊤)
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (A i) (A j)) :
    (∫ ω, (∫ x, (∑ i ∈ F, a i *
      (A i).indicator (fun _ => (1 : ℝ)) x) ∂
      (ProbabilityTheory.poissonRandomMeasure K Y ω)) ^ 2 ∂P) =
      (∑ i ∈ F, a i * (m (A i)).toReal) ^ 2 +
      ∑ i ∈ F, (a i) ^ 2 * (m (A i)).toReal := by
  have hAE := Kyprianou.ProofPreparation.poisson_prm_finset_integral_ae_eq
    P m K Y hd F A a hA hfin
  calc
    (∫ ω, (∫ x, (∑ i ∈ F, a i *
      (A i).indicator (fun _ => (1 : ℝ)) x) ∂
      (poissonRandomMeasure K Y ω)) ^ 2 ∂P) =
        (∫ ω, (∑ i ∈ F, a i *
          (poissonRandomMeasure K Y ω (A i)).toReal) ^ 2 ∂P) := by
      apply integral_congr_ae
      filter_upwards [hAE] with ω hω
      rw [hω]
    _ = _ :=
      Kyprianou.ProofPreparation.poisson_prm_finset_weighted_count_second_moment
        P m K Y hd F A a hA hfin hdisj
