-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_finset_simple_integral_centered_isometry
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T15:13:10.811201+00:00
-- url     : https://prove2.me/submissions/303b841c-34de-4efd-b1fd-dc67dc1e64b8

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_integral_ae_eq
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_count_centered_isometry
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

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
    (∫ ω, ((∫ x, (∑ i ∈ F, a i *
      (A i).indicator (fun _ => (1 : ℝ)) x) ∂
      (ProbabilityTheory.poissonRandomMeasure K Y ω)) -
        ∑ i ∈ F, a i * (m (A i)).toReal) ^ 2 ∂P) =
      ∑ i ∈ F, a i ^ 2 * (m (A i)).toReal := by
  rw [← Kyprianou.ProofPreparation.poisson_prm_finset_count_centered_isometry P m K Y hd F A a
    hA hfin hdisj]
  refine integral_congr_ae ?_
  filter_upwards [Kyprianou.ProofPreparation.poisson_prm_finset_integral_ae_eq P m K Y hd F A a
    hA hfin] with ω hω
  rw [hω]
