-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_finset_count_centered_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T13:24:28.612828+00:00
-- url     : https://prove2.me/submissions/69c4b813-e382-4484-8a0f-c96bcac453c5

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_pair_count_product_integrable
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_real_first_moment
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_weighted_count_first_moment
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_weighted_count_second_moment
import Theorems.Thm_Kyprianou_ProofPreparation_real_finset_weighted_square_integrable
import Theorems.Thm_Kyprianou_ProofPreparation_real_centered_square_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The finite disjoint Poisson count sum has exact centred squared moment. -/
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
    (∫ ω, ((∑ i ∈ F, a i *
      (ProbabilityTheory.poissonRandomMeasure K Y ω (A i)).toReal) -
      ∑ i ∈ F, a i * (m (A i)).toReal) ^ 2 ∂P) =
      ∑ i ∈ F, a i ^ 2 * (m (A i)).toReal := by
  let Z : ι → Ω → ℝ := fun i ω =>
    (poissonRandomMeasure K Y ω (A i)).toReal
  let J : Ω → ℝ := fun ω => ∑ i ∈ F, a i * Z i ω
  let c : ℝ := ∑ i ∈ F, a i * (m (A i)).toReal
  have hp : ∀ i ∈ F, ∀ j ∈ F,
      Integrable (fun ω => Z i ω * Z j ω) P := by
    intro i hi j hj
    exact Kyprianou.ProofPreparation.poisson_prm_pair_count_product_integrable
      P m K Y hd A i j (hA i hi) (hA j hj)
        (hfin i hi) (hfin j hj) (hdisj i hi j hj)
  have hJ2 : Integrable (fun ω => J ω ^ 2) P :=
    Kyprianou.ProofPreparation.real_finset_weighted_square_integrable
      P F Z a hp
  have hJ : Integrable J P := by
    apply integrable_finset_sum F
    intro i hi
    exact ((Kyprianou.ProofPreparation.poisson_prm_eval_real_first_moment
      P m K Y hd (A i) (hA i hi) (hfin i hi)).1).const_mul (a i)
  have hm : (∫ ω, J ω ∂P) = c :=
    Kyprianou.ProofPreparation.poisson_prm_finset_weighted_count_first_moment
      P m K Y hd F A a hA hfin
  have h2 : (∫ ω, J ω ^ 2 ∂P) =
      c ^ 2 + ∑ i ∈ F, a i ^ 2 * (m (A i)).toReal :=
    Kyprianou.ProofPreparation.poisson_prm_finset_weighted_count_second_moment
      P m K Y hd F A a hA hfin hdisj
  change (∫ ω, (J ω - c) ^ 2 ∂P) =
    ∑ i ∈ F, a i ^ 2 * (m (A i)).toReal
  calc
    (∫ ω, (J ω - c) ^ 2 ∂P) =
        (∫ ω, J ω ^ 2 ∂P) -
          (2 * c) * (∫ ω, J ω ∂P) + c ^ 2 :=
      Kyprianou.ProofPreparation.real_centered_square_integral
        P J c hJ hJ2
    _ = ∑ i ∈ F, a i ^ 2 * (m (A i)).toReal := by
      rw [hm, h2]
      ring
