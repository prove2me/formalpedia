-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_finset_weighted_count_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:57:13.052337+00:00
-- url     : https://prove2.me/submissions/b9525eed-4e9a-4838-8fa3-0c8fdcff0b6e

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_pair_count_product_integrable
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_count_pair_moment_kernel
import Theorems.Thm_Kyprianou_ProofPreparation_real_finset_weighted_square_integral
import Theorems.Thm_Kyprianou_ProofPreparation_real_finset_poisson_pair_moment_algebra
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Finite disjoint Poisson count sums have variance equal to the intensity sum of squares. -/
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
    (∫ ω, (∑ i ∈ F, a i *
      (ProbabilityTheory.poissonRandomMeasure K Y ω (A i)).toReal) ^ 2 ∂P) =
      (∑ i ∈ F, a i * (m (A i)).toReal) ^ 2 +
        ∑ i ∈ F, (a i) ^ 2 * (m (A i)).toReal := by
  let X : ι → Ω → ℝ := fun i ω =>
    (poissonRandomMeasure K Y ω (A i)).toReal
  let r : ι → ℝ := fun i => (m (A i)).toReal
  have hprod : ∀ i ∈ F, ∀ j ∈ F,
      Integrable (fun ω => X i ω * X j ω) P := by
    intro i hi j hj
    exact Kyprianou.ProofPreparation.poisson_prm_pair_count_product_integrable
      P m K Y hd A i j (hA i hi) (hA j hj)
        (hfin i hi) (hfin j hj) (hdisj i hi j hj)
  have hpair : ∀ i ∈ F, ∀ j ∈ F,
      (∫ ω, X i ω * X j ω ∂P) =
        r i * r j + if i = j then r i else 0 := by
    intro i hi j hj
    exact Kyprianou.ProofPreparation.poisson_prm_count_pair_moment_kernel
      P m K Y hd A i j (hA i hi) (hA j hj)
        (hfin i hi) (hfin j hj) (hdisj i hi j hj)
  change (∫ ω, (∑ i ∈ F, a i * X i ω) ^ 2 ∂P) =
      (∑ i ∈ F, a i * r i) ^ 2 + ∑ i ∈ F, a i ^ 2 * r i
  calc
    (∫ ω, (∑ i ∈ F, a i * X i ω) ^ 2 ∂P) =
        ∑ i ∈ F, ∑ j ∈ F, (a i * a j) *
          (∫ ω, X i ω * X j ω ∂P) :=
      Kyprianou.ProofPreparation.real_finset_weighted_square_integral
        P F X a hprod
    _ = ∑ i ∈ F, ∑ j ∈ F,
        (a i * a j) * (r i * r j + if i = j then r i else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hpair i hi j hj]
    _ = (∑ i ∈ F, a i * r i) ^ 2 +
        ∑ i ∈ F, a i ^ 2 * r i :=
      Kyprianou.ProofPreparation.real_finset_poisson_pair_moment_algebra F a r
