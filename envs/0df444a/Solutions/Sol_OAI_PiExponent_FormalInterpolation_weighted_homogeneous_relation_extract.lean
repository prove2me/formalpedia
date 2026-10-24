-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_homogeneous_relation_extract
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:07:05.70597+00:00
-- url     : https://prove2.me/submissions/8d9b30ea-4e59-4eb5-9a6f-9b2ee0bb551f

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_component_mul_for_relation_extract

open scoped BigOperators

theorem solution
    {d m : Nat} (w : Fin d -> ℚ) (D N : ℚ)
    (p : Fin m -> MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) D)
    (F : MvPolynomial (Fin d) ℂ)
    (hF : MvPolynomial.IsWeightedHomogeneous w F N)
    (q : Fin m -> MvPolynomial (Fin d) ℂ)
    (hrel : F = ∑ j, q j * p j) :
    ∃ q' : Fin m -> MvPolynomial (Fin d) ℂ,
      F = ∑ j, q' j * p j ∧
      ∀ j, MvPolynomial.IsWeightedHomogeneous w (q' j) (N - D) := by
  classical
  let q' : Fin m -> MvPolynomial (Fin d) ℂ :=
    fun j => MvPolynomial.weightedHomogeneousComponent w (N - D) (q j)
  refine ⟨q', ?_, ?_⟩
  · have hproj : MvPolynomial.weightedHomogeneousComponent w N F =
        ∑ j, q' j * p j := by
      rw [hrel]
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact OAI.PiExponent.FormalInterpolation.weighted_component_mul_for_relation_extract
        w D N (q j) (p j) (hp j)
    rw [← MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same hF]
    exact hproj
  · intro j
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (N - D) (q j)
