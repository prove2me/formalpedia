-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_explicit_representation_extract
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:20:23.650842+00:00
-- url     : https://prove2.me/submissions/41222762-10fe-4213-9e49-bdc56e4e05d7

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_component_mul_homogeneous

open scoped BigOperators

theorem solution
    {d k : Nat} (w : Fin d → Rat)
    (D E : Real) (g : Fin k → MvPolynomial (Fin d) Complex)
    (f : MvPolynomial (Fin d) Complex)
    (a : Fin k → MvPolynomial (Fin d) Complex)
    (hhom : ∀ j, (g j).IsWeightedHomogeneous (fun i => (w i : Real)) D)
    (hf : f.IsWeightedHomogeneous (fun i => (w i : Real)) E)
    (hrep : f = ∑ j : Fin k, a j * g j) :
    ∃ c : Fin k → MvPolynomial (Fin d) Complex,
      f = ∑ j : Fin k, c j * g j ∧
      ∀ j, (c j).IsWeightedHomogeneous (fun i => (w i : Real)) (E - D) := by
  classical
  let c : Fin k → MvPolynomial (Fin d) Complex :=
    fun j => MvPolynomial.weightedHomogeneousComponent
      (fun i => (w i : Real)) (E - D) (a j)
  refine ⟨c, ?_, ?_⟩
  · calc
      f = MvPolynomial.weightedHomogeneousComponent
          (fun i => (w i : Real)) E f :=
        (hf.weightedHomogeneousComponent_same).symm
      _ = ∑ j : Fin k,
          MvPolynomial.weightedHomogeneousComponent
            (fun i => (w i : Real)) E (a j * g j) := by
        rw [hrep, map_sum]
      _ = ∑ j : Fin k, c j * g j := by
        apply Finset.sum_congr rfl
        intro j hj
        exact OAI.PiExponent.FormalInterpolation.weighted_component_mul_homogeneous
          w D E (a j) (g j) (hhom j)
  · intro j
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (w := fun i => (w i : Real)) (n := E - D) (φ := a j)
