-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.sum_truncation_errors_in_ideal_power
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:21:56.860555+00:00
-- url     : https://prove2.me/submissions/3cf5a3be-1085-456c-b34f-f39f05855780

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d m t : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (n : Nat) (g : Fin m → MvPolynomial (Fin d) Complex)
    (b : Fin t → MvPolynomial (Fin d) Complex)
    (F G : Fin t → MvPolynomial (Fin m) Complex)
    (hFG : ∀ i, MvPolynomial.aeval g (F i - G i) ∈ I ^ n) :
    (∑ i : Fin t, MvPolynomial.aeval g (F i) * b i) -
      (∑ i : Fin t, MvPolynomial.aeval g (G i) * b i) ∈ I ^ n := by
  classical
  rw [← Finset.sum_sub_distrib]
  apply (I ^ n).sum_mem
  intro i hi
  rw [← sub_mul, ← map_sub]
  exact (I ^ n).mul_mem_right _ (hFG i)