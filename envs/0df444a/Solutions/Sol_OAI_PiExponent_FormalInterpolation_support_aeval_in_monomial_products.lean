-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.support_aeval_in_monomial_products
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:51:59.707894+00:00
-- url     : https://prove2.me/submissions/6ada6e2f-84a2-4049-bae3-3fbe767eea04

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d m : Nat} (g : Fin m → MvPolynomial (Fin d) Complex)
    (f : MvPolynomial (Fin m) Complex) (a : Fin d →₀ Nat)
    (ha : a ∈ (MvPolynomial.aeval g f).support) :
    ∃ u ∈ f.support, a ∈ (∏ j : Fin m, (g j) ^ (u j)).support := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq'] at ha
  rw [MvPolynomial.mem_support_iff] at ha
  have ha' :
      (∑ u ∈ f.support,
        MvPolynomial.coeff a
          ((algebraMap Complex (MvPolynomial (Fin d) Complex) (f.coeff u)) *
            ∏ j : Fin m, g j ^ u j)) ≠ 0 := by
    simpa only [MvPolynomial.coeff_sum] using ha
  have hex : ∃ u ∈ f.support,
      MvPolynomial.coeff a
        ((algebraMap Complex (MvPolynomial (Fin d) Complex) (f.coeff u)) *
          ∏ j : Fin m, g j ^ u j) ≠ 0 := by
    by_contra h
    push_neg at h
    apply ha'
    rw [Finset.sum_eq_zero]
    intro u hu
    exact h u hu
  obtain ⟨u, hu, hcoeff⟩ := hex
  refine ⟨u, hu, ?_⟩
  rw [MvPolynomial.mem_support_iff]
  by_contra hzero
  apply hcoeff
  simp [MvPolynomial.coeff_C_mul, hzero]
