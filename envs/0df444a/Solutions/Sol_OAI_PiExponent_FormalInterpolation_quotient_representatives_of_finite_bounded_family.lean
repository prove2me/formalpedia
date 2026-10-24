-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.quotient_representatives_of_finite_bounded_family
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:44:11.621047+00:00
-- url     : https://prove2.me/submissions/6e90d73b-f0b1-40f4-bf13-54e013ca2097
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_polynomial_representations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncate_polynomial_representations

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (rho : Rat) (eps : Real)
    (s : Nat) (hs : 0 < s) (D : Nat)
    (hD : (D : Real) < (s : Real) * ((rho : Real) + eps))
    (m : Nat) (g : Fin m → MvPolynomial (Fin d) Complex)
    (hg : ∀ j, g j ∈ I ^ s)
    (hdeg : ∀ j, ∀ a ∈ (g j).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real))
    (hmod : Module.Finite (Algebra.adjoin Complex (Set.range g))
      (MvPolynomial (Fin d) Complex)) :
    ∃ C : Real, 0 ≤ C ∧ ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ q : MvPolynomial (Fin d) Complex, ∃ p : MvPolynomial (Fin d) Complex,
        q - p ∈ I ^ n ∧
        ∀ a ∈ p.support,
          ∑ k, (w k : Real) * (a k : Real) ≤
            (n : Real) * ((rho : Real) + eps) + C := by
  have hrepr :=
    OAI.PiExponent.FormalInterpolation.finite_adjoin_polynomial_representations
      (g := g) hmod
  exact OAI.PiExponent.FormalInterpolation.truncate_polynomial_representations
    (I := I) (w := w) (rho := rho) (eps := eps) (s := s) (hs := hs)
    (D := D) (hD := hD) (m := m) (g := g) (hg := hg) (hdeg := hdeg)
    hrepr
