-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_degree_of_truncated_generator_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:53:48.728838+00:00
-- url     : https://prove2.me/submissions/e9f23458-9534-4169-b6ac-b07abeed8161

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_support_aeval_truncated
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_support_sum_mul_of_support_bounds

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d m t : Nat} (w : Fin d → Rat) (rho : Rat) (eps : Real)
    (s : Nat) (hs : 0 < s) (D : Nat)
    (hD : (D : Real) < (s : Real) * ((rho : Real) + eps))
    (g : Fin m → MvPolynomial (Fin d) Complex)
    (hdeg : ∀ j, ∀ a ∈ (g j).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real))
    (b : Fin t → MvPolynomial (Fin d) Complex)
    (C : Real) (hb : ∀ i, ∀ a ∈ (b i).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ C)
    (n : Nat) (F G : Fin t → MvPolynomial (Fin m) Complex)
    (hG : ∀ i, ∀ u ∈ (G i).support, s * (∑ j, u j) < n) :
    ∀ a ∈ (∑ i : Fin t, MvPolynomial.aeval g (G i) * b i).support,
      ∑ k, (w k : Real) * (a k : Real) ≤
        (n : Real) * ((rho : Real) + eps) + C := by
  apply OAI.PiExponent.FormalInterpolation.weighted_support_sum_mul_of_support_bounds
    w (fun i => MvPolynomial.aeval g (G i)) b
    ((n : Real) * ((rho : Real) + eps)) C
  · intro i a ha
    exact OAI.PiExponent.FormalInterpolation.weighted_support_aeval_truncated
      w rho eps s hs D hD g hdeg (G i) n (hG i) a ha
  · exact hb