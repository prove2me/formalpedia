-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncate_one_polynomial_mod_power
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:20:22.384848+00:00
-- url     : https://prove2.me/submissions/a2545001-8cf5-44b5-ae85-e3365b5837d2

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncate_polynomial_support_decomposition
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bad_monomial_mem_power

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d m : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (s n : Nat) (hs : 0 < s) (hn : 0 < n)
    (g : Fin m → MvPolynomial (Fin d) Complex)
    (hg : ∀ j, g j ∈ I ^ s)
    (F : MvPolynomial (Fin m) Complex) :
    ∃ G : MvPolynomial (Fin m) Complex,
      (∀ u ∈ G.support, s * (∑ j : Fin m, u j) < n) ∧
      MvPolynomial.aeval g (F - G) ∈ I ^ n := by
  obtain ⟨G, hG, hdecomp⟩ :=
    OAI.PiExponent.FormalInterpolation.truncate_polynomial_support_decomposition s n F
  refine ⟨G, hG, ?_⟩
  rw [hdecomp, MvPolynomial.aeval_sum]
  exact (I ^ n).sum_mem fun u hu => by
    rcases Finset.mem_filter.mp hu with ⟨_, hbad⟩
    exact OAI.PiExponent.FormalInterpolation.bad_monomial_mem_power
      I s n g hg u (Nat.le_of_not_gt hbad) (F.coeff u)