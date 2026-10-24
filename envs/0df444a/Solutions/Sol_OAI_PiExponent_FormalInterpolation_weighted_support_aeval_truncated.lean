-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_support_aeval_truncated
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T10:03:37.824358+00:00
-- url     : https://prove2.me/submissions/78b2f6b6-41c4-4462-8c65-2855ec183ea1

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_aeval_in_monomial_products
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_monomial_product_weight
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_cutoff_arithmetic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d m : Nat} (w : Fin d → Rat) (rho : Rat) (eps : Real)
    (s : Nat) (hs : 0 < s) (D : Nat)
    (hD : (D : Real) < (s : Real) * ((rho : Real) + eps))
    (g : Fin m → MvPolynomial (Fin d) Complex)
    (hdeg : ∀ j, ∀ a ∈ (g j).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real))
    (f : MvPolynomial (Fin m) Complex) (n : Nat)
    (hcut : ∀ u ∈ f.support, s * (∑ j, u j) < n) :
    ∀ a ∈ (MvPolynomial.aeval g f).support,
      ∑ k, (w k : Real) * (a k : Real) ≤
        (n : Real) * ((rho : Real) + eps) := by
  intro a ha
  obtain ⟨u, hu, hproduct⟩ :=
    OAI.PiExponent.FormalInterpolation.support_aeval_in_monomial_products
      g f a ha
  have hmon :=
    OAI.PiExponent.FormalInterpolation.support_monomial_product_weight
      w D g hdeg u a hproduct
  exact OAI.PiExponent.FormalInterpolation.weighted_cutoff_arithmetic
    w rho eps s D n hs hD u (hcut u hu) a hmon