-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.high_weight_terms_in_coordinate_power_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:35:54.863335+00:00
-- url     : https://prove2.me/submissions/84fabec1-da66-40cf-92d2-c940b6ca3a26

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_high_weight_monomial_in_ideal
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_homogeneous_support_weight
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_monomials_in_ideal

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (n : Fin d → Nat) (hn : ∀ i, 0 < n i)
    (I : Ideal (MvPolynomial (Fin d) ℂ))
    (hpow : ∀ i : Fin d,
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n i ∈ I) :
    ∀ (t : ℚ) (f : MvPolynomial (Fin d) ℂ),
      (∑ i : Fin d, ((n i : ℚ) - 1) * w i) < t →
      MvPolynomial.IsWeightedHomogeneous w f t → f ∈ I := by
  intro t f hcut hhom
  apply OAI.PiExponent.FormalInterpolation.support_monomials_in_ideal I f
  intro e he
  have hweight :
      Finsupp.weight w e = t :=
    OAI.PiExponent.FormalInterpolation.weighted_homogeneous_support_weight
      w f t hhom e he
  apply OAI.PiExponent.FormalInterpolation.high_weight_monomial_in_ideal
    w hw n hn I hpow t e (f.coeff e)
  simpa [hweight] using hcut