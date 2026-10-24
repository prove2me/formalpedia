-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_homogeneous_support_weight
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:40:34.2491+00:00
-- url     : https://prove2.me/submissions/2d8be2c3-f131-4ae0-b965-fe26e0dd1c77

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

theorem solution
    {d : Nat} (w : Fin d → ℚ) (f : MvPolynomial (Fin d) ℂ) (t : ℚ)
    (hhom : MvPolynomial.IsWeightedHomogeneous w f t)
    (e : Fin d →₀ Nat) (he : e ∈ f.support) :
    Finsupp.weight w e = t := by
  exact hhom (Finsupp.mem_support_iff.mp he)