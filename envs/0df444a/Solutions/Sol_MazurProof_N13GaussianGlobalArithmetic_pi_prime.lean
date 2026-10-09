-- Prove2me | solution 1 for MazurProof.N13GaussianGlobalArithmetic.pi_prime
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T04:32:41.974627+00:00
-- url     : https://prove2.me/submissions/ad71b2fb-e19e-4afd-ae0a-892ddf12b018

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13GaussianGlobalArithmetic =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianGlobalArithmetic =====
section
/-!
# The Gaussian cubic at the ramified prime over 13

This file freezes the global Gaussian arithmetic attached to the actual N13
sextic

`X⁶ + 4X⁵ + 6X⁴ + 2X³ + X² + 2X + 1`.

Over `ℤ[i]` it is the product of a cubic and its conjugate.  The cubic has
discriminant `(3-2i)²`; after translating its root by `9`, it is Eisenstein at
the prime element `3-2i`.  Primality is proved from the Gaussian norm `13`,
and the Eisenstein constant-term test is the single norm nondivisibility
`13 ∤ 62197`.  No class-group computation or factor table is used.
-/
open Polynomial
namespace MazurProof.N13GaussianGlobalArithmetic
noncomputable section
/-- An element of Gaussian prime norm is irreducible.  Here the only fixed
arithmetic input is primality of `13`. -/
theorem pi_irreducible : Irreducible pi := by
  rw [irreducible_iff]
  constructor
  · intro hunit
    have hnorm : (Zsqrtd.norm pi).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr hunit
    rw [pi_norm] at hnorm
    norm_num at hnorm
  · intro a b hab
    have hnorm :
        (Zsqrtd.norm pi).natAbs =
          (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs := by
      simpa [Zsqrtd.norm_mul, Int.natAbs_mul] using
        congrArg (fun z : GI => (Zsqrtd.norm z).natAbs) hab
    rw [pi_norm] at hnorm
    have hp13 : Nat.Prime 13 := by
      decide
    rcases hp13.eq_one_or_self_of_dvd
        (Zsqrtd.norm a).natAbs
        ⟨(Zsqrtd.norm b).natAbs, hnorm⟩ with ha | ha
    · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp ha)
    · right
      apply Zsqrtd.norm_eq_one_iff.mp
      norm_num at hnorm
      rw [ha] at hnorm
      omega
theorem pi_prime : Prime pi :=
  irreducible_iff_prime.mp pi_irreducible
end
end MazurProof.N13GaussianGlobalArithmetic
end

end

theorem solution : type_of% @MazurProof.N13GaussianGlobalArithmetic.pi_prime := @MazurProof.N13GaussianGlobalArithmetic.pi_prime
