-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.derivation_extendRatFunc
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T05:10:33.405632+00:00
-- url     : https://prove2.me/submissions/6d25c4b3-09a0-4c42-967b-370bbaefb558

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Derivation
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_derivation_ratFuncFormalDerivative

open RatFunc

theorem solution
    (K : Type) [Field K]
    (D : Derivation K (Polynomial K) (RatFunc K)) :
    ∃ d : Derivation K (RatFunc K) (RatFunc K),
      ∀ p : Polynomial K,
        d (algebraMap (Polynomial K) (RatFunc K) p) = D p := by
  obtain ⟨δ, hδ⟩ := OAI.PiExponent.FormalInterpolation.derivation_ratFuncFormalDerivative K
  refine ⟨(D Polynomial.X) • δ, ?_⟩
  intro p
  rw [Derivation.smul_apply, hδ p]
  simpa [RatFunc.aeval_X_left_eq_algebraMap, Algebra.smul_def, mul_comm] using
    (D.map_aeval p (Polynomial.X : Polynomial K)).symm