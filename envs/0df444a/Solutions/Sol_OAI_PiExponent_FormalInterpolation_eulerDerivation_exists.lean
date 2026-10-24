-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eulerDerivation_exists
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T05:01:56.118872+00:00
-- url     : https://prove2.me/submissions/e721abb3-e123-4f02-a5dc-c9d8244c3ba2

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Derivation
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_derivation_extendRatFunc

open RatFunc

theorem solution
    (K : Type) [Field K] [CharZero K] :
    ∃ d : Derivation K (RatFunc K) (RatFunc K),
      d RatFunc.X = RatFunc.X := by
  obtain ⟨d, hd⟩ :=
    OAI.PiExponent.FormalInterpolation.derivation_extendRatFunc
      (K := K) (Polynomial.mkDerivation K (RatFunc.X))
  refine ⟨d, ?_⟩
  simpa only [RatFunc.algebraMap_X, Polynomial.mkDerivation_X] using hd Polynomial.X