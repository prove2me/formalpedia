-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.ratFunc_euler_constant_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:56:39.370658+00:00
-- url     : https://prove2.me/submissions/edc83ff5-fd88-41c4-a501-073a23879c35

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Derivation.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eulerDerivation_exists
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eulerDerivation_nonzero_constant_obstruction

open RatFunc

theorem solution
    (K : Type) [Field K] [CharZero K] :
    ∃ d : Derivation K (RatFunc K) (RatFunc K),
      d RatFunc.X = RatFunc.X ∧
      ∀ (r : RatFunc K) (c : K), c ≠ 0 →
        d r ≠ algebraMap K (RatFunc K) c := by
  obtain ⟨d, hdX⟩ :=
    OAI.PiExponent.FormalInterpolation.eulerDerivation_exists K
  exact ⟨d, hdX,
    OAI.PiExponent.FormalInterpolation.eulerDerivation_nonzero_constant_obstruction
      K d hdX⟩