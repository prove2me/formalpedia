-- Prove2me | solution 1 for GlobalTheory.SqZeroPow.dual_inl_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:57:17.072927+00:00
-- url     : https://prove2.me/submissions/99d81fbc-71cf-4e84-8d61-a7999294da40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsRingSqZeroNilpotentAugmented

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.SqZeroPow
namespace GlobalTheory.SqZeroPow
theorem _root_.solution {R : Type} [CommRing R] (r : R) (n : ℕ) (h : r ^ n = 0) :
    (TrivSqZeroExt.inl r : DualNumber R) ^ n = 0 := by
  rw [TrivSqZeroExt.inl_pow, h, TrivSqZeroExt.inl_zero]
end GlobalTheory.SqZeroPow
