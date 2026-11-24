-- Prove2me | solution 1 for GlobalTheory.SqZeroPow.dual_fst_of_eps_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:57:16.318975+00:00
-- url     : https://prove2.me/submissions/449a0df8-4ce3-4059-b91b-2d6be3ffcd6f

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
theorem _root_.solution {R : Type} [CommRing R] (f : DualNumber R) (r : R) (n : ℕ)
    (h : (DualNumber.eps : DualNumber R) * (TrivSqZeroExt.inl r) ^ n * f = 0) :
    r ^ n * f.fst = 0 := by
  have hs := congrArg TrivSqZeroExt.snd h
  simpa [mul_comm] using hs
end GlobalTheory.SqZeroPow
