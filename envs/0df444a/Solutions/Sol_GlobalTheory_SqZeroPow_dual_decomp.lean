-- Prove2me | solution 1 for GlobalTheory.SqZeroPow.dual_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:57:15.354593+00:00
-- url     : https://prove2.me/submissions/ec58bb6c-dd5e-4bd1-922c-b4de604af929

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
theorem _root_.solution {R : Type} [CommRing R] (b : DualNumber R) (r s : R) (h : r * s = b.fst) :
    TrivSqZeroExt.inl b.snd * (DualNumber.eps : DualNumber R)
      + TrivSqZeroExt.inl s * TrivSqZeroExt.inl r = b := by
  ext <;> simp [← h, mul_comm]
end GlobalTheory.SqZeroPow
