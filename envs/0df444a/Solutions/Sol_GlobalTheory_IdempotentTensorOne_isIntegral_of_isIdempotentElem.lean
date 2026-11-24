-- Prove2me | solution 1 for GlobalTheory.IdempotentTensorOne.isIntegral_of_isIdempotentElem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:38:36.995554+00:00
-- url     : https://prove2.me/submissions/e0f719e5-436d-4f84-8e4b-65c6c2999139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralOfIsIdempotentElem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.IdempotentTensorOne
namespace GlobalTheory.IdempotentTensorOne
theorem _root_.solution {S B : Type} [CommRing S] [CommRing B] [Algebra S B]
    {e : B} (he : IsIdempotentElem e) : IsIntegral S e := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by norm_num)), ?_⟩
  simp [sq, he.eq]
end GlobalTheory.IdempotentTensorOne
