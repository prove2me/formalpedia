-- Prove2me | solution 1 for GlobalTheory.TraceRealEmbeddingSum.re_embedding_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:38:58.950318+00:00
-- url     : https://prove2.me/submissions/2f09e823-d8fb-4018-9db4-e06711325183

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceEqSumMultMulRe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TraceRealEmbeddingSum
open NumberField
namespace GlobalTheory.TraceRealEmbeddingSum
theorem _root_.solution {F : Type} [Field F] (φ : F →+* ℂ) (x : F) :
    ((InfinitePlace.mk φ).embedding x).re = (φ x).re := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h <;>
    simp [h, ComplexEmbedding.conjugate_coe_eq]
end GlobalTheory.TraceRealEmbeddingSum
