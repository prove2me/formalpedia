-- Prove2me | solution 1 for GlobalTheory.TraceSumRealEmbeddings.re_embedding_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:39:04.936803+00:00
-- url     : https://prove2.me/submissions/890e47de-7184-4c65-8d13-d298bd02d23d

import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_LocalDualIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TraceInfAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TraceSumRealEmbeddings
open NumberField NumberField.InfinitePlace
namespace GlobalTheory.TraceSumRealEmbeddings
theorem _root_.solution {F : Type} [Field F] (φ : F →+* ℂ) (x : F) :
    ((InfinitePlace.mk φ).embedding x).re = (φ x).re := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h <;> rw [h]
  rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
end GlobalTheory.TraceSumRealEmbeddings
