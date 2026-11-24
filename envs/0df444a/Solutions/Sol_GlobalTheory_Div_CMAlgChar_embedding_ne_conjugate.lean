-- Prove2me | solution 1 for GlobalTheory.Div.CMAlgChar.embedding_ne_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:23:43.696086+00:00
-- url     : https://prove2.me/submissions/649a1eaf-5da6-4e18-85c7-300691eee8e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmAlgCharEqArgMulAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.CMAlgChar
namespace GlobalTheory.Div.CMAlgChar
theorem _root_.solution {E : Type} [Field E] [IsTotallyComplex E] (w : InfinitePlace E) :
    w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
  intro h
  have hc := IsTotallyComplex.isComplex w
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff,
    ComplexEmbedding.isReal_iff] at hc
  exact hc h.symm
end GlobalTheory.Div.CMAlgChar
