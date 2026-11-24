-- Prove2me | solution 1 for GlobalTheory.Div.CMAlgChar.fiber_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:23:44.866318+00:00
-- url     : https://prove2.me/submissions/aaf1d70f-6667-4913-9ed6-044854785e4a

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
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] [DecidableEq (E →+* ℂ)]
    [DecidableEq (InfinitePlace E)]
    (w : InfinitePlace E) :
    (Finset.univ.filter fun φ : E →+* ℂ => InfinitePlace.mk φ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  have h1 : InfinitePlace.mk φ = w ↔ InfinitePlace.mk φ = InfinitePlace.mk w.embedding := by
    rw [w.mk_embedding]
  rw [h1, InfinitePlace.mk_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right; rw [← h, ComplexEmbedding.involutive_conjugate E]
  · rintro (h | h)
    · exact Or.inl h
    · right; rw [h, ComplexEmbedding.involutive_conjugate E]
end GlobalTheory.Div.CMAlgChar
