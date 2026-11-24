-- Prove2me | solution 1 for GlobalTheory.TraceSumRealEmbeddings.sum_re_embeddings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:57:44.522056+00:00
-- url     : https://prove2.me/submissions/f25b5243-caf0-4556-b7c7-99c96ccf3161

import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_LocalDualIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TraceInfAlgebraMap
import Theorems.Thm_GlobalTheory_TraceSumRealEmbeddings_re_embedding_mk

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
theorem _root_.solution (F : Type) [Field F] [NumberField F] (x : F) :
    ∑ φ : F →+* ℂ, (φ x).re = ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re := by
  classical
  rw [← Finset.univ.sum_fiberwise (fun φ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hw : ∀ φ ∈ ({φ | InfinitePlace.mk φ = w} : Finset (F →+* ℂ)), (φ x).re = (w.embedding x).re :=
    fun φ hφ => by rw [← (Finset.mem_filter.mp hφ).2, re_embedding_mk]
  rw [Finset.sum_congr rfl hw, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]
end GlobalTheory.TraceSumRealEmbeddings
