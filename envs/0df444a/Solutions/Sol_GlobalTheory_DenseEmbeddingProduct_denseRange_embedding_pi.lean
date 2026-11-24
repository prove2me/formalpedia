-- Prove2me | solution 1 for GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:10:57.266503+00:00
-- url     : https://prove2.me/submissions/ccfdc6b9-6761-4d83-bf2c-49a659ebe175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DenseRangeEmbeddingPi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DenseEmbeddingProduct
open NumberField NumberField.InfinitePlace
namespace GlobalTheory.DenseEmbeddingProduct
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] :
    DenseRange fun (x : E) (w : InfinitePlace E) ↦ (InfinitePlace.embedding w : E → ℂ) x := by
  let Φ : InfiniteAdeleRing E → (InfinitePlace E → ℂ) :=
    fun y w ↦ Completion.extensionEmbedding w (y w)
  have hc : Continuous Φ := continuous_pi fun w ↦
    (Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
  have hs : Function.Surjective Φ := by
    intro f
    choose y hy using fun w : InfinitePlace E ↦
      Completion.surjective_extensionEmbedding_of_isComplex (IsTotallyComplex.isComplex w) (f w)
    exact ⟨y, funext hy⟩
  have h := hs.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc
  convert h using 1
  funext x w
  simp [Φ]
end GlobalTheory.DenseEmbeddingProduct
