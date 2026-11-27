-- Prove2me | solution 1 for GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:34:52.414729+00:00
-- url     : https://prove2.me/submissions/5e832ce0-0d3f-49c1-9f04-e575a99a0c0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceEqSumMultMulRe
import Theorems.Thm_GlobalTheory_TraceRealEmbeddingSum_re_embedding_mk

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
theorem _root_.solution {F : Type} [Field F] [NumberField F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) =
      ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re := by
  classical

  have htr : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ σ : F →ₐ[ℚ] ℂ, σ x := by
    rw [← trace_eq_sum_embeddings ℂ (K := ℚ) (L := F), eq_ratCast]
  have hre : ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, (φ x).re := by
    have h := congrArg Complex.re htr
    rw [Complex.ratCast_re, Complex.re_sum] at h
    rw [h, ← (RingHom.equivRatAlgHom F ℂ).sum_comp]
    rfl

  rw [hre, ← Finset.univ.sum_fiberwise (fun φ : F →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hfib : ∀ φ ∈ Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w),
      (φ x).re = (w.embedding x).re := by
    intro φ hφ
    rw [(Finset.mem_filter.mp hφ).2.symm, re_embedding_mk]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    nsmul_eq_mul]
end GlobalTheory.TraceRealEmbeddingSum
