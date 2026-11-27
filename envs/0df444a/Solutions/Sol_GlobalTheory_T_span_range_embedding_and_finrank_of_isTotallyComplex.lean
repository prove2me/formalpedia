-- Prove2me | solution 1 for GlobalTheory.T.span_range_embedding_and_finrank_of_isTotallyComplex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:33:48.350252+00:00
-- url     : https://prove2.me/submissions/5791a6d9-5430-4329-b93a-e6f6e714f431

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TotallyComplexSpanEmbeddingsAndFinrank
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TotallyComplexSpanEmbeddingsAndFinrankStatement
import Theorems.Thm_GlobalTheory_totallyComplex_span_embeddings_and_finrank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], Submodule.span ℝ (Set.range (Pi.ringHom fun w : InfinitePlace E => w.embedding)) = ⊤ ∧ Module.finrank ℝ (InfinitePlace E → ℂ) = Module.finrank ℚ E := by
  first | exact @GlobalTheory.totallyComplex_span_embeddings_and_finrank | exact GlobalTheory.totallyComplex_span_embeddings_and_finrank | (intros; apply GlobalTheory.totallyComplex_span_embeddings_and_finrank <;> assumption)
end _root_.GlobalTheory.T
