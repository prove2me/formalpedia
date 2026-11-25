-- Prove2me | solution 1 for GlobalTheory.T.exists_complex_embedding_fractionField_cdvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:14:49.250321+00:00
-- url     : https://prove2.me/submissions/fbeab0bf-d6e2-4826-b7cf-d8c63726c20c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComplexEmbeddingFractionFieldCdvr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComplexEmbeddingFractionFieldCdvrStatement
import Theorems.Thm_GlobalTheory_ComplexEmbedding_exists_embedding_fractionField


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T : CDVR), T.FinRes → ∀ io : K →+* T.Fr, ∃ ι : T.Fr →+* ℂ, ι.comp io = σ := by
  first | exact @GlobalTheory.ComplexEmbedding.exists_embedding_fractionField | exact GlobalTheory.ComplexEmbedding.exists_embedding_fractionField | (intros; apply GlobalTheory.ComplexEmbedding.exists_embedding_fractionField <;> assumption)
end _root_.GlobalTheory.T
