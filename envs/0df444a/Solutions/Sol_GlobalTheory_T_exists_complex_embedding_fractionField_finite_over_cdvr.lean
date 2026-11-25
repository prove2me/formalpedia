-- Prove2me | solution 1 for GlobalTheory.T.exists_complex_embedding_fractionField_finite_over_cdvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:14:52.231883+00:00
-- url     : https://prove2.me/submissions/199626ec-4a6d-4588-8d6c-68065295c6bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComplexEmbeddingFractionFieldFiniteOverCdv
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComplexEmbeddingFractionFieldCdvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComplexEmbeddingFractionFieldFiniteOverCdvStatement
import Theorems.Thm_GlobalTheory_ComplexEmbedding_exists_embedding_fractionField_of_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.L2.Pj
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T T' : CDVR) (g : T.V →+* T'.V), Function.Injective g → g.Finite → Countable (IsLocalRing.ResidueField T.V) → ∀ io : K →+* T'.Fr, ∃ ι : T'.Fr →+* ℂ, ι.comp io = σ := by
  first | exact @GlobalTheory.ComplexEmbedding.exists_embedding_fractionField_of_finite | exact GlobalTheory.ComplexEmbedding.exists_embedding_fractionField_of_finite | (intros; apply GlobalTheory.ComplexEmbedding.exists_embedding_fractionField_of_finite <;> assumption)
end _root_.GlobalTheory.T
