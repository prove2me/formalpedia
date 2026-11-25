-- Prove2me | solution 1 for GlobalTheory.ComplexEmbedding.exists_embedding_fractionField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:55:50.232909+00:00
-- url     : https://prove2.me/submissions/595c3254-dd95-4bbd-88e9-3971a2e0a9f4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComplexEmbeddingFractionFieldCdvr
import Theorems.Thm_GlobalTheory_ComplexEmbedding_mk_le_continuum_of_finite_residueField
import Theorems.Thm_GlobalTheory_ComplexEmbedding_exists_embedding_of_mk_le_continuum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Pj
open GlobalTheory GlobalTheory.ComplexEmbedding
open Cardinal IsLocalRing
namespace GlobalTheory.ComplexEmbedding
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T : CDVR), T.FinRes →
      ∀ io : K →+* T.Fr, ∃ ι : T.Fr →+* ℂ, ι.comp io = σ := by
  intro K _ _ σ T hT io
  haveI : Finite (ResidueField T.V) := hT
  have hV := mk_le_continuum_of_finite_residueField T.V
  have hF : #T.Fr ≤ 𝔠 := by
    rw [show #T.Fr = #T.V from IsFractionRing.cardinalMk T.V T.Fr]
    exact hV
  exact @exists_embedding_of_mk_le_continuum K T.Fr _ _ _ io.toAlgebra hF σ
end GlobalTheory.ComplexEmbedding
