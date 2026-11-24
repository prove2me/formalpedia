-- Prove2me | solution 1 for GlobalTheory.exists_realPlace_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:58.940554+00:00
-- url     : https://prove2.me/submissions/b4955e10-2e87-4450-8066-cd74ac841f6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsResidueClassNearRealEmbeddings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {F : Type} [Field F] [NumberField F] (τ : F →+* ℝ) :
    ∃ (P : InfinitePlace F) (hP : P.IsReal), embedding_of_isReal hP = τ := by
  have hreal : ComplexEmbedding.IsReal (Complex.ofRealHom.comp τ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hP : (InfinitePlace.mk (Complex.ofRealHom.comp τ)).IsReal := isReal_mk_iff.2 hreal
  refine ⟨_, hP, ?_⟩
  ext x
  apply Complex.ofReal_injective
  rw [embedding_of_isReal_apply, embedding_mk_eq_of_isReal hreal]
  simp
end GlobalTheory
