-- Prove2me | solution 1 for GlobalTheory.QNorm.exists_infiniteAdele_real_component
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:43:47.78275+00:00
-- url     : https://prove2.me/submissions/0daea57d-0795-48a8-b897-c0068d00cb49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsAdmissibleLocalNormMemSUnitsSupGlobalNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsIdeleNotMulNorm
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (σ : F →+* ℝ) :
    ∃ e : InfiniteAdeleRing F →+* ℝ,
      ∀ t : F, e (algebraMap F (InfiniteAdeleRing F) t) = σ t := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp
  have hw : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal := ⟨_, hφ, rfl⟩
  refine ⟨(InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).comp
    (Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) _), fun t => ?_⟩
  have he := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw
    ((WithAbs.equiv (InfinitePlace.mk (Complex.ofRealHom.comp σ)).1).symm t)
  refine he.trans ?_
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  simp
end GlobalTheory.QNorm
