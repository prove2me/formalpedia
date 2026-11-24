-- Prove2me | solution 1 for GlobalTheory.cm_eq_or_conj_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:31:55.143949+00:00
-- url     : https://prove2.me/submissions/d9fbdd38-0b9a-48d0-b977-5bd89bd7dfb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldProdEmbeddingsRegroupMaximalReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E]
    (τ τ' : E →+* ℂ)
    (h : τ'.comp (algebraMap (maximalRealSubfield E) E) =
      τ.comp (algebraMap (maximalRealSubfield E) E)) :
    τ' = τ ∨ τ' = ComplexEmbedding.conjugate τ := by
  have h1 : InfinitePlace.mk τ = InfinitePlace.mk τ' := by
    apply (IsCMField.equivInfinitePlace E).injective
    rw [IsCMField.equivInfinitePlace_apply, IsCMField.equivInfinitePlace_apply,
      InfinitePlace.comap_mk, InfinitePlace.comap_mk, h]
  rcases InfinitePlace.mk_eq_iff.1 h1 with h2 | h2
  · exact Or.inl h2.symm
  · exact Or.inr h2.symm
end GlobalTheory
