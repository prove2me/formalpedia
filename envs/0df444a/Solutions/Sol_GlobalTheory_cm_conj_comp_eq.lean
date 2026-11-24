-- Prove2me | solution 1 for GlobalTheory.cm_conj_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:29:15.501175+00:00
-- url     : https://prove2.me/submissions/2b0d4767-aa37-4bfd-b2ab-91a4c3be3b84

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
theorem _root_.solution (E : Type) [Field E] [NumberField E] (τ : E →+* ℂ) :
    (ComplexEmbedding.conjugate τ).comp (algebraMap (maximalRealSubfield E) E) =
      τ.comp (algebraMap (maximalRealSubfield E) E) := by
  have h := IsTotallyReal.complexEmbedding_isReal (τ.comp (algebraMap (maximalRealSubfield E) E))
  rw [ComplexEmbedding.isReal_iff] at h
  exact h
end GlobalTheory
