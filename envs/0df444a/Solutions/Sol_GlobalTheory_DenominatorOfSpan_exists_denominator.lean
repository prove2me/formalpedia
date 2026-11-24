-- Prove2me | solution 1 for GlobalTheory.DenominatorOfSpan.exists_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:40:59.076679+00:00
-- url     : https://prove2.me/submissions/5a0df021-90de-4b5c-8b0d-926e5f0f5290

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmulMemOfSpanEqTop
import Theorems.Thm_GlobalTheory_DenominatorOfSpan_exists_smul_mem_of_span_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DenominatorOfSpan
open GlobalTheory.UnitLemma
namespace GlobalTheory.DenominatorOfSpan
theorem _root_.solution {K : UQ} (B : InvAlg K) (L : Submodule K.O B.A)
    (hL : Submodule.span K.E (L : Set B.A) = ⊤) (x : B.A) :
    ∃ d : K.O, d ≠ 0 ∧ d • x ∈ L :=
  exists_smul_mem_of_span_eq_top L hL x
end GlobalTheory.DenominatorOfSpan
