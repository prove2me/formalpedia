-- Prove2me | solution 1 for GlobalTheory.CMType.mem_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:32:19.005966+00:00
-- url     : https://prove2.me/submissions/6ce1eaa4-fbbb-4593-92cf-25be13b67172

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped ComplexConjugate
open GlobalTheory
open GlobalTheory.CMType
variable {E : Type*} [Field E]
namespace GlobalTheory.CMType
theorem _root_.solution (Φ : CMType E) (τ : E →+* ℂ) :
    τ ∈ Φ.conjugate ↔ ComplexEmbedding.conjugate τ ∈ Φ := Iff.rfl
end GlobalTheory.CMType
