-- Prove2me | solution 1 for GlobalTheory.T.rational_functional_trace_representation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:33:46.179883+00:00
-- url     : https://prove2.me/submissions/e4f3a64f-a8c0-4b6d-8aa3-56dd62ed12fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RationalFunctionalTraceRepresentation
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RationalFunctionalTraceRepresentationStatement
import Theorems.Thm_GlobalTheory_linearMap_rat_valued_eq_trace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (g : E →ₗ[ℚ] ℝ), (∀ z, ∃ q : ℚ, g z = q) →
    ∃ mu : E, ∀ z, g z = ((Algebra.trace ℚ E (mu * z) : ℚ) : ℝ) := by
  first | exact @GlobalTheory.linearMap_rat_valued_eq_trace | exact GlobalTheory.linearMap_rat_valued_eq_trace | (intros; apply GlobalTheory.linearMap_rat_valued_eq_trace <;> assumption)
end _root_.GlobalTheory.T
