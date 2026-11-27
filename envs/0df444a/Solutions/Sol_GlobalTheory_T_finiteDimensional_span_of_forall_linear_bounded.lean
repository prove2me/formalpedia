-- Prove2me | solution 1 for GlobalTheory.T.finiteDimensional_span_of_forall_linear_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:33:39.244747+00:00
-- url     : https://prove2.me/submissions/ef0c60b5-658f-4937-acb8-0534a5a14184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanFiniteDimensionalOfBoundedForms
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanFiniteDimensionalOfBoundedFormsStatement
import Theorems.Thm_GlobalTheory_span_finiteDimensional_of_bounded_forms


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s) := by
  first | exact @GlobalTheory.span_finiteDimensional_of_bounded_forms | exact GlobalTheory.span_finiteDimensional_of_bounded_forms | (intros; apply GlobalTheory.span_finiteDimensional_of_bounded_forms <;> assumption)
end _root_.GlobalTheory.T
