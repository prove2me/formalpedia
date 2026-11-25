-- Prove2me | solution 1 for GlobalTheory.T.eq_zero_of_trace_mul_of_separable_generated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:40:53.741937+00:00
-- url     : https://prove2.me/submissions/91b38682-b7ec-4ca6-b7c1-3e409d4fca5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGenerated
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGeneratedStatement
import Theorems.Thm_GlobalTheory_UnitLemma_TraceNondeg_eq_zero_of_trace_mul_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → (∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f) → ∀ w : B.A, (∀ y, Algebra.trace K.E B.A (w * y) = 0) → w = 0 := by
  first | exact @GlobalTheory.UnitLemma.TraceNondeg.eq_zero_of_trace_mul_eq_zero | exact GlobalTheory.UnitLemma.TraceNondeg.eq_zero_of_trace_mul_eq_zero | (intros; apply GlobalTheory.UnitLemma.TraceNondeg.eq_zero_of_trace_mul_eq_zero <;> assumption)
end _root_.GlobalTheory.T
