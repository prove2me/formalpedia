-- Prove2me | solution 1 for GlobalTheory.T.exists_unit_trace_unramifiedInvolutionFieldExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:51:35.207996+00:00
-- url     : https://prove2.me/submissions/41e74f8c-3f4f-4b67-9286-4e7f2a84a52b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtensionStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_trace_unit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∃ y : K'.O, ∃ a : K.O, IsUnit a ∧ @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a := by
  first | exact @GlobalTheory.UnitLemma.Unr.exists_trace_unit | exact GlobalTheory.UnitLemma.Unr.exists_trace_unit | (intros; apply GlobalTheory.UnitLemma.Unr.exists_trace_unit <;> assumption)
end _root_.GlobalTheory.T
