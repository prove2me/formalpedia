-- Prove2me | solution 1 for GlobalTheory.T.exists_integral_trace_unramifiedQuadraticLocalExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:42:43.906314+00:00
-- url     : https://prove2.me/submissions/65b23932-9ebd-4bf6-a27c-c1671fecb38d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnramifiedQuadraticLocalExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnramifiedQuadraticLocalExtStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_trace_int


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
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ y : K'.O, ∃ a : K.O, @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a := by
  first | exact @GlobalTheory.UnitLemma.Unr.trace_int | exact GlobalTheory.UnitLemma.Unr.trace_int | (intros; apply GlobalTheory.UnitLemma.Unr.trace_int <;> assumption)
end _root_.GlobalTheory.T
