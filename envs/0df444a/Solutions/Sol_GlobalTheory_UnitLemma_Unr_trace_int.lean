-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.trace_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:33:52.533808+00:00
-- url     : https://prove2.me/submissions/d2b55c65-b4b1-4500-abea-a953dc2b9fb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceIntOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIntegersUnramifiedInvolutionExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnramifiedQuadraticLocalExt
import Theorems.Thm_GlobalTheory_T_isIntegral_integers_unramifiedInvolutionExt
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_IsUnrExt_ne_zero
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_trace_int_of_isIntegral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ y : K'.O,
    ∃ a : K.O, @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a :=
  fun K K' d φ hU y => trace_int_of_isIntegral hU _ (GlobalTheory.T.isIntegral_integers_unramifiedInvolutionExt K K' d φ hU hU.ne_zero y)
end GlobalTheory.UnitLemma.Unr
