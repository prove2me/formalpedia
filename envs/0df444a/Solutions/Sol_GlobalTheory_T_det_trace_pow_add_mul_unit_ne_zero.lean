-- Prove2me | solution 1 for GlobalTheory.T.det_trace_pow_add_mul_unit_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:22:35.738944+00:00
-- url     : https://prove2.me/submissions/7fcc12ce-edc3-44b7-85a3-8813468cdde7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetTracePowAddMulUnitNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetTracePowAddMulUnitNeZeroStatement
import Theorems.Thm_GlobalTheory_UnitLemma_TraceDet_det_trace_pow_mul_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ u : B.A, IsUnit u → (Matrix.of fun k l : Fin (Module.finrank K.E B.A) => Algebra.trace K.E B.A (B.g ^ ((k : ℕ) + (l : ℕ)) * u)).det ≠ 0 := by
  first | exact @GlobalTheory.UnitLemma.TraceDet.det_trace_pow_mul_ne_zero | exact GlobalTheory.UnitLemma.TraceDet.det_trace_pow_mul_ne_zero | (intros; apply GlobalTheory.UnitLemma.TraceDet.det_trace_pow_mul_ne_zero <;> assumption)
end _root_.GlobalTheory.T
