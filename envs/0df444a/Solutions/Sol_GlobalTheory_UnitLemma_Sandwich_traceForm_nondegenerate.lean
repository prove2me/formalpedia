-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Sandwich.traceForm_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:40:45.100527+00:00
-- url     : https://prove2.me/submissions/e08bc412-3530-4856-a2f3-3fe91fc8fd6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGenerated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmulMemOfSpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements
import Theorems.Thm_GlobalTheory_UnitLemma_Sandwich_exists_aeval
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
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Sandwich
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.UnitLemma.Sandwich
theorem _root_.solution (hP : B.P.Separable) : (Algebra.traceForm K.E B.A).Nondegenerate := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · exact TraceNondeg.eq_zero_of_trace_mul_eq_zero K B hP (exists_aeval B hP) w
      (fun y => by simpa [Algebra.traceForm_apply] using hw y)
  · exact TraceNondeg.eq_zero_of_trace_mul_eq_zero K B hP (exists_aeval B hP) w
      (fun y => by simpa [Algebra.traceForm_apply, mul_comm] using hw y)
end GlobalTheory.UnitLemma.Sandwich
