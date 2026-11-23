-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.val_mul_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:06.518807+00:00
-- url     : https://prove2.me/submissions/05de11a0-5c42-42d3-a143-e016c929eb0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddValNormUnramifiedInvolutionFieldExtEqMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBasisTraceInvolutionDetUnitUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetTraceGramBlockMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetInvAlgBaseChangeUnramifiedOdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution {K : UQ} {a b : K.E} (ha : a ≠ 0) (hb : b ≠ 0) :
    val K.O (a * b) = val K.O a + val K.O b := by
  unfold val
  have ha' : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E a ≠ 0 := by simpa using ha
  have hb' : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E b ≠ 0 := by simpa using hb
  rw [map_mul, WithZero.log_mul ha' hb']; ring
end GlobalTheory.UnitLemma.Unr
