-- Prove2me | solution 1 for GlobalTheory.HomTrace.finrank_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:37:19.554877+00:00
-- url     : https://prove2.me/submissions/49469b15-2a7c-4603-a915-314dc2cf1a8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HostGeneratorPowFourTraceNormModEight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TraceEqFinrankMulSum
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_finrank_eq
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul
attribute [local simp] GlobalTheory.coe_symplecticGroupMap
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.HomTrace
namespace GlobalTheory.HomTrace
theorem _root_.solution (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    Module.finrank ℂ (X →+ ℂ) = Module.finrank ℤ X := by
  rw [(addMonoidHomLequivInt (A := X) (B := ℂ) ℂ).finrank_eq, Module.finrank_linearMap]
  simp
end GlobalTheory.HomTrace
