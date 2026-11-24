-- Prove2me | solution 1 for GlobalTheory.Mem.GelfCheck.rowE_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:00.469217+00:00
-- url     : https://prove2.me/submissions/8fb16c94-afc4-4e19-a839-cfaa8ecf73ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_GelfA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TracePowApply
import Theorems.Thm_GlobalTheory_Mem_GelfCheck_rowE_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.GelfCheck
open MvPolynomial GlobalTheory.Mem.Gelf
open MvPolynomial
namespace GlobalTheory.Mem.GelfCheck
namespace _root_.GlobalTheory.Mem.GelfCheck
theorem _root_.solution (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (x : R) :
    _root_.GlobalTheory.Mem.Gelf.rowE R r n a b (C x) = 0 := by
  simp [_root_.GlobalTheory.Mem.GelfCheck.rowE_apply]
end _root_.GlobalTheory.Mem.GelfCheck
end GlobalTheory.Mem.GelfCheck
