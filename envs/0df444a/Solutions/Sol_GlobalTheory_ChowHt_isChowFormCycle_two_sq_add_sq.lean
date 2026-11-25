-- Prove2me | solution 1 for GlobalTheory.ChowHt.isChowFormCycle_two_sq_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:29:49.521609+00:00
-- url     : https://prove2.me/submissions/a5f52911-b319-4907-86eb-0c888f9319f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Theorems.Thm_GlobalTheory_ChowHt_IsChowFormCycle_nsmul
import Theorems.Thm_GlobalTheory_ChowHt_isPrime_span_sq_add_sq
import Theorems.Thm_GlobalTheory_ChowHt_isHomogeneous_span_sq_add_sq
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type} [Field k] {N : ℕ}
namespace GlobalTheory.ChowHt
theorem _root_.solution :
    IsChowFormCycle
      (Finsupp.single (Ideal.span {(X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)}) 2) 0 4
      ((X (0, 0) ^ 2 + X (0, 1) ^ 2) ^ 2) := by
  simpa using (isChowFormInt_sq_add_sq.single isPrime_span_sq_add_sq
    isHomogeneous_span_sq_add_sq).nsmul 2
end GlobalTheory.ChowHt
