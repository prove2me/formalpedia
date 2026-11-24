-- Prove2me | solution 1 for GlobalTheory.ChowHt.IsChowFormCycle.nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:54:53.942775+00:00
-- url     : https://prove2.me/submissions/e2cb9e11-8a95-450c-95be-47773105c272

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Theorems.Thm_GlobalTheory_ChowHt_isChowFormCycle_zero_iff
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
namespace IsChowFormCycle
theorem _root_.solution {Z : Ideal (MvPolynomial (Fin N) k) →₀ ℕ} {e dl : ℕ}
    {f : MvPolynomial (Fin (e + 1) × Fin N) k} (h : IsChowFormCycle Z e dl f) (m : ℕ) :
    IsChowFormCycle (m • Z) e (m * dl) (f ^ m) := by
  induction m with
  | zero => simpa using isChowFormCycle_zero_iff.2 ⟨rfl, 1, one_ne_zero, C_1.symm⟩
  | succ m ih =>
    rw [succ_nsmul, Nat.succ_mul, pow_succ]
    exact ih.add h
end IsChowFormCycle
end GlobalTheory.ChowHt
