-- Prove2me | solution 1 for GlobalTheory.RealZeroNearOne.order_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:54:04.970693+00:00
-- url     : https://prove2.me/submissions/d546ce8f-bfe3-462a-9fed-8baba43a635c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivDirichletLFunctionLocalZeroSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegSumLogDerivNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_OrderNeTop
import Theorems.Thm_GlobalTheory_RealZeroNearOne_analyticAt_L

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.RealZeroNearOne
namespace GlobalTheory.RealZeroNearOne
theorem _root_.solution {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ≠ 1) (z : ℂ) :
    analyticOrderAt (LFunction χ) z ≠ ⊤ := by
  intro htop
  rw [AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z (fun w => analyticAt_L h w)] at htop
  have h2 : LFunction χ 2 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (.inl h) (by norm_num)
  exact h2 (by rw [htop, Pi.zero_apply])
end GlobalTheory.RealZeroNearOne
