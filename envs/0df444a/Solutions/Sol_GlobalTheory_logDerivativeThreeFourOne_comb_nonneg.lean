-- Prove2me | solution 1 for GlobalTheory.logDerivativeThreeFourOne.comb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:18:55.7207+00:00
-- url     : https://prove2.me/submissions/36035104-24a8-40e3-bd29-143554efd7cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivativeBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.logDerivativeThreeFourOne
namespace GlobalTheory.logDerivativeThreeFourOne
theorem _root_.solution {z : ℂ} (hz : ‖z‖ = 1) : 0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have h : z.re ^ 2 + z.im ^ 2 = 1 := by
    have e := Complex.normSq_eq_norm_sq z
    rw [hz, Complex.normSq_apply] at e
    nlinarith
  have e2 : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by simp [sq]
  rw [e2]
  nlinarith [sq_nonneg (z.re + 1)]
end GlobalTheory.logDerivativeThreeFourOne
