-- Prove2me | solution 1 for GlobalTheory.HCA.dw_append
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:26.635033+00:00
-- url     : https://prove2.me/submissions/25c35e54-c95b-45b9-ac9c-a57b352e1028

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
theorem _root_.solution {d : ℕ} (w v : List (Fin d)) (f : E d → ℂ) : dw (w ++ v) f = dw w (dw v f) := by
  induction w with
  | nil => rfl
  | cons j w ih => funext x; show fderiv ℝ (dw (w ++ v) f) x (ev j) = _; rw [ih]; rfl
end GlobalTheory.HCA
