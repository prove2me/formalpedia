-- Prove2me | solution 1 for GlobalTheory.HCA.SupEst.dw_zero_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:54:08.096445+00:00
-- url     : https://prove2.me/submissions/203cd6ae-80b7-4486-b4a4-07cc96a6803e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AestronglyMeasurableExtendByZeroOffSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticSystemDerivativeContinuousFunctionalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticWeakSolWordDerivLeConstMulSup

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
noncomputable section
open GlobalTheory GlobalTheory.HCA GlobalTheory.HCA.SupEst
variable {d : ℕ}
namespace GlobalTheory.HCA.SupEst
theorem _root_.solution : ∀ w : List (Fin d), dw w (fun _ : E d => (0 : ℂ)) = fun _ => 0
  | [] => rfl
  | j :: w => by
      funext x
      show fderiv ℝ (dw w (fun _ : E d => (0 : ℂ))) x (ev j) = 0
      rw [solution w]
      simp
end GlobalTheory.HCA.SupEst
