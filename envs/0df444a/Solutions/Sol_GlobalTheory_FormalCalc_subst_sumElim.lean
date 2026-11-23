-- Prove2me | solution 1 for GlobalTheory.FormalCalc.subst_sumElim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:59.169697+00:00
-- url     : https://prove2.me/submissions/31fd5eb7-f7ff-415e-8feb-69ba0bde4cd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries Sum
variable {σ τ ι κ μ A : Type*} [CommRing A]
namespace GlobalTheory.FormalCalc
theorem _root_.solution (b : κ → MvPowerSeries μ A) (u : σ → MvPowerSeries κ A)
    (t : τ → MvPowerSeries κ A) :
    (fun i => subst b (Sum.elim u t i)) =
      Sum.elim (fun i => subst b (u i)) fun j => subst b (t j) := by
  funext i; cases i <;> rfl
end GlobalTheory.FormalCalc
