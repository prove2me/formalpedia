-- Prove2me | solution 1 for GlobalTheory.FormalCalc.subst_elim_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:16.288265+00:00
-- url     : https://prove2.me/submissions/64fe82cc-414a-4003-b10e-1a6915ab509e

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
theorem _root_.solution (f : MvPowerSeries (σ ⊕ τ) A) :
    subst (Sum.elim (fun i => X (inl i)) fun j => X (inr j) :
      σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A) f = f := by
  have : (Sum.elim (fun i => X (inl i)) fun j => X (inr j) :
      σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A) = X := by funext i; cases i <;> rfl
  rw [this, subst_self, id]
end GlobalTheory.FormalCalc
