-- Prove2me | solution 1 for GlobalTheory.FormalCalc.pderiv_X_ite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:48.332811+00:00
-- url     : https://prove2.me/submissions/1eb23376-9c47-4d96-81f6-07378c4d5cfa

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
theorem _root_.solution [DecidableEq κ] (i j : κ) :
    pderiv A i (X j : MvPowerSeries κ A) = if j = i then 1 else 0 := by
  split_ifs with h
  · rw [h, pderiv_X_self]
  · exact pderiv_X_of_ne h
end GlobalTheory.FormalCalc
