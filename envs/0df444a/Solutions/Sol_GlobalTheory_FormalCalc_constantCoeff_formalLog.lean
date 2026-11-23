-- Prove2me | solution 1 for GlobalTheory.FormalCalc.constantCoeff_formalLog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:24.016273+00:00
-- url     : https://prove2.me/submissions/9e7d2480-d980-49b5-ac34-de250d30110e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries
variable {σ τ A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
namespace GlobalTheory.FormalCalc
theorem _root_.solution {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    constantCoeff (formalLog g) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp [hg]) _ PowerSeries.constantCoeff_log
end GlobalTheory.FormalCalc
