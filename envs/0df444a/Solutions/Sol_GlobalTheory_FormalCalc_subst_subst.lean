-- Prove2me | solution 1 for GlobalTheory.FormalCalc.subst_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:33.73353+00:00
-- url     : https://prove2.me/submissions/b04ef79b-dc43-4167-ab23-e0357251af47

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
theorem _root_.solution [Finite ι] {a : ι → MvPowerSeries κ A} {b : κ → MvPowerSeries μ A}
    (hb : HasSubst b) (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries ι A) :
    subst b (subst a f) = subst (fun i => subst b (a i)) f :=
  subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) hb f
end GlobalTheory.FormalCalc
