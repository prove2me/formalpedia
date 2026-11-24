-- Prove2me | solution 1 for GlobalTheory.FormalCalc.subst_formalExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:09:47.880907+00:00
-- url     : https://prove2.me/submissions/fa0ebf61-9960-4c37-81fb-08c5e2361d43

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
theorem _root_.solution {a : σ → MvPowerSeries τ A} (ha : HasSubst a)
    {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) :
    subst a (formalExp f) = formalExp (subst a f) := by
  rw [formalExp, formalExp, PowerSeries.subst, PowerSeries.subst,
    subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hf).const ha]
end GlobalTheory.FormalCalc
