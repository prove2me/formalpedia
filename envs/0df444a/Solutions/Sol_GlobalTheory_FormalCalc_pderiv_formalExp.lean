-- Prove2me | solution 1 for GlobalTheory.FormalCalc.pderiv_formalExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:07:15.933572+00:00
-- url     : https://prove2.me/submissions/873d55cc-99bc-45ee-b5a1-05e30bd70586

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_powerSeries_subst


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
theorem _root_.solution {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) (i : σ) :
    pderiv A i (formalExp f) = formalExp f * pderiv A i f := by
  rw [formalExp, pderiv_powerSeries_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf),
    PowerSeries.derivative_exp]
end GlobalTheory.FormalCalc
