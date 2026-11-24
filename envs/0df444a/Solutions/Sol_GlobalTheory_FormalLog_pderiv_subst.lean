-- Prove2me | solution 1 for GlobalTheory.FormalLog.pderiv_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:05:46.093732+00:00
-- url     : https://prove2.me/submissions/e56a8b05-4e78-4070-af0b-34e603ca79fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqCOfPderivZero
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {σ τ : Type}
namespace GlobalTheory.FormalLog
theorem _root_.solution [Fintype σ] {a : σ → MvPowerSeries τ k} (ha : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries σ k) (t : τ) :
    pderiv k t (subst a f) = ∑ s, subst a (pderiv k s f) * pderiv k t (a s) :=
  GlobalTheory.FormalCalc.pderiv_subst (hasSubst_of_constantCoeff_zero ha) f t
end GlobalTheory.FormalLog
