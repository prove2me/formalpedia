-- Prove2me | solution 1 for GlobalTheory.FormalCalc.pderiv_powerSeries_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:49:41.626795+00:00
-- url     : https://prove2.me/submissions/1b45f104-2365-424b-8866-ce27628026ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries Finsupp
variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
namespace GlobalTheory.FormalCalc
theorem _root_.solution {a : MvPowerSeries τ S} (ha : PowerSeries.HasSubst a)
    (f : PowerSeries R) (j : τ) :
    pderiv S j (PowerSeries.subst a f) =
      PowerSeries.subst a (PowerSeries.derivative R f) * pderiv S j a := by
  have h := pderiv_subst (σ := Unit) (a := fun _ => a) ha.const f j
  simpa [PowerSeries.subst, PowerSeries.derivative] using h
end GlobalTheory.FormalCalc
