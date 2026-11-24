-- Prove2me | solution 1 for GlobalTheory.FormalCalc.pderiv_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:57.026454+00:00
-- url     : https://prove2.me/submissions/3c0f4b44-ed22-4a96-bbb0-e3cdd399ec27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq

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
theorem _root_.solution {T : Type*} [CommRing T] (φ : R →+* T) (i : σ) (f : MvPowerSeries σ R) :
    pderiv T i (map φ f) = map φ (pderiv R i f) := by
  ext d
  simp [coeff_pderiv]
end GlobalTheory.FormalCalc
