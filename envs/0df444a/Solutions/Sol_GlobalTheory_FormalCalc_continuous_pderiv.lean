-- Prove2me | solution 1 for GlobalTheory.FormalCalc.continuous_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:09:45.47859+00:00
-- url     : https://prove2.me/submissions/c4b2bceb-c29b-4563-b832-41ce260965a8

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
open MvPowerSeries.WithPiTopology
namespace GlobalTheory.FormalCalc
theorem _root_.solution [TopologicalSpace R] [DiscreteTopology R] (i : σ) :
    Continuous (pderiv R i : MvPowerSeries σ R → MvPowerSeries σ R) := by
  refine continuous_iff_continuousAt.mpr fun f => ?_
  rw [ContinuousAt, tendsto_iff_coeff_tendsto]
  intro d
  simp only [coeff_pderiv]
  exact ((continuous_coeff R (d + single i 1)).mul continuous_const).continuousAt
end GlobalTheory.FormalCalc
