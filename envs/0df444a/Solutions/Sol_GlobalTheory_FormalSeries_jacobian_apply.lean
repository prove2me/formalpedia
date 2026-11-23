-- Prove2me | solution 1 for GlobalTheory.FormalSeries.jacobian_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:09.807411+00:00
-- url     : https://prove2.me/submissions/028439f3-0049-4ec2-a099-6cdc89bb4f87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FormalSeries
open MvPowerSeries
variable {σ τ υ R S : Type*} [CommRing R] [CommRing S]
namespace GlobalTheory.FormalSeries
theorem _root_.solution (f : τ → MvPowerSeries σ R) (i : τ) (j : σ) :
    jacobian f i j = coeff (Finsupp.single j 1) (f i) := rfl
end GlobalTheory.FormalSeries
