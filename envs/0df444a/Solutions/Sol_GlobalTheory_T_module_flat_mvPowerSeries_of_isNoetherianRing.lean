-- Prove2me | solution 1 for GlobalTheory.T.module_flat_mvPowerSeries_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:19:43.183302+00:00
-- url     : https://prove2.me/submissions/649896b2-663d-43d4-89b6-c86afac51af6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatMvPowerSeriesOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatMvPowerSeriesOfIsNoetherianRingStatement
import Theorems.Thm_GlobalTheory_FiniteHeight_flat_mvPowerSeries_of_isNoetherianRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (σ : Type), Module.Flat T (MvPowerSeries σ T) := by
  first | exact @GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing | exact GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing | (intros; apply GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing <;> assumption)
end _root_.GlobalTheory.T
