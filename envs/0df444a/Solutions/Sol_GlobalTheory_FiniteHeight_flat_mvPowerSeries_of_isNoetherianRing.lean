-- Prove2me | solution 1 for GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:58:52.423354+00:00
-- url     : https://prove2.me/submissions/59402a26-ea9e-4e27-8011-9e2a877b8896

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatMvPowerSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatMvPowerSeriesOfIsNoetherianRing
import Theorems.Thm_GlobalTheory_PowerSeriesFlat_flat_mvPowerSeries


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.FiniteHeight
namespace GlobalTheory.FiniteHeight
theorem _root_.solution :
    ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (σ : Type),
      Module.Flat T (MvPowerSeries σ T) :=
  GlobalTheory.PowerSeriesFlat.flat_mvPowerSeries
end GlobalTheory.FiniteHeight
