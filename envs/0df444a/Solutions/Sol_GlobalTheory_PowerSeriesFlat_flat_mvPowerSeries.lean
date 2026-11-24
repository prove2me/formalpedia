-- Prove2me | solution 1 for GlobalTheory.PowerSeriesFlat.flat_mvPowerSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:43:43.218341+00:00
-- url     : https://prove2.me/submissions/b6ef5171-763b-45b9-8f1e-a282845ffe67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatMvPowerSeries
import Theorems.Thm_GlobalTheory_PowerSeriesFlat_flat_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.PowerSeriesFlat
namespace GlobalTheory.PowerSeriesFlat
theorem _root_.solution :
    ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (σ : Type),
      Module.Flat T (MvPowerSeries σ T) :=
  fun T _ _ σ => flat_pi T (σ →₀ ℕ)
end GlobalTheory.PowerSeriesFlat
