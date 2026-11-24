-- Prove2me | solution 1 for GlobalTheory.mvPowerSeries_map_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:23:47.309187+00:00
-- url     : https://prove2.me/submissions/f8afb68f-166f-47f5-ad73-c24136b7852c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesMemMapCOfCoeffMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {σ R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) :
    Function.Surjective (MvPowerSeries.map (σ := σ) φ) := by
  intro g
  refine ⟨fun n => Function.surjInv hφ (MvPowerSeries.coeff n g), ?_⟩
  ext n
  exact Function.surjInv_eq hφ _
end GlobalTheory
