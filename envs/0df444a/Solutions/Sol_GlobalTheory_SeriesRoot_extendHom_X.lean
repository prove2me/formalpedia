-- Prove2me | solution 1 for GlobalTheory.SeriesRoot.extendHom_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:45:34.969928+00:00
-- url     : https://prove2.me/submissions/bc9e5a65-50c9-4eda-9c33-db1d9ad2546d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRingHomPowerSeriesRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open GlobalTheory
open GlobalTheory.SeriesRoot
variable {O : Type*} [CommRing O]
variable {K : Type*} [CommRing K]
namespace GlobalTheory.SeriesRoot
theorem _root_.solution (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) : extendHom φ hk ht X = t := by
  have := extendAdd_X_pow_mul_expand φ hk ht 1 1
  rw [pow_one, pow_one, map_one, map_one, mul_one, mul_one] at this
  exact this
end GlobalTheory.SeriesRoot
