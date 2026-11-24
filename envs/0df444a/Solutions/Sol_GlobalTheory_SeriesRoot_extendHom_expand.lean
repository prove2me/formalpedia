-- Prove2me | solution 1 for GlobalTheory.SeriesRoot.extendHom_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:45:35.848026+00:00
-- url     : https://prove2.me/submissions/db3ba736-327b-4a49-8c6e-1237d0b65b4d

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
    (ht : t ^ k = φ X) (g : PowerSeries O) : extendHom φ hk ht (expand k hk g) = φ g := by
  have := extendAdd_X_pow_mul_expand φ hk ht 0 g
  rw [pow_zero, pow_zero, one_mul, one_mul] at this
  exact this
end GlobalTheory.SeriesRoot
