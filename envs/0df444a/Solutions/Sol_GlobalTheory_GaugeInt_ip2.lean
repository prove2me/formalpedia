-- Prove2me | solution 1 for GlobalTheory.GaugeInt.ip2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:00:29.053535+00:00
-- url     : https://prove2.me/submissions/d38638fe-1167-45c2-92f5-7d7807cba890

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.QuadDeriv
open GlobalTheory GlobalTheory.GaugeInt
variable {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {d : ℕ}
variable {φ}
namespace GlobalTheory.GaugeInt
theorem _root_.solution {n : ℕ} {a b : Pt k n d} (ha : IP φ a) (hb : IP φ b) : ∀ j, IP φ (![a, b] j) := by
  intro j; fin_cases j; exacts [ha, hb]
end GlobalTheory.GaugeInt
