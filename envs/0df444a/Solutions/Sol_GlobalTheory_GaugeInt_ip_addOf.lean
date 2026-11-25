-- Prove2me | solution 1 for GlobalTheory.GaugeInt.ip_addOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:06:41.997877+00:00
-- url     : https://prove2.me/submissions/0580809c-7ef5-4852-9df0-17dd98fc62a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Theorems.Thm_GlobalTheory_GaugeInt_ip2
import Theorems.Thm_GlobalTheory_GaugeInt_ip_evP

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
theorem _root_.solution {n : ℕ} {F : Pt k 2 d} {a b : Pt k n d} (hF : IP φ F) (ha : IP φ a) (hb : IP φ b) :
    IP φ (addOf F a b) := ip_evP (ip2 ha hb) hF
end GlobalTheory.GaugeInt
