-- Prove2me | solution 1 for GlobalTheory.GaugeInt.ip_evP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:02:13.780721+00:00
-- url     : https://prove2.me/submissions/9ba946a8-d250-46e2-bc79-7f18e6a433ec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Theorems.Thm_GlobalTheory_QuadDeriv_map_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_evP


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
theorem _root_.solution {m n : ℕ} {V : Fin m → Pt k n d} (hV : ∀ j, IP φ (V j)) {a : Pt k m d}
    (ha : IP φ a) : IP φ (evP V a) := by
  obtain ⟨a, h0, rfl⟩ := ha
  choose V' h1 h2 using hV
  obtain rfl : V = fun j => mapP φ (V' j) := funext fun j => (h2 j).symm
  exact ⟨evP V' a, gp_evP V' h1 a h0, funext fun i => map_ev φ V' h1 (a i)⟩
end GlobalTheory.GaugeInt
