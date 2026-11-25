-- Prove2me | solution 1 for GlobalTheory.GaugeInt.int_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:01:20.543903+00:00
-- url     : https://prove2.me/submissions/9ef7652d-cabb-4ebf-9094-59867c598db3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Theorems.Thm_GlobalTheory_QuadDeriv_map_ev


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
theorem _root_.solution {m n : ℕ} {V : Fin m → Pt k n d} (hV : ∀ j, IP φ (V j)) {f : PS k m d}
    (hf : f ∈ IntS φ m d) : ev V f ∈ IntS φ n d := by
  obtain ⟨f, rfl⟩ := hf
  choose V' h1 h2 using hV
  obtain rfl : V = fun j => mapP φ (V' j) := funext fun j => (h2 j).symm
  exact ⟨ev V' f, map_ev φ V' h1 f⟩
end GlobalTheory.GaugeInt
