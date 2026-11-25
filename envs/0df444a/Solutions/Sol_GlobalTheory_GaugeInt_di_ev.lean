-- Prove2me | solution 1 for GlobalTheory.GaugeInt.di_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:06:40.229089+00:00
-- url     : https://prove2.me/submissions/15035876-307d-4cc5-b6d3-d2fbbabeb339

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Theorems.Thm_GlobalTheory_GaugeInt_IP_gp
import Theorems.Thm_GlobalTheory_GaugeInt_IP_int
import Theorems.Thm_GlobalTheory_GaugeInt_int_pderiv
import Theorems.Thm_GlobalTheory_GaugeInt_int_ev
import Theorems.Thm_GlobalTheory_QuadDeriv_pderiv_ev


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
    (hf : DI φ f) : DI φ (ev V f) := by
  intro s
  rw [pderiv_ev V fun j => (hV j).gp]
  exact sum_mem fun j _ => sum_mem fun i _ =>
    mul_mem (int_ev hV (hf _)) (int_pderiv ((hV j).int i) s)
end GlobalTheory.GaugeInt
