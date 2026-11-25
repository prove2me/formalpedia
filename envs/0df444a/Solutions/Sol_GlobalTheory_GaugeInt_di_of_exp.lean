-- Prove2me | solution 1 for GlobalTheory.GaugeInt.di_of_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:01:19.374788+00:00
-- url     : https://prove2.me/submissions/3f154fc7-606f-444b-b940-b70ed7b575a9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_map
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_powerSeries_subst


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
theorem _root_.solution [Algebra ℚ k] {n : ℕ} (p : PS R n d) (hp : constantCoeff p = 1) (a : PS k n d)
    (ha : constantCoeff a = 0) (h : MvPowerSeries.map φ p = FB.expS k a) : DI φ a := by
  intro s
  have h1 : pderiv k s (FB.expS k a) = FB.expS k a * pderiv k s a := by
    unfold FB.expS
    rw [GlobalTheory.FormalCalc.pderiv_powerSeries_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha),
      PowerSeries.derivative_exp]
  have h2 := MvPowerSeries.mul_invOfUnit p 1 (by simpa using hp)
  refine ⟨invOfUnit p 1 * pderiv R s p, ?_⟩
  rw [map_mul, ← GlobalTheory.FormalCalc.pderiv_map, h, h1, ← h, ← mul_assoc, ← map_mul, mul_comm (invOfUnit p 1),
    h2, map_one, one_mul]
end GlobalTheory.GaugeInt
