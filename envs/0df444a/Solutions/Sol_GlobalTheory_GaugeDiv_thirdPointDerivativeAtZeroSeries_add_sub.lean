-- Prove2me | solution 1 for GlobalTheory.GaugeDiv.thirdPointDerivativeAtZeroSeries_add_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:46:24.332935+00:00
-- url     : https://prove2.me/submissions/293ad087-ddf1-4e7a-a0c7-22618f7489e9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral
import Theorems.Thm_GlobalTheory_QuadDeriv_hDown
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_sub


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
open GlobalTheory.QuadDeriv GlobalTheory.GaugeInt
open GlobalTheory GlobalTheory.GaugeDiv
variable {R k : Type} [CommRing R] [CommRing k] {φ : R →+* k} {d : ℕ}
namespace GlobalTheory.GaugeDiv
theorem _root_.solution (v : Fin d → k) (f g h : PS k 3 d) :
    dz3 v (f + g - h) = dz3 v f + dz3 v g - dz3 v h := by
  simp only [dz3, map_add, map_sub, gt_ev_add _ hDown, gt_ev_sub _ hDown, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
end GlobalTheory.GaugeDiv
