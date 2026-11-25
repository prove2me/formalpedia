-- Prove2me | solution 1 for GlobalTheory.GaugeDiv.dd_ev_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:51:31.301827+00:00
-- url     : https://prove2.me/submissions/5002cebc-cc07-41e9-842f-36194230f0f1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral
import Theorems.Thm_GlobalTheory_QuadDeriv_pderiv_ev_eq_zero
import Theorems.Thm_GlobalTheory_QuadDeriv_pderiv_pt_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant


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
theorem _root_.solution (F : Pt k 2 d) {a b : Fin 2} (hab : b ≠ a) (v : Fin d → k) (f : PS k 1 d) :
    DD F a v (ev (n := 2) ![pt k d b] f) = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [pderiv_ev_eq_zero _ (single_point_zero_constant (gp_pt b)), mul_zero]
  intro j' i
  fin_cases j'
  exact pderiv_pt_ne hab _ _
end GlobalTheory.GaugeDiv
