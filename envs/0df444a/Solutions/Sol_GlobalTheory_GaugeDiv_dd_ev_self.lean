-- Prove2me | solution 1 for GlobalTheory.GaugeDiv.dd_ev_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:49:10.819297+00:00
-- url     : https://prove2.me/submissions/ec7b8fc8-6959-4dbd-b140-836b9706e004

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral
import Theorems.Thm_GlobalTheory_QuadDeriv_ev_sum
import Theorems.Thm_GlobalTheory_QuadDeriv_pderiv_ev
import Theorems.Thm_GlobalTheory_QuadDeriv_pderiv_pt_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_mul
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
theorem _root_.solution (F : Pt k 2 d) (a : Fin 2) (v : Fin d → k) (f : PS k 1 d) :
    DD F a v (ev (n := 2) ![pt k d a] f) = ev (n := 2) ![pt k d a] (Dof F v f) := by
  have h : ∀ j, GP ((![pt k d a] : Fin 1 → Pt k 2 d) j) := single_point_zero_constant (gp_pt a)
  rw [DD, Dof, ev_sum _ h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gt_ev_mul _ h, pderiv_ev _ h, Fin.sum_univ_one]
  simp [pderiv_pt_self, dy]
end GlobalTheory.GaugeDiv
