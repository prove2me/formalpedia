-- Prove2me | solution 1 for GlobalTheory.GaugeDiv.thirdPointDerivativeAtZeroSeries_twoPointLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:47:15.022499+00:00
-- url     : https://prove2.me/submissions/6e7debaf-f8be-454e-b6a6-643c93f10da8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral
import Theorems.Thm_GlobalTheory_QuadDeriv_hDown
import Theorems.Thm_GlobalTheory_QuadDeriv_pderiv_ev_eq_zero
import Theorems.Thm_GlobalTheory_QuadDeriv_pderiv_up
import Theorems.Thm_P2M_GlobalTheory_QuadDeriv_constantCoeff_up_eq_zero__83ee02ec8fbc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant


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
theorem _root_.solution (v : Fin d → k) (g : PS k 2 d) :
    dz3 v (ev ![up (pt k d 0), up (pt k d 1)] g) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [pderiv_ev_eq_zero _ (pair_points_zero_constant (constantCoeff_up_eq_zero₂ (gp_pt 0)) (constantCoeff_up_eq_zero₂ (gp_pt 1))), gt_ev_zero _ hDown,
    mul_zero]
  intro j l
  fin_cases j <;> exact pderiv_up _ _ _
end GlobalTheory.GaugeDiv
