-- Prove2me | solution 1 for GlobalTheory.GaugeDiv.thirdPointDerivativeAtZeroSeries_addOf_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:58:31.326814+00:00
-- url     : https://prove2.me/submissions/29f07221-9b4b-4ccd-94fc-9d5e4bd911db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral
import Theorems.Thm_GlobalTheory_GaugeDiv_ev_formalSecondPointDerivative
import Theorems.Thm_GlobalTheory_GaugeDiv_down_addOf
import Theorems.Thm_GlobalTheory_GaugeDiv_ev_pts
import Theorems.Thm_GlobalTheory_QuadDeriv_down_up
import Theorems.Thm_GlobalTheory_QuadDeriv_dz_right
import Theorems.Thm_GlobalTheory_QuadDeriv_ev_pderiv_ev
import Theorems.Thm_GlobalTheory_QuadDeriv_hDown
import Theorems.Thm_GlobalTheory_QuadDeriv_pderiv_up
import Theorems.Thm_P2M_GlobalTheory_QuadDeriv_constantCoeff_up_eq_zero__83ee02ec8fbc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eval_pair_points
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
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
theorem _root_.solution {F : Pt k 2 d} (hF : GP F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    (v : Fin d → k) (g : PS k 2 d) :
    dz3 v (ev ![addOf F (up (pt k d 0)) (pt k d 2), up (pt k d 1)] g) = DD F 0 v g := by
  have hA := pair_points_zero_constant (gp_addOf F hF _ _ (constantCoeff_up_eq_zero₂ (gp_pt (k := k) (d := d) 0)) (gp_pt 2))
    (constantCoeff_up_eq_zero₂ (gp_pt 1))
  simp only [dz3, DD, ev_pderiv_ev _ hDown _ hA, Fin.sum_univ_two, eval_pair_points, down_up, down_addOf hU,
    Matrix.cons_val_zero, Matrix.cons_val_one, pderiv_up, gt_ev_zero _ hDown, mul_zero,
    Finset.sum_const_zero, add_zero, ev_pts, addOf, dz_right _ _ (gp_pt 0),
    ev_formalSecondPointDerivative _ (gp_pt 0), Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
end GlobalTheory.GaugeDiv
