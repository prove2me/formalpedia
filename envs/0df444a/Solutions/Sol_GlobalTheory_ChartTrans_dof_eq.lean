-- Prove2me | solution 1 for GlobalTheory.ChartTrans.dof_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:07:13.857249+00:00
-- url     : https://prove2.me/submissions/4af1d3ac-0b6f-4d9a-92de-c91da1b4d0dc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
import Theorems.Thm_GlobalTheory_ChartTrans_pderiv_ev
import Theorems.Thm_GlobalTheory_ChartTrans_ev_sum
import Theorems.Thm_GlobalTheory_ChartTrans_vec1
import Theorems.Thm_GlobalTheory_ChartTrans_axis_GP
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_pt_self
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
open GlobalTheory GlobalTheory.ChartTrans
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.ChartTrans
theorem _root_.solution (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0)
    (hu : ∀ i, ev (n := 1) ![pt k (n := 1) d 0, 0] (F i) = (X ((0 : Fin 1), i) : PS k 1 d))
    (u : Fin d → k) (g : PS k 1 d) :
    Dof F u g = ∑ i, C (u i) *
      ev (n := 1) ![pt k (n := 1) d 0, 0] (pderiv k ((1 : Fin 2), i) (ev (n := 2) ![F] g)) := by
  have hF1 : ∀ j, GP ((![F] : Fin 1 → Pt k 2 d) j) := single_point_zero_constant hF
  have hS : ∀ h : PS k 1 d, ev (n := 1) ![pt k (n := 1) d 0, 0] (ev (n := 2) ![F] h) = h := by
    intro h
    rw [gt_ev_ev' _ _ axis_GP hF1, vec1]
    have : evP ![pt k (n := 1) d 0, 0] F = pt k (n := 1) d 0 := funext hu
    rw [this, gt_ev_pt_self]
  unfold Dof
  simp only [pderiv_ev _ hF1, Fin.sum_univ_one, ev_sum _ axis_GP, gt_ev_mul _ axis_GP, hS,
    Finset.mul_sum, Finset.sum_mul, Matrix.cons_val_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end GlobalTheory.ChartTrans
