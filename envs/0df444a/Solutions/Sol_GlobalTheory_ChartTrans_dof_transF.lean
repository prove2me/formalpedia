-- Prove2me | solution 1 for GlobalTheory.ChartTrans.dof_transF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:45:25.832897+00:00
-- url     : https://prove2.me/submissions/6e21562c-821b-483f-bf24-2628d8f0193a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
import Theorems.Thm_GlobalTheory_ChartTrans_ev_sum
import Theorems.Thm_GlobalTheory_ChartTrans_ev_C_mul
import Theorems.Thm_GlobalTheory_ChartTrans_vec1
import Theorems.Thm_GlobalTheory_ChartTrans_axis_GP
import Theorems.Thm_GlobalTheory_ChartTrans_dof_eq
import Theorems.Thm_GlobalTheory_ChartTrans_axis_pderiv_comp
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant
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
    (φ φi : Pt k 1 d) (hinv : IsInvPair φ φi) (u : Fin d → k) (g : PS k 1 d) :
    Dof (transF F φ φi) u (ev (n := 1) ![φ] g) =
      ev (n := 1) ![φ] (Dof F ((dLin φ).mulVec u) g) := by
  have hφ : GP φ := hinv.1
  have hφi : GP φi := hinv.2.1
  have h0 : GP (comp1 φ (pt k (n := 2) d 0)) := gp_comp1 φ _ hφ (gp_pt 0)
  have h1 : GP (comp1 φ (pt k (n := 2) d 1)) := gp_comp1 φ _ hφ (gp_pt 1)
  have hΦ := pair_points_zero_constant h0 h1
  have hA := gp_addOf F hF _ _ h0 h1
  have eF : transF F φ φi =
      comp1 φi (addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))) := rfl
  have hF' : GP (transF F φ φi) := eF ▸ gp_comp1 φi _ hφi hA
  have hax : addOf F φ 0 = φ := by
    have e1 : addOf F (pt k (n := 1) d 0) 0 = pt k (n := 1) d 0 := funext hu
    have e2 := congrArg (evP ![φ]) e1
    rwa [evP_addOf _ (single_point_zero_constant hφ) _ _ _ (gp_pt 0) gp_zero₂, evP_pt _ (single_point_zero_constant hφ),
      evP_zero _ (single_point_zero_constant hφ)] at e2
  have hu' : evP ![pt k (n := 1) d 0, 0] (transF F φ φi) = pt k (n := 1) d 0 := by
    rw [eF, evP_comp1 _ axis_GP _ _ hA, evP_addOf _ axis_GP _ _ _ h0 h1,
      evP_comp1 _ axis_GP φ _ (gp_pt 0), evP_comp1 _ axis_GP φ _ (gp_pt 1),
      evP_pt _ axis_GP, evP_pt _ axis_GP]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [gt_comp1_pt_right, gt_comp1_zero φ hφ, hax, hinv.2.2.2]
  have key : ev (n := 2) ![transF F φ φi] (ev (n := 1) ![φ] g) =
      ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] (ev (n := 2) ![F] g) := by
    rw [gt_ev_ev' _ _ (single_point_zero_constant hF') (single_point_zero_constant hφ), vec1, gt_ev_ev' _ _ hΦ (single_point_zero_constant hF), vec1]
    have : evP ![transF F φ φi] φ = evP ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] F :=
      gt_comp_inv hinv _ hA
    rw [this]
  rw [dof_eq _ hF' (congrFun hu'), dof_eq F hF hu, key, ev_sum _ (single_point_zero_constant hφ)]
  simp only [axis_pderiv_comp φ hφ, ev_C_mul _ (single_point_zero_constant hφ)]
  simp only [Matrix.mulVec, dotProduct, map_sum,
    map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end GlobalTheory.ChartTrans
