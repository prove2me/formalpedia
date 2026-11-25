-- Prove2me | solution 1 for GlobalTheory.DerivEndo.dof_endo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:23:12.252937+00:00
-- url     : https://prove2.me/submissions/18065dbc-9929-4884-a56b-991847424189

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ContinuousPderivDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvariantDerivAlongEndo
import Theorems.Thm_GlobalTheory_ChartTrans_axis_pderiv_comp
import Theorems.Thm_GlobalTheory_ChartTrans_dof_eq
import Theorems.Thm_GlobalTheory_ChartTrans_ev_C_mul
import Theorems.Thm_GlobalTheory_ChartTrans_ev_sum
import Theorems.Thm_GlobalTheory_ChartTrans_vec1
import Theorems.Thm_GlobalTheory_QuadDeriv_dof_eq
import Theorems.Thm_GlobalTheory_QuadDeriv_ev_sum
import Theorems.Thm_GlobalTheory_QuadDeriv_vec1
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
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
open GlobalTheory GlobalTheory.DerivEndo
open GlobalTheory.ChartTrans
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.DerivEndo
theorem _root_.solution (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0)
    (hu : ∀ i, ev (n := 1) ![pt k (n := 1) d 0, 0] (F i) = (X ((0 : Fin 1), i) : PS k 1 d))
    (φ : Pt k 1 d) (hφ : GP φ)
    (hom : comp1 φ F = addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1)))
    (u : Fin d → k) (g : PS k 1 d) :
    Dof F u (ev (n := 1) ![φ] g) = ev (n := 1) ![φ] (Dof F ((dLin φ).mulVec u) g) := by
  have h0 : GP (comp1 φ (pt k (n := 2) d 0)) := gp_comp1 φ _ hφ (gp_pt 0)
  have h1 : GP (comp1 φ (pt k (n := 2) d 1)) := gp_comp1 φ _ hφ (gp_pt 1)
  have hΦ := pair_points_zero_constant h0 h1
  have key : ev (n := 2) ![F] (ev (n := 1) ![φ] g) =
      ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] (ev (n := 2) ![F] g) := by
    rw [gt_ev_ev' _ _ (single_point_zero_constant hF) (single_point_zero_constant hφ), vec1, gt_ev_ev' _ _ hΦ (single_point_zero_constant hF), vec1]
    have : evP ![F] φ = evP ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] F := hom
    rw [this]
  rw [dof_eq _ hF hu, dof_eq F hF hu, key, ChartTrans.ev_sum _ (single_point_zero_constant hφ)]
  simp only [axis_pderiv_comp φ hφ, ChartTrans.ev_C_mul _ (single_point_zero_constant hφ)]
  simp only [Matrix.mulVec, dotProduct, map_sum,
    map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end GlobalTheory.DerivEndo
