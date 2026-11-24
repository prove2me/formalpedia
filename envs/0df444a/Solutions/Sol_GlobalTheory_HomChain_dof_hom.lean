-- Prove2me | solution 1 for GlobalTheory.HomChain.dof_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:55:05.39163+00:00
-- url     : https://prove2.me/submissions/3519637e-3d7c-4926-b19a-c27324ba0dd4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_LawRightUnit
import Theorems.Thm_GlobalTheory_HomChain_law_right_unit
import Theorems.Thm_GlobalTheory_ChartTrans_axis_pderiv_comp
import Theorems.Thm_GlobalTheory_ChartTrans_dof_eq
import Theorems.Thm_GlobalTheory_ChartTrans_ev_C_mul
import Theorems.Thm_GlobalTheory_ChartTrans_ev_sum
import Theorems.Thm_GlobalTheory_ChartTrans_vec1
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
open GlobalTheory.ChartTrans
open GlobalTheory GlobalTheory.HomChain
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.HomChain
theorem _root_.solution (G G' : FGLaw k d) (α : Pt k 1 d) (hα : ∀ i, constantCoeff (α i) = 0)
    (hom : comp1 α (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      G'.add (comp1 α (pt k (n := 2) d 0)) (comp1 α (pt k (n := 2) d 1)))
    (u : Fin d → k) (g : PS k 1 d) :
    Dof G.F u (ev (n := 1) ![α] g) = ev (n := 1) ![α] (Dof G'.F ((dLin α).mulVec u) g) := by
  have hφ : GP α := hα
  have h0 : GP (comp1 α (pt k (n := 2) d 0)) := gp_comp1 α _ hφ (gp_pt 0)
  have h1 : GP (comp1 α (pt k (n := 2) d 1)) := gp_comp1 α _ hφ (gp_pt 1)
  have hΦ := pair_points_zero_constant h0 h1
  have hF : GP G.F := G.const
  have hF' : GP G'.F := G'.const
  have eF : G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1) = G.F := by
    funext i
    have e : (![pt k (n := 2) d 0, pt k (n := 2) d 1] : Fin 2 → Pt k 2 d) = pt k d := by
      funext j; fin_cases j <;> rfl
    change ev ![pt k (n := 2) d 0, pt k (n := 2) d 1] (G.F i) = _
    rw [e]
    exact congrFun (MvPowerSeries.subst_self (R := k) (σ := Fin 2 × Fin d)) (G.F i)
  have key : ev (n := 2) ![G.F] (ev (n := 1) ![α] g) =
      ev ![comp1 α (pt k (n := 2) d 0), comp1 α (pt k (n := 2) d 1)] (ev (n := 2) ![G'.F] g) := by
    rw [gt_ev_ev' _ _ (single_point_zero_constant hF) (single_point_zero_constant hφ), vec1, gt_ev_ev' _ _ hΦ (single_point_zero_constant hF'), vec1]
    have : evP ![G.F] α = evP ![comp1 α (pt k (n := 2) d 0), comp1 α (pt k (n := 2) d 1)] G'.F := by
      rw [eF] at hom
      exact hom
    rw [this]
  rw [dof_eq _ G.const (law_right_unit G), dof_eq _ G'.const (law_right_unit G'), key,
    ev_sum _ (single_point_zero_constant hφ)]
  simp only [axis_pderiv_comp α hφ, ev_C_mul _ (single_point_zero_constant hφ)]
  simp only [Matrix.mulVec, dotProduct, map_sum,
    map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end GlobalTheory.HomChain
