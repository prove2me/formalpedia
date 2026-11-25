-- Prove2me | solution 1 for GlobalTheory.quadDeriv_of_biadditive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:56:01.989801+00:00
-- url     : https://prove2.me/submissions/78a34f62-f3f6-4175-8908-21eb39016ce4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Theorems.Thm_GlobalTheory_QuadDeriv_addOf_pt
import Theorems.Thm_GlobalTheory_QuadDeriv_quad
import Theorems.Thm_GlobalTheory_QuadDeriv_baseChange_pt
import Theorems.Thm_GlobalTheory_QuadDeriv_baseChange_comp1
import Theorems.Thm_GlobalTheory_QuadDeriv_baseChange_addOf
import Theorems.Thm_GlobalTheory_QuadDeriv_constantCoeff_mapP_eq_zero
import Theorems.Thm_GlobalTheory_QuadDeriv_unit_right
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt_right


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
open GlobalTheory
open QuadDeriv
namespace GlobalTheory
theorem _root_.solution : G2.QuadraticFormDerivatives := by
  intro R _ d O _ _ k _ _ _ B g hg w0
  obtain ⟨h0, h1, hl, hr, -⟩ := hg
  have eF : B.FK k = mapP (algebraMap R k) B.G.F := rfl
  have ew : B.actK k w0 = mapP (algebraMap R k) (B.A.act w0) := rfl
  have hF : GP (B.FK k) := constantCoeff_mapP_eq_zero _ _ B.G.const
  have hw : GP (B.actK k w0) := constantCoeff_mapP_eq_zero _ _ (B.A.const w0)
  have hU : evP (n := 1) ![pt k d 0, 0] (B.FK k) = pt k d 0 := by
    have := congrArg (mapP (algebraMap R k)) (unit_right B.G)
    rw [baseChange_addOf _ _ _ _ (gp_pt 0) gp_zero₂, baseChange_pt,
      show mapP (algebraMap R k) (0 : Pt R 1 d) = 0 from funext fun i => map_zero _] at this
    exact this
  have hom : comp1 (B.actK k w0) (B.FK k) = addOf (B.FK k) (comp1 (B.actK k w0) (pt k (n := 2) d 0))
      (comp1 (B.actK k w0) (pt k (n := 2) d 1)) := by
    have := congrArg (mapP (algebraMap R k)) (B.A.hom w0)
    rw [FGLaw.add, FGLaw.add, addOf_pt, baseChange_comp1 _ _ _ B.G.const,
      baseChange_addOf _ _ _ _ (gp_comp1 _ _ (B.A.const w0) (gp_pt 0))
        (gp_comp1 _ _ (B.A.const w0) (gp_pt 1)),
      baseChange_comp1 _ _ _ (gp_pt 0), baseChange_comp1 _ _ _ (gp_pt 1), baseChange_pt, baseChange_pt] at this
    exact this
  obtain ⟨a, b, c⟩ := quad (B.FK k) hF hU (B.actK k w0) hw hom g h0 h1 hl hr
  rw [gt_comp1_pt_right]
  refine ⟨a, b, fun u v => ?_⟩
  rw [c]
  congr 1
  simp only [dotProduct, Matrix.mulVec, bilinPart, dAct, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => by ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
end GlobalTheory
