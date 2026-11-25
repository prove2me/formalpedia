-- Prove2me | solution 1 for GlobalTheory.QuadDeriv.quad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:48:03.092796+00:00
-- url     : https://prove2.me/submissions/2b9e85bd-7d5f-4cce-973b-14996a4bc3f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Theorems.Thm_GlobalTheory_QuadDeriv_pderiv_pt_self
import Theorems.Thm_GlobalTheory_QuadDeriv_ev_zero_pts
import Theorems.Thm_GlobalTheory_QuadDeriv_const_pderiv
import Theorems.Thm_GlobalTheory_QuadDeriv_hX0
import Theorems.Thm_GlobalTheory_QuadDeriv_dy_add
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_formalSubst_two
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_first_coordinate
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_second_coordinate
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_subst_first_point
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_subst_second_point
import Theorems.Thm_GlobalTheory_QuadDeriv_dof_eq
import Theorems.Thm_GlobalTheory_QuadDeriv_dof_additive
import Theorems.Thm_GlobalTheory_QuadDeriv_addOf_pt
import Theorems.Thm_GlobalTheory_QuadDeriv_add_left
import Theorems.Thm_GlobalTheory_QuadDeriv_add_right
import Theorems.Thm_GlobalTheory_QuadDeriv_dz_add_left
import Theorems.Thm_GlobalTheory_QuadDeriv_dz_add_right
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSubst_single_of_formalSubst_two
import Theorems.Thm_GlobalTheory_QuadDeriv_formalComp_zero_left_point
import Theorems.Thm_GlobalTheory_QuadDeriv_const_pderiv_pderiv
import Theorems.Thm_GlobalTheory_QuadDeriv_constantCoeff_pderiv_formalSubst_two
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_comm
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_C_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_eq_zero_of_axes
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev_eq
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
open GlobalTheory GlobalTheory.QuadDeriv
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.QuadDeriv
theorem _root_.solution (F : Fin d → PS k 2 d) (hF : GP F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    (w : Pt k 1 d) (hw : GP w)
    (hom : comp1 w F = addOf F (comp1 w (pt k (n := 2) d 0)) (comp1 w (pt k (n := 2) d 1)))
    (g : PS k 2 d) (h0 : ev (n := 1) ![0, pt k d 0] g = 0) (h1 : ev (n := 1) ![pt k d 0, 0] g = 0)
    (hl : ev (n := 3) ![pt k d 0, pt k d 2] g + ev (n := 3) ![pt k d 1, pt k d 2] g =
      ev (n := 3) ![addOf F (pt k d 0) (pt k d 1), pt k d 2] g)
    (hr : ev (n := 3) ![pt k d 0, pt k d 1] g + ev (n := 3) ![pt k d 0, pt k d 2] g =
      ev (n := 3) ![pt k d 0, addOf F (pt k d 1) (pt k d 2)] g) :
    constantCoeff (ev (n := 1) ![pt k d 0, w] g) = 0 ∧
    (∀ u, constantCoeff (Dof F u (ev (n := 1) ![pt k d 0, w] g)) = 0) ∧
    ∀ u v, Dof F u (Dof F v (ev (n := 1) ![pt k d 0, w] g)) =
      C (∑ j, (∑ l, v l * coeff (Finsupp.single ((0 : Fin 1), l) 1) (w j)) *
          (∑ i, u i * coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g) +
        ∑ i, v i * ∑ l, u l * ∑ j,
          coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g *
            coeff (Finsupp.single ((0 : Fin 1), l) 1) (w j)) := by
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have q0 : GP (pt k (n := 1) d 0) := gp_pt 0
  have w0 := gp_comp1 w _ hw p0
  have w1 := gp_comp1 w _ hw p1
  have c0 : constantCoeff g = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact coeff_eq_zero_of_axes g h0 h1 0 (by simp)
  have c1 : ∀ s, constantCoeff (pderiv k s g) = 0 := fun s => by
    rw [const_pderiv]
    exact coeff_eq_zero_of_axes g h0 h1 _ (by simp)
  have e0 : evP (n := 1) ![pt k d 0, 0] (pt k d 0) = pt k d 0 := evP_pt _ hX0 0
  have e1 : evP (n := 1) ![pt k d 0, 0] (pt k d 1) = 0 := evP_pt _ hX0 1
  have f0 : evP (n := 1) ![pt k d 0, 0] (comp1 w (pt k d 0)) = w := by
    rw [evP_comp1 _ hX0 _ _ p0, e0, gt_comp1_pt_right]
  have f1 : evP (n := 1) ![pt k d 0, 0] (comp1 w (pt k d 1)) = 0 := by
    rw [evP_comp1 _ hX0 _ _ p1, e1, gt_comp1_zero w hw]
  have g0 : ∀ v i, dy v (comp1 w (pt k d 0) i) = 0 := fun v i => formalSecondPointDerivative_subst_first_point v _
  have g1 : ∀ v i, dy v (comp1 w (pt k d 1) i) = C (lin v (w i)) := fun v i => formalSecondPointDerivative_subst_second_point v _
  have z : ∀ s, ev (n := 1) ![0, 0] (pderiv k s g) = 0 := fun s => by
    rw [ev_zero_pts _ (by intro j; fin_cases j <;> rfl), c1, map_zero]
  have hD : ∀ v, Dof F v (ev (n := 1) ![pt k d 0, w] g) =
      ∑ j, C (lin v (w j)) * ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), j) g) +
      ∑ i, C (v i) * ev (n := 1) ![0, w] (pderiv k ((0 : Fin 2), i) g) := by
    intro v
    rw [dof_eq F hF hU, formalSubst_single_of_formalSubst_two F hF _ _ q0 hw, gt_comp1_pt F hF, hom]
    have : ev ![F, addOf F (comp1 w (pt k (n := 2) d 0)) (comp1 w (pt k (n := 2) d 1))] g =
        ev ![addOf F (pt k d 0) (pt k d 1),
          addOf F (comp1 w (pt k (n := 2) d 0)) (comp1 w (pt k (n := 2) d 1))] g := by
      rw [addOf_pt]
    rw [this, add_left F hF g hl _ _ _ p0 p1 (gp_addOf F hF _ _ w0 w1),
      add_right F hF g hr _ _ _ p0 w0 w1, add_right F hF g hr _ _ _ p1 w0 w1,
      dy_add, dy_add, dy_add, formalSecondPointDerivative_formalSubst_two v _ _ p0 w0, formalSecondPointDerivative_formalSubst_two v _ _ p0 w1, formalSecondPointDerivative_formalSubst_two v _ _ p1 w0,
      formalSecondPointDerivative_formalSubst_two v _ _ p1 w1]
    simp only [e0, e1, f0, f1, g0, g1, formalSecondPointDerivative_first_coordinate, formalSecondPointDerivative_second_coordinate, z, zero_mul, mul_zero, Finset.sum_const_zero,
      zero_add, add_zero]
  refine ⟨by rw [gt_const_ev_eq _ (pair_points_zero_constant q0 hw), c0], fun u => ?_, fun u v => ?_⟩
  · rw [hD]
    simp only [map_add, map_sum, map_mul, gt_const_ev_eq _ hX0,
      gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ hw), c1, mul_zero, Finset.sum_const_zero, add_zero]
  · have hb : ∀ j, Dof F u (ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), j) g)) =
        C (∑ i, u i * coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g) := by
      intro j
      rw [dof_additive F hF hU]
      · congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [constantCoeff_pderiv_formalSubst_two _ _ q0 gp_zero₂]
        simp [pderiv_pt_self, const_pderiv_pderiv, apply_ite]
      · rw [formalSubst_single_of_formalSubst_two _ hF _ _ q0 gp_zero₂, formalSubst_single_of_formalSubst_two _ p0 _ _ q0 gp_zero₂,
          formalSubst_single_of_formalSubst_two _ p1 _ _ q0 gp_zero₂, gt_comp1_pt _ hF, gt_comp1_pt _ p0, gt_comp1_pt _ p1,
          formalComp_zero_left_point _ hF, formalComp_zero_left_point _ p0, formalComp_zero_left_point _ p1,
          ← dz_add_left F hF g hl _ _ p0 p1, addOf_pt]
    have ha : ∀ i, Dof F u (ev (n := 1) ![0, w] (pderiv k ((0 : Fin 2), i) g)) =
        C (∑ l, u l * ∑ j,
          coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g *
            coeff (Finsupp.single ((0 : Fin 1), l) 1) (w j)) := by
      intro i
      rw [dof_additive F hF hU]
      · congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [constantCoeff_pderiv_formalSubst_two _ _ gp_zero₂ hw]
        simp only [Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero, zero_add]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [GlobalTheory.FormalCalc.pderiv_comm, const_pderiv_pderiv, const_pderiv]
      · rw [formalSubst_single_of_formalSubst_two _ hF _ _ gp_zero₂ hw, formalSubst_single_of_formalSubst_two _ p0 _ _ gp_zero₂ hw,
          formalSubst_single_of_formalSubst_two _ p1 _ _ gp_zero₂ hw,
          formalComp_zero_left_point _ hF, formalComp_zero_left_point _ p0, formalComp_zero_left_point _ p1,
          ← dz_add_right F hF g hr _ _ w0 w1, hom]
    rw [hD, GE.dof_add, GE.dof_sum, GE.dof_sum]
    simp only [GE.dof_C_mul, ha, hb, ← map_mul, ← map_sum, ← map_add, lin, const_pderiv]
end GlobalTheory.QuadDeriv
