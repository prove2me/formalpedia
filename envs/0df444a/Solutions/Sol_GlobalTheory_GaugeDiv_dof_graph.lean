-- Prove2me | solution 1 for GlobalTheory.GaugeDiv.dof_graph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:55:27.999816+00:00
-- url     : https://prove2.me/submissions/c351804c-1f4a-4e33-87e8-5b477437bf77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral
import Theorems.Thm_GlobalTheory_GaugeDiv_ev_formalSecondPointDerivative
import Theorems.Thm_GlobalTheory_QuadDeriv_dof_eq
import Theorems.Thm_GlobalTheory_QuadDeriv_ev_C
import Theorems.Thm_GlobalTheory_QuadDeriv_ev_sum
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_formalSubst_two
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_subst_first_point
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_subst_second_point
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSubst_single_of_formalSubst_two
import Theorems.Thm_GlobalTheory_QuadDeriv_hX0
import Theorems.Thm_GlobalTheory_QuadDeriv_vec1
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_pt_self
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
open GlobalTheory.QuadDeriv GlobalTheory.GaugeInt
open GlobalTheory GlobalTheory.GaugeDiv
variable {R k : Type} [CommRing R] [CommRing k] {φ : R →+* k} {d : ℕ}
namespace GlobalTheory.GaugeDiv
theorem _root_.solution {F : Pt k 2 d} (hF : GP F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    {w : Pt k 1 d} (hw : GP w)
    (hom : comp1 w F = addOf F (comp1 w (pt k (n := 2) d 0)) (comp1 w (pt k (n := 2) d 1)))
    (u v : Fin d → k) (N : ℕ) (huv : ∀ i, lin u (w i) = N * v i) (G : PS k 2 d) :
    Dof F u (ev (n := 1) ![pt k d 0, w] G) =
      ev (n := 1) ![pt k d 0, w] (DD F 0 u G + N * DD F 1 v G) := by
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have q0 : GP (pt k (n := 1) d 0) := gp_pt 0
  have w0 := gp_comp1 w _ hw p0
  have w1 := gp_comp1 w _ hw p1
  have hV := pair_points_zero_constant q0 hw
  have e0 : evP (n := 1) ![pt k d 0, 0] (pt k d 0) = pt k d 0 := evP_pt _ hX0 0
  have e1 : evP (n := 1) ![pt k d 0, 0] (pt k d 1) = 0 := evP_pt _ hX0 1
  have f0 : evP (n := 1) ![pt k d 0, 0] (comp1 w (pt k d 0)) = w := by
    rw [evP_comp1 _ hX0 _ _ p0, e0, gt_comp1_pt_right]
  have f1 : evP (n := 1) ![pt k d 0, 0] (comp1 w (pt k d 1)) = 0 := by
    rw [evP_comp1 _ hX0 _ _ p1, e1, gt_comp1_zero w hw]
  have f2 : evP (n := 1) ![pt k d 0, 0] (comp1 w F) = w := by
    rw [evP_comp1 _ hX0 _ _ hF, hU, gt_comp1_pt_right]
  have g0 : ∀ i, dy u (comp1 w (pt k d 0) i) = 0 := fun i => formalSecondPointDerivative_subst_first_point u _
  have g1 : ∀ i, dy u (comp1 w (pt k d 1) i) = C (lin u (w i)) := fun i => formalSecondPointDerivative_subst_second_point u _
  have key : ∀ j, dy u (comp1 w F j) = N * ev ![w] (dy v (F j)) := by
    intro j
    rw [hom, addOf, formalSecondPointDerivative_formalSubst_two u _ _ w0 w1, ev_formalSecondPointDerivative w hw]
    simp only [g0, g1, f0, f1, huv, zero_mul, Finset.sum_const_zero, zero_add, Finset.mul_sum, map_mul,
      map_natCast, mul_assoc]
  have a0 : ∀ f : PS k 1 d, ev (n := 1) ![pt k d 0, w] (ev (n := 2) ![pt k d 0] f) = f := fun f => by
    rw [gt_ev_ev' _ _ hV (single_point_zero_constant p0), vec1, evP_pt _ hV]
    exact gt_ev_pt_self f
  have a1 : ∀ f : PS k 1 d, ev (n := 1) ![pt k d 0, w] (ev (n := 2) ![pt k d 1] f) = ev ![w] f :=
    fun f => by
      rw [gt_ev_ev' _ _ hV (single_point_zero_constant p1), vec1, evP_pt _ hV]
      rfl
  have hN : ev (n := 1) ![pt k d 0, w] (N : PS k 2 d) = N := by
    rw [← map_natCast (C : k →+* PS k 2 d), ev_C, map_natCast]
  rw [dof_eq F hF hU, formalSubst_single_of_formalSubst_two F hF _ _ q0 hw, gt_comp1_pt F hF,
    formalSecondPointDerivative_formalSubst_two u _ _ hF (gp_comp1 w _ hw hF), hU, f2, gt_ev_add _ hV, gt_ev_mul _ hV, hN, DD, DD,
    ev_sum _ hV, ev_sum _ hV]
  simp only [gt_ev_mul _ hV, a0, a1, key, Finset.mul_sum, mul_assoc]
end GlobalTheory.GaugeDiv
