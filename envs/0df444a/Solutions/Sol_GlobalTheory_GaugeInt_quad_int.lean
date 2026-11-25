-- Prove2me | solution 1 for GlobalTheory.GaugeInt.quad_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:12:05.847923+00:00
-- url     : https://prove2.me/submissions/e42e7adc-793f-4a2f-b7a2-ce188c7a308a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Theorems.Thm_GlobalTheory_GaugeInt_IP_gp
import Theorems.Thm_GlobalTheory_GaugeInt_IP_int
import Theorems.Thm_GlobalTheory_GaugeInt_ip_pt
import Theorems.Thm_GlobalTheory_GaugeInt_ip3
import Theorems.Thm_GlobalTheory_GaugeInt_int_C
import Theorems.Thm_GlobalTheory_GaugeInt_ip_comp1
import Theorems.Thm_GlobalTheory_GaugeInt_ip_addOf
import Theorems.Thm_GlobalTheory_GaugeInt_di_ev
import Theorems.Thm_GlobalTheory_GaugeInt_dy_sub
import Theorems.Thm_GlobalTheory_GaugeInt_dy_int
import Theorems.Thm_GlobalTheory_GaugeInt_lin_int
import Theorems.Thm_GlobalTheory_GaugeInt_dof_int
import Theorems.Thm_GlobalTheory_GaugeInt_dof_sub
import Theorems.Thm_GlobalTheory_GaugeInt_dof_almost_additive
import Theorems.Thm_GlobalTheory_GaugeInt_ev_defL
import Theorems.Thm_GlobalTheory_GaugeInt_ev_defR
import Theorems.Thm_GlobalTheory_GaugeInt_dz_defL
import Theorems.Thm_GlobalTheory_GaugeInt_dz_defR
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_comm
import Theorems.Thm_GlobalTheory_QuadDeriv_addOf_pt
import Theorems.Thm_GlobalTheory_QuadDeriv_const_pderiv
import Theorems.Thm_GlobalTheory_QuadDeriv_const_pderiv_pderiv
import Theorems.Thm_GlobalTheory_QuadDeriv_constantCoeff_pderiv_formalSubst_two
import Theorems.Thm_GlobalTheory_QuadDeriv_dof_eq
import Theorems.Thm_GlobalTheory_QuadDeriv_dy_add
import Theorems.Thm_GlobalTheory_QuadDeriv_ev_zero_pts
import Theorems.Thm_GlobalTheory_QuadDeriv_formalComp_zero_left_point
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_first_coordinate
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_formalSubst_two
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_second_coordinate
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_subst_first_point
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_subst_second_point
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSubst_single_of_formalSubst_two
import Theorems.Thm_GlobalTheory_QuadDeriv_hX0
import Theorems.Thm_GlobalTheory_QuadDeriv_pderiv_pt_self
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_C_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_zero


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
open GlobalTheory.QuadDeriv
open GlobalTheory GlobalTheory.GaugeInt
variable {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {d : ℕ}
variable {φ}
namespace GlobalTheory.GaugeInt
theorem _root_.solution {F : Pt k 2 d} (iF : IP φ F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    {w : Pt k 1 d} (iw : IP φ w)
    (hom : comp1 w F = addOf F (comp1 w (pt k (n := 2) d 0)) (comp1 w (pt k (n := 2) d 1)))
    (g : PS k 2 d) (c1 : ∀ s, constantCoeff (pderiv k s g) = 0)
    (hl : DI φ (defL F g)) (hr : DI φ (defR F g)) {u v : Fin d → k} (hu : ∀ i, u i ∈ φ.range)
    (hv : ∀ i, v i ∈ φ.range) :
    Dof F u (Dof F v (ev (n := 1) ![pt k d 0, w] g)) -
      C (∑ j, (∑ l, v l * coeff (Finsupp.single ((0 : Fin 1), l) 1) (w j)) *
          (∑ i, u i * coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g) +
        ∑ i, v i * ∑ l, u l * ∑ j,
          coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g *
            coeff (Finsupp.single ((0 : Fin 1), l) 1) (w j)) ∈ IntS φ 1 d := by
  have hF := iF.gp
  have hw := iw.gp
  have ip0 : IP φ (pt k (n := 2) d 0) := ip_pt 0
  have ip1' : IP φ (pt k (n := 2) d 1) := ip_pt 1
  have iw0 := ip_comp1 iw ip0
  have iw1 := ip_comp1 iw ip1'
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have q0 : GP (pt k (n := 1) d 0) := gp_pt 0
  have w0 := gp_comp1 w _ hw p0
  have w1 := gp_comp1 w _ hw p1
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
  obtain ⟨E, hE, hD⟩ : ∃ E ∈ IntS φ 1 d, Dof F v (ev (n := 1) ![pt k d 0, w] g) =
      ∑ j, C (lin v (w j)) * ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), j) g) +
      ∑ i, C (v i) * ev (n := 1) ![0, w] (pderiv k ((0 : Fin 2), i) g) - E := by
    refine ⟨_, add_mem (add_mem (dy_int hv (di_ev (ip3 ip0 ip1' (ip_addOf iF iw0 iw1)) hl))
      (dy_int hv (di_ev (ip3 ip0 iw0 iw1) hr))) (dy_int hv (di_ev (ip3 ip1' iw0 iw1) hr)), ?_⟩
    rw [dof_eq F hF hU, formalSubst_single_of_formalSubst_two F hF _ _ q0 hw, gt_comp1_pt F hF, hom,
      ev_defL F hF g _ _ _ p0 p1 (gp_addOf F hF _ _ w0 w1), ev_defR F hF g _ _ _ p0 w0 w1,
      ev_defR F hF g _ _ _ p1 w0 w1, addOf_pt]
    simp only [dy_sub, dy_add]
    rw [formalSecondPointDerivative_formalSubst_two v _ _ p0 w0, formalSecondPointDerivative_formalSubst_two v _ _ p0 w1, formalSecondPointDerivative_formalSubst_two v _ _ p1 w0, formalSecondPointDerivative_formalSubst_two v _ _ p1 w1]
    simp only [e0, e1, f0, f1, g0, g1, formalSecondPointDerivative_first_coordinate, formalSecondPointDerivative_second_coordinate, z, zero_mul, mul_zero, Finset.sum_const_zero,
      zero_add, add_zero]
    ring
  have hb : ∀ j, Dof F u (ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), j) g)) -
      C (∑ i, u i * coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g)
        ∈ IntS φ 1 d := by
    intro j
    have h := dof_almost_additive hF hU hu (ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), j) g)) (by
      rw [formalSubst_single_of_formalSubst_two _ hF _ _ q0 gp_zero₂, formalSubst_single_of_formalSubst_two _ p0 _ _ q0 gp_zero₂,
        formalSubst_single_of_formalSubst_two _ p1 _ _ q0 gp_zero₂, gt_comp1_pt _ hF, gt_comp1_pt _ p0, gt_comp1_pt _ p1,
        formalComp_zero_left_point _ hF, formalComp_zero_left_point _ p0, formalComp_zero_left_point _ p1]
      have := dz_defL iF g hl ip0 ip1' j
      rwa [addOf_pt] at this)
    convert h using 3
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [constantCoeff_pderiv_formalSubst_two _ _ q0 gp_zero₂]
    simp [pderiv_pt_self, const_pderiv_pderiv, apply_ite]
  have ha : ∀ i, Dof F u (ev (n := 1) ![0, w] (pderiv k ((0 : Fin 2), i) g)) -
      C (∑ l, u l * ∑ j,
        coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g *
          coeff (Finsupp.single ((0 : Fin 1), l) 1) (w j)) ∈ IntS φ 1 d := by
    intro i
    have h := dof_almost_additive hF hU hu (ev (n := 1) ![0, w] (pderiv k ((0 : Fin 2), i) g)) (by
      rw [formalSubst_single_of_formalSubst_two _ hF _ _ gp_zero₂ hw, formalSubst_single_of_formalSubst_two _ p0 _ _ gp_zero₂ hw,
        formalSubst_single_of_formalSubst_two _ p1 _ _ gp_zero₂ hw,
        formalComp_zero_left_point _ hF, formalComp_zero_left_point _ p0, formalComp_zero_left_point _ p1, hom]
      exact dz_defR iF g hr iw0 iw1 i)
    convert h using 3
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [constantCoeff_pderiv_formalSubst_two _ _ gp_zero₂ hw]
    simp only [Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero, zero_add]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.FormalCalc.pderiv_comm, const_pderiv_pderiv, const_pderiv]
  have h := sub_mem (add_mem
    (sum_mem (t := Finset.univ) fun j _ => mul_mem (int_C (lin_int hv (iw.int j))) (hb j))
    (sum_mem (t := Finset.univ) fun i _ => mul_mem (int_C (hv i)) (ha i))) (dof_int iF hu hE)
  convert h using 1
  rw [hD, dof_sub, GE.dof_add, GE.dof_sum, GE.dof_sum]
  simp only [GE.dof_C_mul, mul_sub, Finset.sum_sub_distrib, ← map_mul, ← map_sum, map_add, lin,
    const_pderiv]
  ring
end GlobalTheory.GaugeInt
