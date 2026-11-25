-- Prove2me | solution 1 for GlobalTheory.JetSer.IntTrans.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:54:51.304833+00:00
-- url     : https://prove2.me/submissions/8273204d-f8aa-4525-b765-554f6c46c1d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RelatedMap
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_expS_zero
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_solve_exp
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_expS_nsmul
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_unit_right
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_constantCoeff_logS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eq_zero_of_exp_eq_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_log
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gauge_transformation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_expS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_expS_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_map_id
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.IntTrans
variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}
namespace GlobalTheory.JetSer.IntTrans
theorem _root_.solution (hN : NabTransSt) {O : Type} [CommRing O] [StarRing O] {B B' : FB k d O} {φ φi : Pt k 1 d}
    {ε : PS k 2 d} (r : Related B B' φ φi ε) (h : PS k 2 d) (hh : B.IsCanonGauge k h) :
    ∃ h' : PS k 2 d, B'.IsCanonGauge k h' ∧ ∀ (w0 : O) (m : ℕ) (f f' : PS k 1 d),
      f' * ev (n := 1) ![pt k (n := 1) d 0, comp1 (B'.A.act w0) (pt k (n := 1) d 0)] ε ^ m =
        ev (n := 1) ![φ] f →
      ∀ (Λ : Type) [Fintype Λ] (u : Λ → Fin d → k) (P : MvPolynomial Λ k),
        B'.nabVal k h' w0 m f' u P = B.nabVal k h w0 m f (fun l => (dLin φ).mulVec (u l)) P := by
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hz : ∀ {n : ℕ}, GP (0 : Pt k n d) := gp_zero₂
  have hε : constantCoeff ε = 1 := by
    have := congrArg constantCoeff r.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_one] at this
  obtain ⟨lam, hl, he⟩ : ∃ lam : PS k 2 d, constantCoeff lam = 0 ∧ FB.expS k lam = ε :=
    ⟨_, constantCoeff_logS hε, exp_log hε⟩
  subst he
  have E : ∀ {n : ℕ} {a b : Pt k n d}, GP a → GP b →
      ev ![a, b] (FB.expS k lam) = FB.expS k (ev ![a, b] lam) := fun ha hb => gt_ev_expS _ (pair_points_zero_constant ha hb) _ hl
  have Z : ∀ {n : ℕ} {a b : Pt k n d}, GP a → GP b →
      constantCoeff (ev ![a, b] lam) = 0 := fun ha hb => gt_const_ev _ (pair_points_zero_constant ha hb) _ hl
  have l0 : ev (n := 1) ![0, pt k (n := 1) d 0] lam = 0 :=
    eq_zero_of_exp_eq_one (Z hz (hp 0)) ((E hz (hp 0)).symm.trans r.ax0)
  have l1 : ev (n := 1) ![pt k (n := 1) d 0, 0] lam = 0 :=
    eq_zero_of_exp_eq_one (Z (hp 0) hz) ((E (hp 0) hz).symm.trans r.ax1)
  have hBa' : ∀ a, GP (B'.A.act a) := B'.A.const
  refine ⟨_, gauge_transformation k d O B B' φ φi lam r.inv l0 l1 r.law r.act ?_ ?_ ?_ (fun a => ?_) h hh, ?_⟩
  · have g := gp_addOf _ B'.G.const _ _ (hp (n := 3) 0) (hp 1)
    have := r.ph1
    rw [E g (hp 2), E (hp 0) (hp 2), E (hp 1) (hp 2), ← gt_expS_add _ _ (Z (hp 0) (hp 2)) (Z (hp 1) (hp 2))] at this
    exact solve_exp (by rw [map_add, Z (hp 0) (hp 2), Z (hp 1) (hp 2), add_zero]) (Z g (hp 2)) this
  · have g := gp_addOf _ B'.G.const _ _ (hp (n := 3) 1) (hp 2)
    have := r.ph2
    rw [E (hp 0) g, E (hp 0) (hp 1), E (hp 0) (hp 2), ← gt_expS_add _ _ (Z (hp 0) (hp 1)) (Z (hp 0) (hp 2))] at this
    exact solve_exp (by rw [map_add, Z (hp 0) (hp 1), Z (hp 0) (hp 2), add_zero]) (Z (hp 0) g) this
  · have := r.sy
    rw [E (hp 1) (hp 0)] at this
    exact solve_exp (Z (hp 1) (hp 0)) hl this
  · have g0 := gp_comp1 _ _ (hBa' a) (hp (n := 2) 0)
    have g1 := gp_comp1 _ _ (hBa' (star a)) (hp (n := 2) 1)
    have := r.ad a
    rw [E (hp 0) g1, E g0 (hp 1)] at this
    exact solve_exp (Z g0 (hp 1)) (Z (hp 0) g1) this
  · intro w0 m f f' hf Λ _ u P
    have ak : B'.actK k w0 = B'.A.act w0 := funext fun i => gt_map_id _
    have g := gp_comp1 _ _ (hBa' w0) (hp (n := 1) 0)
    rw [← hN k d O B B' φ φi lam r.inv l0 l1 (unit_right B.G) r.law r.act h hh.ax0 w0 m f Λ u P, ak]
    congr 1
    rw [E (hp 0) g, ← expS_nsmul (Z (hp 0) g)] at hf
    have := solve_exp (x := f') (y := ev ![φ] f) (a := 0)
      (c := (m : k) • ev (n := 1) ![pt k (n := 1) d 0, comp1 (B'.A.act w0) (pt k (n := 1) d 0)] lam) (map_zero _)
      (by rw [Nat.cast_smul_eq_nsmul, map_nsmul, Z (hp 0) g, nsmul_zero])
      (by rw [expS_zero, _root_.mul_one]; exact hf)
    rwa [zero_sub] at this
end GlobalTheory.JetSer.IntTrans
