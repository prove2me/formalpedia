-- Prove2me | solution 1 for GlobalTheory.canonGauge_dmonOf_hL_natCast_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:48:13.723205+00:00
-- url     : https://prove2.me/submissions/4aa6b177-20ac-4719-ae72-4c2af0006114

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral
import Theorems.Thm_GlobalTheory_GaugeDiv_dmon_div
import Theorems.Thm_GlobalTheory_FormalCalc_dAct_add_and_one
import Theorems.Thm_GlobalTheory_GaugeInt_IP_gp
import Theorems.Thm_GlobalTheory_GaugeInt_IP_int
import Theorems.Thm_GlobalTheory_GaugeInt_di_of_exp
import Theorems.Thm_GlobalTheory_GaugeInt_lin_int
import Theorems.Thm_GlobalTheory_QuadDeriv_addOf_pt
import Theorems.Thm_GlobalTheory_QuadDeriv_baseChange_addOf
import Theorems.Thm_GlobalTheory_QuadDeriv_baseChange_comp1
import Theorems.Thm_GlobalTheory_QuadDeriv_baseChange_pt
import Theorems.Thm_GlobalTheory_QuadDeriv_const_pderiv
import Theorems.Thm_GlobalTheory_QuadDeriv_unit_right
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_eq_zero_of_axes
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_triple_points_zero_constant


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
open GlobalTheory
open GaugeDiv
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k]
      [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h →
      ∀ (w : O) (N : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin d → R),
      (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec
        ((dAct k B w).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
      ∀ mo : ι →₀ ℕ, ∃ r : R, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo
        (B.hL k h ((N : O) * w))) = algebraMap R k (N * r) := by
  intro R _ d O _ _ k _ _ _ B g hg w N ι _ u hβ m
  have iF : IP (algebraMap R k) (B.FK k) := ⟨B.G.F, B.G.const, rfl⟩
  have iw : ∀ a, IP (algebraMap R k) (B.actK k a) := fun a => ⟨B.A.act a, B.A.const a, rfl⟩
  have hF := iF.gp
  have hU : evP (n := 1) ![pt k d 0, 0] (B.FK k) = pt k d 0 := by
    have := congrArg (mapP (algebraMap R k)) (unit_right B.G)
    rw [baseChange_addOf _ _ _ _ (gp_pt 0) gp_zero₂, baseChange_pt,
      show mapP (algebraMap R k) (0 : Pt R 1 d) = 0 from funext fun i => map_zero _] at this
    exact this
  have hom : ∀ w0, comp1 (B.actK k w0) (B.FK k) =
      addOf (B.FK k) (comp1 (B.actK k w0) (pt k (n := 2) d 0))
        (comp1 (B.actK k w0) (pt k (n := 2) d 1)) := by
    intro w0
    have := congrArg (mapP (algebraMap R k)) (B.A.hom w0)
    rw [FGLaw.add, FGLaw.add, addOf_pt, baseChange_comp1 _ _ _ B.G.const,
      baseChange_addOf _ _ _ _ (gp_comp1 _ _ (B.A.const w0) (gp_pt 0))
        (gp_comp1 _ _ (B.A.const w0) (gp_pt 1)),
      baseChange_comp1 _ _ _ (gp_pt 0), baseChange_comp1 _ _ _ (gp_pt 1), baseChange_pt, baseChange_pt] at this
    exact this
  have c0 : constantCoeff g = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact coeff_eq_zero_of_axes g hg.ax0 hg.ax1 0 (by simp)
  have c1 : ∀ s, constantCoeff (pderiv k s g) = 0 := fun s => by
    rw [const_pderiv]
    exact coeff_eq_zero_of_axes g hg.ax0 hg.ax1 _ (by simp)
  have hp : ∀ j : Fin 3, GP (pt k d j) := gp_pt
  have hl : DI (algebraMap R k) (defL (B.FK k) g) := by
    refine di_of_exp B.ph1 ?_ _ ?_ hg.ph1
    · rw [← gt_const_ev_eq _ (triple_points_zero_constant (n := 2) gp_zero₂ (gp_pt 0) (gp_pt 1)), B.cocycleLeft_zero_fst, map_one]
    · rw [defL, map_sub, map_add, gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (gp_addOf _ hF _ _ (hp _) (hp _)) (hp _)) _ c0]
      simp
  have hr : DI (algebraMap R k) (defR (B.FK k) g) := by
    refine di_of_exp B.ph2 ?_ _ ?_ hg.ph2
    · rw [← gt_const_ev_eq _ (triple_points_zero_constant (n := 2) gp_zero₂ (gp_pt 0) (gp_pt 1)), B.cocycleRight_zero_fst, map_one]
    · rw [defR, map_sub, map_add, gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (hp _) (gp_addOf _ hF _ _ (hp _) (hp _))) _ c0]
      simp
  have hlin : ∀ a (v : Fin d → k) i, lin v (B.actK k a i) = (dAct k B a).mulVec v i := by
    intro a v i
    simp only [lin, const_pderiv, Matrix.mulVec, dotProduct, dAct, mul_comm]
  have hadd := (FormalCalc.dAct_add_and_one R d O k B).1
  have hN : ∀ n : ℕ, dAct k B ((n : O) * w) = n • dAct k B w := by
    intro n
    induction n with
    | zero =>
      have := hadd 0 0
      rw [add_zero, left_eq_add] at this
      simp [this]
    | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hadd, ih, succ_nsmul]
  rw [FB.hL, gt_comp1_pt_right]
  refine dmon_div iF hU (iw _).gp (hom _) g hg.ax1 c1 hl hr _
    (fun l => (dAct k B w).mulVec fun i => algebraMap R k (u l i)) (fun l i => ⟨u l i, rfl⟩)
    (fun l i => ?_) N (fun l i => ?_) hβ m
  · rw [← hlin]
    exact lin_int (fun i => ⟨u l i, rfl⟩) ((iw w).int i)
  · rw [hlin, hN, Matrix.smul_mulVec]
    simp
end GlobalTheory
