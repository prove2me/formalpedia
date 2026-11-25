-- Prove2me | solution 1 for GlobalTheory.canonGauge_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:33:41.043584+00:00
-- url     : https://prove2.me/submissions/a11a478e-2acd-4136-b9fe-b16b851e4687

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeOfSteps
import Theorems.Thm_GlobalTheory_CanonGaugeAssembly_const_of_ax
import Theorems.Thm_GlobalTheory_CanonGaugeAssembly_cancel_expS
import Theorems.Thm_GlobalTheory_CanonGaugeAssembly_cob_three
import Theorems.Thm_GlobalTheory_CanonGaugeAssembly_cob_two
import Theorems.Thm_GlobalTheory_CanonGaugeAssembly_cob_swap
import Theorems.Thm_GlobalTheory_CanonGaugeAssembly_Cob_chain
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_nt_expS_zero
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
open GlobalTheory.CanonGaugeAssembly
namespace GlobalTheory
theorem _root_.solution :
    (∀ (R k : Type) [CommRing R] [CommRing k] (f : R →+* k) (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ B' : FB k d O, (∀ i, B'.G.F i = MvPowerSeries.map f (B.G.F i)) ∧ (∀ a i, B'.A.act a i = MvPowerSeries.map f (B.A.act a i)) ∧ B'.ph1 = MvPowerSeries.map f B.ph1 ∧ B'.ph2 = MvPowerSeries.map f B.ph2 ∧ B'.sy = MvPowerSeries.map f B.sy ∧ ∀ a, B'.ad a = MvPowerSeries.map f (B.ad a)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O) (h : PS k 2 d), (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) → ∃ B' : FB k d O, B'.G.F = B.G.F ∧ B'.A.act = B.A.act ∧ B.ph1 = B'.ph1 * FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) ∧ B.ph2 = B'.ph2 * FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) ∧ B.sy = B'.sy * FB.expS k (ev (n := 2) ![pt k d 1, pt k d 0] h - h) ∧ ∀ a : O, B.ad a = B'.ad a * FB.expS k (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ B.ph1 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), B.ph1 = 1 → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ B.ph2 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (B : FB k d O), B.ph1 = 1 → B.ph2 = 1 → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) = 0 ∧ ∀ a : O, B.ad a = FB.expS k (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), B.ph1 = 1 → B.ph2 = 1 → (∀ a, B.ad a = 1) → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) = 0 ∧ (∀ a : O, (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h) = 0) ∧ B.sy = FB.expS k (ev (n := 2) ![pt k d 1, pt k d 0] h - h)) → CanonGaugeSt := by
  intro hbc hrg s1 s2 s3 s4 R _ d O _ _ _ _ _ k _ _ _ B
  obtain ⟨B0, hF0, hA0, hp10, hp20, hsy0, had0⟩ := hbc R k (algebraMap R k) d O B
  have eF : B.FK k = B0.G.F := funext fun i => (hF0 i).symm
  have eA : ∀ a, B.actK k a = B0.A.act a := fun a => funext fun i => (hA0 a i).symm
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have C1 := cob_three (n := 3) ![pt k d 0, pt k d 2] ![pt k d 1, pt k d 2]
    ![addOf B0.G.F (pt k d 0) (pt k d 1), pt k d 2] (pair_points_zero_constant (hp _) (hp _)) (pair_points_zero_constant (hp _) (hp _))
    (pair_points_zero_constant (gp_addOf _ B0.G.const _ _ (hp _) (hp _)) (hp _))
  have C2 := cob_three (n := 3) ![pt k d 0, pt k d 1] ![pt k d 0, pt k d 2]
    ![pt k d 0, addOf B0.G.F (pt k d 1) (pt k d 2)] (pair_points_zero_constant (hp _) (hp _)) (pair_points_zero_constant (hp _) (hp _))
    (pair_points_zero_constant (hp _) (gp_addOf _ B0.G.const _ _ (hp _) (hp _)))
  have CS := cob_swap ![pt k d 1, pt k d 0] (pair_points_zero_constant (hp _) (hp _))
  have CA := fun a : O => cob_two (n := 2) ![comp1 (B0.A.act a) (pt k d 0), pt k d 1]
    ![pt k d 0, comp1 (B0.A.act (star a)) (pt k d 1)]
    (pair_points_zero_constant (gp_comp1 _ _ (B0.A.const a) (hp _)) (hp _))
    (pair_points_zero_constant (hp _) (gp_comp1 _ _ (B0.A.const (star a)) (hp _)))

  obtain ⟨h1, ax1, t1⟩ := s1 k d O B0
  have c1 := const_of_ax ax1.1
  obtain ⟨B1, F1, A1, p11, p21, sy1, ad1⟩ := hrg k d O B0 h1 ax1
  have q11 : B1.ph1 = 1 := cancel_expS (C1.const _ c1) (t1.symm.trans p11)

  obtain ⟨h2, ax2, z12, t2⟩ := s2 k d O B1 q11
  have c2 := const_of_ax ax2.1
  obtain ⟨B2, F2, A2, p12, p22, sy2, ad2⟩ := hrg k d O B1 h2 ax2
  have q12 : B2.ph1 = 1 := by
    rw [z12, nt_expS_zero, mul_one, q11] at p12; exact p12.symm
  rw [F1] at t2 p12 p22
  rw [A1] at ad2
  have q22 : B2.ph2 = 1 := cancel_expS (C2.const _ c2) (t2.symm.trans p22)

  obtain ⟨h3, ax3, z13, z23, t3⟩ := s3 k d O B2 q12 q22
  have c3 := const_of_ax ax3.1
  obtain ⟨B3, F3, A3, p13, p23, sy3, ad3⟩ := hrg k d O B2 h3 ax3
  have q13 : B3.ph1 = 1 := by
    rw [z13, nt_expS_zero, mul_one, q12] at p13; exact p13.symm
  have q23 : B3.ph2 = 1 := by
    rw [z23, nt_expS_zero, mul_one, q22] at p23; exact p23.symm
  rw [F2, F1] at p13 p23
  rw [A2, A1] at ad3 t3
  have qa3 : ∀ a, B3.ad a = 1 := fun a =>
    cancel_expS ((CA a).const _ c3) ((t3 a).symm.trans (ad3 a))

  obtain ⟨h4, ax4, z14, z24, za4, t4⟩ := s4 k d O B3 q13 q23 qa3
  have c4 := const_of_ax ax4.1
  rw [F3, F2, F1] at z14 z24
  rw [A3, A2, A1] at za4
  have g0 : ∀ j, GP ((![0, pt k d 0] : Fin 2 → Pt k 1 d) j) := pair_points_zero_constant gp_zero₂ (hp _)
  have g1 : ∀ j, GP ((![pt k d 0, 0] : Fin 2 → Pt k 1 d) j) := pair_points_zero_constant (hp _) gp_zero₂
  refine ⟨h1 + h2 + h3 + h4, ?_, ?_, ?_, ?_, ?_, fun a => ?_⟩
  · rw [gt_ev_add _ g0, gt_ev_add _ g0, gt_ev_add _ g0, ax1.1, ax2.1, ax3.1, ax4.1]; simp
  · rw [gt_ev_add _ g1, gt_ev_add _ g1, gt_ev_add _ g1, ax1.2, ax2.2, ax3.2, ax4.2]; simp
  · rw [eF]
    exact hp10.symm.trans (C1.chain c1 c2 c3 c4 p11 p12 p13 (by
      rw [q13]; beta_reduce; rw [z14, nt_expS_zero]))
  · rw [eF]
    exact hp20.symm.trans (C2.chain c1 c2 c3 c4 p21 p22 p23 (by
      rw [q23]; beta_reduce; rw [z24, nt_expS_zero]))
  · exact hsy0.symm.trans (CS.chain c1 c2 c3 c4 sy1 sy2 sy3 t4)
  · rw [eA, eA]
    exact (had0 a).symm.trans ((CA a).chain c1 c2 c3 c4 (ad1 a) (ad2 a) (ad3 a) (by
      rw [qa3 a]; beta_reduce; rw [za4 a, nt_expS_zero]))
end GlobalTheory
