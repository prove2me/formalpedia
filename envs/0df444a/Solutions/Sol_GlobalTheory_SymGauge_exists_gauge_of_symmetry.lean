-- Prove2me | solution 1 for GlobalTheory.SymGauge.exists_gauge_of_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:08:04.710099+00:00
-- url     : https://prove2.me/submissions/7c87a46f-e234-42be-b11d-bd8eb8b0d10c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGaugeOfSymmetry
import Theorems.Thm_GlobalTheory_SymGauge_ev_C_mul
import Theorems.Thm_GlobalTheory_SymGauge_expS_inj
import Theorems.Thm_GlobalTheory_SymGauge_expS_zero
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_constantCoeff_logS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eval_pair_points
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_log
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_expS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_expS_add
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
open GlobalTheory GlobalTheory.SymGauge
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.SymGauge
theorem _root_.solution :
    ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), B.ph1 = 1 → B.ph2 = 1 → (∀ a, B.ad a = 1) → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) = 0 ∧ (∀ a : O, (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h) = 0) ∧ B.sy = FB.expS k (ev (n := 2) ![pt k d 1, pt k d 0] h - h) := by
  intro k _ _ d O _ _ B h1 h2 had
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hz : ∀ {n : ℕ}, GP (0 : Pt k n d) := gp_zero₂
  have hF : ∀ i, constantCoeff (B.G.F i) = 0 := B.G.const
  have hsy1 : constantCoeff B.sy = 1 := by
    have := congrArg constantCoeff B.symmetry_zero_fst
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_one] at this
  obtain ⟨s, hs0, hs⟩ : ∃ s : PS k 2 d, constantCoeff s = 0 ∧ FB.expS k s = B.sy :=
    ⟨_, constantCoeff_logS hsy1, exp_log hsy1⟩
  have E : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → ev ![a, b] B.sy = FB.expS k (ev ![a, b] s) := by
    intro n a b ha hb
    rw [← hs, gt_ev_expS _ (pair_points_zero_constant ha hb) _ hs0]
  have c0 : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → constantCoeff (ev ![a, b] s) = 0 :=
    fun a b ha hb => gt_const_ev _ (pair_points_zero_constant ha hb) _ hs0

  have anti0 : s + ev (n := 2) ![pt k d 1, pt k d 0] s = 0 := by
    have e := B.sy_inv
    rw [E _ _ (hp 1) (hp 0)] at e
    refine expS_inj (by rw [map_add, hs0, c0 _ _ (hp 1) (hp 0), add_zero]) (map_zero _) ?_
    rw [gt_expS_add _ _ hs0 (c0 _ _ (hp 1) (hp 0)), hs, e, expS_zero]
  have anti : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → ev ![b, a] s = - ev ![a, b] s := by
    intro n a b ha hb
    have hV := pair_points_zero_constant ha hb
    have e := congrArg (ev ![a, b]) anti0
    rw [gt_ev_add _ hV, gt_ev_zero _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 1) (hp 0)), eval_pair_points,
      evP_pt _ hV, evP_pt _ hV] at e
    exact eq_neg_of_add_eq_zero_right e

  have add0 : ev (n := 3) ![pt k d 0, pt k d 1] s + ev (n := 3) ![pt k d 0, pt k d 2] s =
      ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] s := by
    have hA := gp_addOf _ hF _ _ (hp (n := 3) 1) (hp (n := 3) 2)
    have e := B.sy_law
    rw [h1, h2, ev_one, one_mul, mul_one, E _ _ (hp 0) (hp 1), E _ _ (hp 0) (hp 2), E _ _ (hp 0) hA] at e
    refine expS_inj (by rw [map_add, c0 _ _ (hp 0) (hp 1), c0 _ _ (hp 0) (hp 2), add_zero])
      (c0 _ _ (hp 0) hA) ?_
    rw [gt_expS_add _ _ (c0 _ _ (hp 0) (hp 1)) (c0 _ _ (hp 0) (hp 2)), e]
  have add2 : ∀ {n : ℕ} (x y z : Pt k n d), GP x → GP y → GP z →
      ev ![x, y] s + ev ![x, z] s = ev ![x, addOf B.G.F y z] s := by
    intro n x y z hx hy hz'
    have hA := gp_addOf _ hF _ _ (hp (n := 3) 1) (hp (n := 3) 2)
    have hV := triple_points_zero_constant hx hy hz'
    have e := congrArg (ev ![x, y, z]) add0
    rw [gt_ev_add _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 1)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 2)),
      gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) hA), eval_pair_points, eval_pair_points, eval_pair_points,
      evP_addOf _ hV _ _ _ (hp 1) (hp 2), evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at e
    exact e
  obtain ⟨c, hc⟩ : ∃ c : k, (C c : PS k 2 d) * 2 = -1 := by
    refine ⟨algebraMap ℚ k (-1 / 2), ?_⟩
    have e : algebraMap ℚ k (-1 / 2) * 2 = -1 := by
      rw [← map_ofNat (algebraMap ℚ k) 2, ← map_mul]
      norm_num
    have := congrArg (C (σ := Fin 2 × Fin d) (R := k)) e
    rwa [map_mul, map_neg, map_one, map_ofNat] at this
  refine ⟨C c * s, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have e := B.symmetry_zero_fst
    rw [E _ _ hz (hp 0), ← expS_zero] at e
    rw [ev_C_mul _ (pair_points_zero_constant hz (hp 0)), expS_inj (c0 _ _ hz (hp 0)) (map_zero _) e, mul_zero]
  · have e := B.symmetry_zero_snd
    rw [E _ _ (hp 0) hz, ← expS_zero] at e
    rw [ev_C_mul _ (pair_points_zero_constant (hp 0) hz), expS_inj (c0 _ _ (hp 0) hz) (map_zero _) e, mul_zero]
  · have hA := gp_addOf _ hF _ _ (hp (n := 3) 0) (hp (n := 3) 1)
    rw [ev_C_mul _ (pair_points_zero_constant (hp 0) (hp 2)), ev_C_mul _ (pair_points_zero_constant (hp 1) (hp 2)), ev_C_mul _ (pair_points_zero_constant hA (hp 2)),
      anti _ _ (hp 2) (hp 0), anti _ _ (hp 2) (hp 1), anti _ _ (hp 2) hA,
      ← add2 _ _ _ (hp 2) (hp 0) (hp 1)]
    ring
  · have hA := gp_addOf _ hF _ _ (hp (n := 3) 1) (hp (n := 3) 2)
    rw [ev_C_mul _ (pair_points_zero_constant (hp 0) (hp 1)), ev_C_mul _ (pair_points_zero_constant (hp 0) (hp 2)), ev_C_mul _ (pair_points_zero_constant (hp 0) hA),
      ← add0]
    ring
  · intro a
    have hx := gp_comp1 _ _ (B.A.const a) (hp (n := 2) 0)
    have hy := gp_comp1 _ _ (B.A.const (star a)) (hp (n := 2) 1)
    have e := B.ad_sy a
    rw [had, had, ev_one, one_mul, one_mul, E _ _ hx (hp 1), E _ _ (hp 0) hy] at e
    rw [ev_C_mul _ (pair_points_zero_constant hx (hp 1)), ev_C_mul _ (pair_points_zero_constant (hp 0) hy),
      expS_inj (c0 _ _ hx (hp 1)) (c0 _ _ (hp 0) hy) e, sub_self]
  · rw [ev_C_mul _ (pair_points_zero_constant (hp 1) (hp 0)), ← hs]
    congr 1
    linear_combination (-C c) * anti0 + s * hc
end GlobalTheory.SymGauge
