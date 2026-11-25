-- Prove2me | solution 1 for GlobalTheory.GaugeFirstLaw.exists_gauge_first_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:07:54.926453+00:00
-- url     : https://prove2.me/submissions/704dffdd-0af3-4234-a16d-92ff2656b05b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGaugeFirstLaw
import Theorems.Thm_GlobalTheory_GaugeFirstLaw_expS_inj
import Theorems.Thm_GlobalTheory_GaugeFirstLaw_expS_zero
import Theorems.Thm_GlobalTheory_GaugeFirstLaw_ev_axis
import Theorems.Thm_GlobalTheory_GaugeFirstLaw_pderiv_axis
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_constantCoeff_logS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eval_pair_points
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_log
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_expS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_expS_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant
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
open GlobalTheory GlobalTheory.GaugeFirstLaw
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.GaugeFirstLaw
theorem _root_.solution :
    (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (c : PS k 3 d), ev (n := 2) ![0, pt k d 0, pt k d 1] c = 0 → ev (n := 3) ![pt k d 1, pt k d 0, pt k d 2] c = c → ev (n := 4) ![pt k d 0, pt k d 1, pt k d 3] c + ev (n := 4) ![addOf G.F (pt k d 0) (pt k d 1), pt k d 2, pt k d 3] c = ev (n := 4) ![pt k d 1, pt k d 2, pt k d 3] c + ev (n := 4) ![pt k d 0, addOf G.F (pt k d 1) (pt k d 2), pt k d 3] c → ∃ h : PS k 2 d, ev (n := 1) ![0, pt k d 0] h = 0 ∧ (∀ i, ev (n := 1) ![0, pt k d 0] (pderiv k ((0 : Fin 2), i) h) = 0) ∧ c = (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf G.F (pt k d 0) (pt k d 1), pt k d 2] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (q : ℕ) (g : PS k (q + 1) d), ev (n := q + 2) (Fin.cons (addOf G.F (pt k d 0) (pt k d 1)) (fun j : Fin q => pt k d j.succ.succ)) g = ev (n := q + 2) (Fin.cons (pt k d 0) (fun j : Fin q => pt k d j.succ.succ)) g + ev (n := q + 2) (Fin.cons (pt k d 1) (fun j : Fin q => pt k d j.succ.succ)) g → (∀ i, ev (n := q) (Fin.cons 0 (fun j : Fin q => pt k d j)) (pderiv k ((0 : Fin (q + 1)), i) g) = 0) → g = 0) → ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ B.ph1 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) := by
  intro H1 H2 k _ _ d O _ _ B
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hz : ∀ {n : ℕ}, GP (0 : Pt k n d) := gp_zero₂
  have hA : ∀ {n : ℕ} (i j : Fin n), GP (addOf B.G.F (pt k (n := n) d i) (pt k d j)) :=
    fun i j => gp_addOf _ B.G.const _ _ (hp i) (hp j)
  have h1 : constantCoeff B.ph1 = 1 := by
    have := congrArg constantCoeff B.cocycleLeft_zero_fst
    rwa [gt_const_ev_eq _ (triple_points_zero_constant hz (hp 0) (hp 1)), map_one] at this
  obtain ⟨c, hc0, hc⟩ : ∃ c : PS k 3 d, constantCoeff c = 0 ∧ B.ph1 = FB.expS k c :=
    ⟨_, constantCoeff_logS h1, (exp_log h1).symm⟩
  have E : ∀ {n : ℕ} (V : Fin 3 → Pt k n d), (∀ j, GP (V j)) →
      ev V B.ph1 = FB.expS k (ev V c) ∧ constantCoeff (ev V c) = 0 := by
    intro n V hV
    exact ⟨by rw [hc, gt_ev_expS V hV c hc0], gt_const_ev V hV c hc0⟩
  have a0 : ev (n := 2) ![0, pt k d 0, pt k d 1] c = 0 := by
    obtain ⟨e, e0⟩ := E (n := 2) _ (triple_points_zero_constant hz (hp 0) (hp 1))
    refine expS_inj e0 (map_zero _) ?_
    rw [← e, B.cocycleLeft_zero_fst, expS_zero]
  have a2 : ev (n := 2) ![pt k d 0, pt k d 1, 0] c = 0 := by
    obtain ⟨e, e0⟩ := E (n := 2) _ (triple_points_zero_constant (hp 0) (hp 1) hz)
    refine expS_inj e0 (map_zero _) ?_
    rw [← e, B.cocycleLeft_zero_thd, expS_zero]
  have cm : ev (n := 3) ![pt k d 1, pt k d 0, pt k d 2] c = c := by
    obtain ⟨e, e0⟩ := E (n := 3) _ (triple_points_zero_constant (hp 1) (hp 0) (hp 2))
    refine expS_inj e0 hc0 ?_
    rw [← e, B.cocycleLeft_comm, hc]
  have as : ev (n := 4) ![pt k d 0, pt k d 1, pt k d 3] c +
      ev (n := 4) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2, pt k d 3] c =
      ev (n := 4) ![pt k d 1, pt k d 2, pt k d 3] c +
      ev (n := 4) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2), pt k d 3] c := by
    obtain ⟨e1, f1⟩ := E (n := 4) _ (triple_points_zero_constant (hp 0) (hp 1) (hp 3))
    obtain ⟨e2, f2⟩ := E (n := 4) _ (triple_points_zero_constant (hA 0 1) (hp 2) (hp 3))
    obtain ⟨e3, f3⟩ := E (n := 4) _ (triple_points_zero_constant (hp 1) (hp 2) (hp 3))
    obtain ⟨e4, f4⟩ := E (n := 4) _ (triple_points_zero_constant (hp 0) (hA 1 2) (hp 3))
    refine expS_inj (by rw [map_add, f1, f2, add_zero]) (by rw [map_add, f3, f4, add_zero]) ?_
    rw [gt_expS_add _ _ f1 f2, gt_expS_add _ _ f3 f4, ← e1, ← e2, ← e3, ← e4]
    exact B.cocycleLeft_assoc
  obtain ⟨h, hx0, hd, hch⟩ := H1 k d B.G c a0 cm as
  refine ⟨h, ⟨hx0, ?_⟩, by rw [hc, hch]⟩
  have hV : ∀ j, GP ((![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d) j) := triple_points_zero_constant (hp 0) (hp 1) hz
  rw [hch, gt_ev_sub _ hV, gt_ev_add _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 2)),
    gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 1) (hp 2)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hA 0 1) (hp 2)),
    eval_pair_points, eval_pair_points, eval_pair_points, evP_addOf _ hV _ _ _ (hp 0) (hp 1),
    evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at a2
  have cons1 : ∀ {n : ℕ} (a : Pt k n d) (r : Fin 0 → Pt k n d),
      (Fin.cons a r : Fin (0 + 1) → Pt k n d) = ![a] := by
    intro n a r
    funext j
    fin_cases j
    rfl
  refine H2 k d B.G 0 (ev (n := 1) ![pt k d 0, 0] h) ?_ ?_
  · rw [cons1, cons1, cons1]
    have t0 := ev_axis (pt k (n := 2) d 0) (hp 0) h
    have t1 := ev_axis (pt k (n := 2) d 1) (hp 1) h
    have t2 := ev_axis _ (hA (n := 2) 0 1) h
    refine t2.trans (Eq.trans ?_ (congrArg₂ (· + ·) t0 t1).symm)
    exact (sub_eq_zero.1 a2).symm
  · intro i
    rw [cons1]
    have hZ : ∀ j, GP ((![0] : Fin 1 → Pt k 0 d) j) := single_point_zero_constant hz
    have e := congrArg (ev (n := 0) ![0]) (hd i)
    rw [gt_ev_ev' _ _ hZ (pair_points_zero_constant hz (hp 0)), eval_pair_points, evP_zero _ hZ, evP_pt _ hZ,
      gt_ev_zero _ hZ] at e
    refine (congrArg (ev (n := 0) ![0]) (pderiv_axis h i)).trans ?_
    rw [ev_axis _ hz]
    exact e
end GlobalTheory.GaugeFirstLaw
