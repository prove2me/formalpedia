-- Prove2me | solution 1 for GlobalTheory.JetSer.FrameChange.hMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:17:10.894933+00:00
-- url     : https://prove2.me/submissions/4137fadd-1c63-41a5-831b-b34624ce4a2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_uv_linComb
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_gen_change
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_sec_change
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_prod_lam
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_prod_prim
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_unit_mem_lam
import Theorems.Thm_P2M_GlobalTheory_JetSer_FrameChange_cub_lam__d813c2f962f0
import Theorems.Thm_P2M_GlobalTheory_JetSer_FrameChange_cub_lam__899c0adc3157
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_ros_lam
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_lamV_comm
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_eval_standard_points_two
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_eval_standard_points_three
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_toJet_mul
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_toJet_pow
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_jet_unit
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_germ_alg
import Theorems.Thm_GlobalTheory_JetSer_toJet_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_pt_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_hasSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε)
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.FrameChange
namespace GlobalTheory.JetSer.FrameChange
theorem _root_.solution : JetAlgSt → RepSt → TwoChartSt → SerSt → SerExSt → HMulSt := by
  intro hJ hR hT _ hE R _ G _ _ Lr c O _ _ act u hu d x x' hx hx' j j' hj hj' B B' hB hB'
  obtain ⟨φ, φi, hinv, hφ, -, hlaw, hact⟩ := hT R G d x x' hx hx'
  obtain ⟨ε, hε, -⟩ := (hE R G d x' hx').2.1
    ((LB.LinComb Lr.L (lamφ G) lamε).U (fun _ => j) ⊓ (LB.LinComb Lr.L (lamφ G) lamε).U (fun _ => j'))
    (fun z hz => ⟨unit_mem_lam Lr.L j hj hz, unit_mem_lam Lr.L j' hj' hz⟩)
    ((LB.LinComb Lr.L (lamφ G) lamε).g (fun _ => j) (fun _ => j')).val
  have inj : ∀ {n : ℕ} (g g' : PS R n d), (∀ m, toJet m g = toJet m g') → g = g' :=
    fun {n} => (hJ R (Fin n × Fin d)).2.2.1
  have E : ∀ {n : ℕ} {a b : Pt R n d} {y z : Fam G (Fin n × Fin d)}, Rep x' a y → Rep x' b z → ∀ m,
      toJet m (ev ![a, b] ε) = (lamV (T := sp (R₀ := R) (JetR R (Fin n × Fin d) m)) (hv Lr.L j j') (y m) (z m)).val := by
    intro n a b y z hy hz m
    have H := hε n a b y z hy hz
    refine (jet_unit H m).trans (congrArg Units.val ?_)
    exact (uv_linComb Lr.L j j' _ _ _ (H m).1).trans (prod_lam (y m) (z m) (hv Lr.L j j'))
  have P : ∀ {n : ℕ} (i : Fin n), ∃ y, Rep x' (pt R (n := n) d i) y :=
    fun {n} i => ((hR R G d x' hx' (Fin n × Fin d)).1 _ (gp_pt i)).exists
  have Z : ∀ n : ℕ, Rep x' (0 : Pt R n d) (fun _ => 1) := fun n => (hR R G d x' hx' (Fin n × Fin d)).2.2.2.1
  have C : ∀ {n : ℕ} {a : Pt R n d} {y : Fam G (Fin n × Fin d)}, Rep x' a y → Rep x (comp1 φ a) y := by
    intro n a y hy
    simpa only [Category.comp_id] using hφ.2 n a y hy
  have cub : ∀ {y₀ y₁ y₂ : Fam G (Fin 3 × Fin d)}, Rep x' (pt R d 0) y₀ → Rep x' (pt R d 1) y₁ →
      Rep x' (pt R d 2) y₂ → ∀ m, ∃ t : (JetR R (Fin 3 × Fin d) m)ˣ, toJet m B'.ph1 = t.val ∧
        toJet m (ev (n := 3) ![comp1 φ (pt R (n := 3) d 0), comp1 φ (pt R (n := 3) d 1),
          comp1 φ (pt R (n := 3) d 2)] B.ph1) =
        ((∏ I : thK, hv Lr.L j j' ((lift (y₀ m) (lift (y₁ m) (y₂ m))).left ≫ thφ G (x3 G) I) ^ thε I) * t).val := by
    intro y₀ y₁ y₂ h₀ h₁ h₂ m
    have H' := hB'.ph1 3 _ _ _ _ _ _ h₀ h₁ h₂
    have H := hB.ph1 3 _ _ _ _ _ _ (C h₀) (C h₁) (C h₂)
    rw [eval_standard_points_three] at H'
    exact ⟨_, jet_unit H' m, (jet_unit H m).trans (congrArg Units.val
      (gen_change Lr.L j j' (thφ G (x3 G)) thε c.t c.isGen _ (H m).1 (H' m).1))⟩
  refine ⟨φ, φi, ε, ⟨hinv, ?_, ?_, hlaw _ _ hB.law hB'.law, fun a => hact _ _ _ (hB.map a) (hB'.map a),
    ?_, ?_, ?_, fun a => ?_⟩, hφ, ?_⟩
  · obtain ⟨y, hy⟩ := P (n := 1) 0
    refine inj _ _ fun m => ?_
    rw [E (Z 1) hy m, toJet_one]
    simp [lamV]
  · obtain ⟨y, hy⟩ := P (n := 1) 0
    refine inj _ _ fun m => ?_
    rw [E hy (Z 1) m, toJet_one]
    simp [lamV]
  · obtain ⟨y₀, h₀⟩ := P (n := 3) 0
    obtain ⟨y₁, h₁⟩ := P (n := 3) 1
    obtain ⟨y₂, h₂⟩ := P (n := 3) 2
    refine inj _ _ fun m => ?_
    obtain ⟨t, ht', ht⟩ := cub h₀ h₁ h₂ m
    rw [toJet_mul hJ, toJet_mul hJ, toJet_mul hJ, ht', ht, E (hB'.law.2 3 _ _ _ _ h₀ h₁) h₂ m, E h₀ h₂ m, E h₁ h₂ m]
    simp only [← Units.val_mul]
    exact congrArg Units.val (cub_lam₁ (y₀ m) (y₁ m) (y₂ m) (hv Lr.L j j') t)
  · obtain ⟨y₀, h₀⟩ := P (n := 3) 0
    obtain ⟨y₁, h₁⟩ := P (n := 3) 1
    obtain ⟨y₂, h₂⟩ := P (n := 3) 2
    refine inj _ _ fun m => ?_
    obtain ⟨t, ht', ht⟩ := cub h₀ h₁ h₂ m
    rw [hB.ph2, hB'.ph2, toJet_mul hJ, toJet_mul hJ, toJet_mul hJ, ht', ht, E h₀ (hB'.law.2 3 _ _ _ _ h₁ h₂) m,
      E h₀ h₁ m, E h₀ h₂ m]
    simp only [← Units.val_mul]
    exact congrArg Units.val (cub_lam₂ (y₀ m) (y₁ m) (y₂ m) (hv Lr.L j j') t)
  · obtain ⟨y₀, h₀⟩ := P (n := 2) 0
    obtain ⟨y₁, h₁⟩ := P (n := 2) 1
    rw [hB.sy, hB'.sy, ev_one, _root_.one_mul, _root_.one_mul]
    refine inj _ _ fun m => ?_
    have e := E h₀ h₁ m
    rw [eval_standard_points_two] at e
    rw [e, E h₁ h₀ m, lamV_comm]
  · obtain ⟨y₀, h₀⟩ := P (n := 2) 0
    obtain ⟨y₁, h₁⟩ := P (n := 2) 1
    refine inj _ _ fun m => ?_
    have H' := hB'.ad a 2 _ _ _ _ h₀ h₁
    have H := hB.ad a 2 _ _ _ _ (C h₀) (C h₁)
    rw [eval_standard_points_two] at H'
    have g := gen_change Lr.L j j' _ _ (u a) (hu a) _ (H m).1 (H' m).1
    rw [toJet_mul hJ, toJet_mul hJ, jet_unit H' m, jet_unit H m, E h₀ ((hB'.map (star a)).2 2 _ _ h₁) m,
      E ((hB'.map a).2 2 _ _ h₀) h₁ m, map_inv, map_inv, g]
    simp only [← Units.val_mul]
    exact congrArg Units.val (ros_lam _ _ (y₀ m) (y₁ m) (hv Lr.L j j') _)
  · rintro w0 ρ hρ k s f f' ⟨σ, r, hσ, hr, hf⟩ ⟨σ', r', hσ', hr', hf'⟩
    obtain ⟨y, hy⟩ := P (n := 1) 0
    have hc := C hy
    rw [gt_comp1_pt_right] at hc
    refine inj _ _ fun m => ?_
    have Hσ := hσ 1 _ _ hc
    have Hr := hr 1 _ _ hc
    have Hσ' := hσ' 1 _ _ hy
    have Hr' := hr' 1 _ _ hy
    rw [gt_ev_pt_self] at Hσ' Hr'
    have gr := (gen_change Lr.L j j' _ _ ρ hρ _ (Hr m).1 (Hr' m).1).trans
      (congrArg (· * _) (prod_prim (act.act w0) (y m) (hv Lr.L j j')))
    have gs := sec_change Lr.L j j' _ _ s _ (Hσ m).1 (Hσ' m).1
    rw [(Hσ m).2, (Hσ' m).2, Fintype.prod_unique, zpow_natCast] at gs
    have e' := congrArg (toJet m) hf'
    rw [toJet_mul hJ, toJet_pow hJ, jet_unit Hr' m] at e'
    have hev : ev (n := 1) ![φ] f * ev (n := 1) ![φ] r ^ k = ev (n := 1) ![φ] σ := by
      rw [← hf]
      unfold ev
      rw [← MvPowerSeries.coe_substAlgHom (gt_hasSubst ![φ] (single_point_zero_constant hinv.1)), map_mul, map_pow]
    have e := congrArg (toJet m) hev
    rw [toJet_mul hJ, toJet_pow hJ, jet_unit Hr m, gr, gs] at e
    rw [toJet_mul hJ, toJet_pow hJ, E hy ((hB'.map w0).2 1 _ _ hy) m]
    refine germ_alg _ _ _ (hv Lr.L j j' (y m).left) _ k _ e' (e.trans ?_)
    congr 4
end GlobalTheory.JetSer.FrameChange
