-- Prove2me | solution 1 for GlobalTheory.JetSer.lawSt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:43:56.240545+00:00
-- url     : https://prove2.me/submissions/7db6c1ab-3433-4d55-aec2-76ca9b307fc7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AddOfPtPt
import Theorems.Thm_GlobalTheory_JetSer_IsFPt_mul
import Theorems.Thm_GlobalTheory_JetSer_addOf_pt_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant


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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer
namespace GlobalTheory.JetSer
theorem _root_.solution (hJ : JetAlgSt) (hR : RepSt) : LawSt := by
  intro R _ G _ _ d x hx
  have uC : ∀ {n : ℕ} {a a' : Pt R n d} {y : Fam G (Fin n × Fin d)}, Rep x a y → Rep x a' y → a = a' :=
    fun {n a a' y} h h' =>
      ((hR R G d x hx (Fin n × Fin d)).2.1 y ((hR R G d x hx (Fin n × Fin d)).2.2.1 a y h)).unique h h'
  have uP : ∀ {n : ℕ} {a : Pt R n d} {y y' : Fam G (Fin n × Fin d)}, Rep x a y → Rep x a y' → y = y' :=
    fun {n a y y'} h h' => ((hR R G d x hx (Fin n × Fin d)).1 a h.1).unique h h'
  have gen : ∀ (n : ℕ) (j : Fin n), ∃ y : Fam G (Fin n × Fin d), Rep x (pt R d j) y :=
    fun n j => ((hR R G d x hx (Fin n × Fin d)).1 _ (gp_pt j)).exists
  choose Y hY using gen
  refine ⟨?_, fun F F' hF hF' => ?_⟩
  swap
  · rw [← addOf_pt_pt F, ← addOf_pt_pt F']
    exact uC (hF.2 2 _ _ _ _ (hY 2 0) (hY 2 1)) (hF'.2 2 _ _ _ _ (hY 2 0) (hY 2 1))
  have H2 := hR R G d x hx (Fin 2 × Fin d)
  obtain ⟨F, hF⟩ := (H2.2.1 _ (IsFPt.mul (H2.2.2.1 _ _ (hY 2 0)) (H2.2.2.1 _ _ (hY 2 1)))).exists
  have law : IsLawOf x F := by
    refine ⟨hF.1, fun n a b y z ha hb => ?_⟩
    let c : Fin 2 × Fin d → PS R n d := fun p => (![a, b] : Fin 2 → Pt R n d) p.1 p.2
    have hc : ∀ p, constantCoeff (c p) = 0 := fun p => pair_points_zero_constant ha.1 hb.1 p.1 p.2
    have hex : ∀ m, ∃ ψ : JetR R (Fin 2 × Fin d) m →ₐ[R] JetR R (Fin n × Fin d) m,
        ∀ j, ψ (zR m j) = toJet m (c j) :=
      fun m => ((hJ R (Fin n × Fin d)).2.2.2.2 (Fin 2 × Fin d) c hc m).1
    choose ψ hψ using hex
    have sub := H2.2.2.2.2 (Fin n × Fin d) c ψ hc hψ
    have hs : ∀ j : Fin 2, (fun i => MvPowerSeries.subst c (pt R (n := 2) d j i)) = (![a, b] : Fin 2 → Pt R n d) j :=
      fun j => funext fun i => gt_ev_X _ (pair_points_zero_constant ha.1 hb.1) j i
    have e0 : (fun m => spMap (ψ m) ≫ Y 2 0 m) = y := by
      have := sub _ _ (hY 2 0)
      rw [hs 0] at this
      exact uP this ha
    have e1 : (fun m => spMap (ψ m) ≫ Y 2 1 m) = z := by
      have := sub _ _ (hY 2 1)
      rw [hs 1] at this
      exact uP this hb
    have key := sub _ _ hF
    have e : (fun m => spMap (ψ m) ≫ (Y 2 0 m * Y 2 1 m)) = fun m => y m * z m := by
      funext m
      rw [MonObj.comp_mul, ← e0, ← e1]
    rw [← e]
    exact key
  refine ⟨⟨F, hF.1, fun i => ?_, fun i => ?_, fun i => ?_⟩, law⟩
  · have h := law.2 1 _ _ _ _ (hR R G d x hx (Fin 1 × Fin d)).2.2.2.1 (hY 1 0)
    simp only [_root_.one_mul] at h
    exact congrFun (uC h (hY 1 0)) i
  · have h := law.2 2 _ _ _ _ (hY 2 1) (hY 2 0)
    have e : (fun m => Y 2 1 m * Y 2 0 m) = fun m => Y 2 0 m * Y 2 1 m :=
      funext fun m => _root_.mul_comm _ _
    rw [e] at h
    exact congrFun (uC h hF) i
  · have h := law.2 3 _ _ _ _ (law.2 3 _ _ _ _ (hY 3 0) (hY 3 1)) (hY 3 2)
    have h' := law.2 3 _ _ _ _ (hY 3 0) (law.2 3 _ _ _ _ (hY 3 1) (hY 3 2))
    simp only [_root_.mul_assoc] at h
    exact congrFun (uC h h') i
end GlobalTheory.JetSer
