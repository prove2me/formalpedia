-- Prove2me | solution 1 for GlobalTheory.JetSer.twoChart_of_rep_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:41:27.890196+00:00
-- url     : https://prove2.me/submissions/a81be93a-bf8f-4f44-8081-7525581ac5fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_TwoChartAddOfPtPt
import Theorems.Thm_GlobalTheory_JetSer_IsMapOf_twoChart_rep_of_id
import Theorems.Thm_GlobalTheory_JetSer_twoChart_addOf_pt_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer
namespace GlobalTheory.JetSer
theorem _root_.solution : JetAlgSt → RepSt → MapSt → TwoChartSt := by
  intro _ hR hM R _ G _ d x x' hx hx'
  obtain ⟨φ, hφ, -⟩ := hM R G G d x' x hx' hx (𝟙 G) (Category.comp_id _)
  obtain ⟨φi, hφi, -⟩ := hM R G G d x x' hx hx' (𝟙 G) (Category.comp_id _)
  have uniq : ∀ {z : Fam G (Fin d)}, IsUnivChart G d z → ∀ {n : ℕ} {a b : Pt R n d}
      {y : Fam G (Fin n × Fin d)}, Rep z a y → Rep z b y → a = b := fun {z} hz {n a b y} ha hb =>
    ((hR R G d z hz (Fin n × Fin d)).2.1 y ((hR R G d z hz (Fin n × Fin d)).2.2.1 a y ha)).unique ha hb
  have ex : ∀ {z : Fam G (Fin d)}, IsUnivChart G d z → ∀ {n : ℕ} (j : Fin n),
      ∃ y : Fam G (Fin n × Fin d), Rep z (pt R d j) y := fun {z} hz {n} j =>
    ((hR R G d z hz (Fin n × Fin d)).1 (pt R d j) (gp_pt j)).exists
  refine ⟨φ, φi, ⟨hφ.1, hφi.1, ?_, ?_⟩, hφ, hφi, fun F F' hF hF' i => ?_, fun f α α' hα hα' => ?_⟩
  · obtain ⟨y, hy⟩ := ex hx (0 : Fin 1)
    have h := hφ.twoChart_rep_of_id (hφi.twoChart_rep_of_id hy)
    rw [gt_comp1_pt_right] at h
    exact uniq hx h hy
  · obtain ⟨y, hy⟩ := ex hx' (0 : Fin 1)
    have h := hφi.twoChart_rep_of_id (hφ.twoChart_rep_of_id hy)
    rw [gt_comp1_pt_right] at h
    exact uniq hx' h hy
  · obtain ⟨y, hy⟩ := ex hx' (0 : Fin 2)
    obtain ⟨z, hz⟩ := ex hx' (1 : Fin 2)
    have h₁ := hF'.2 2 _ _ y z hy hz
    rw [twoChart_addOf_pt_pt] at h₁
    have h₂ := hφi.twoChart_rep_of_id (hF.2 2 _ _ y z (hφ.twoChart_rep_of_id hy) (hφ.twoChart_rep_of_id hz))
    exact congrFun (uniq hx' h₁ h₂) i
  · obtain ⟨y, hy⟩ := ex hx' (0 : Fin 1)
    have h₁ := hα'.2 1 _ y hy
    have h₂ := hφi.twoChart_rep_of_id (hα.2 1 _ y (hφ.twoChart_rep_of_id hy))
    rw [gt_comp1_pt_right] at h₁ h₂
    exact uniq hx' h₁ h₂
end GlobalTheory.JetSer
