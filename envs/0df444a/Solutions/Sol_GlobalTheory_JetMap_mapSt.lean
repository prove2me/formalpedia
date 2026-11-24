-- Prove2me | solution 1 for GlobalTheory.JetMap.mapSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:40:02.483456+00:00
-- url     : https://prove2.me/submissions/bbb7ef8b-3b29-4118-923a-b09a3e93d6ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ToJetOneEqSum
import Theorems.Thm_GlobalTheory_JetMap_isFPt_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt_right
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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetMap
namespace GlobalTheory.JetMap
theorem _root_.solution (hJ : JetAlgSt) (hR : RepSt) : MapSt := by
  intro R _ G _ G' _ d x x' hx hx' f hf
  obtain ⟨hex, -, hfp, -, hsub⟩ := hR R G d x hx (Fin 1 × Fin d)
  obtain ⟨-, hco', -, -, hsub'⟩ := hR R G' d x' hx' (Fin 1 × Fin d)
  obtain ⟨y₀, hy₀, -⟩ := hex (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n := 1) d 0) (gp_pt 0)
  obtain ⟨φ, hφ, hu⟩ := hco' _ (isFPt_comp (hfp _ _ hy₀) f hf)
  refine ⟨φ, ⟨hφ.1, fun n a y hy => ?_⟩, fun φ' hφ' => ?_⟩
  · have hb : ∀ p : Fin 1 × Fin d, constantCoeff ((![a] : Fin 1 → Pt R n d) p.1 p.2) = 0 :=
      fun p => single_point_zero_constant (a := a) hy.1 p.1 p.2
    have hψ := fun m => ((hJ R (Fin n × Fin d)).2.2.2.2 (Fin 1 × Fin d) _ hb m).1
    choose ψ hψ using hψ
    have h1 := hsub (Fin n × Fin d) _ ψ hb hψ _ _ hy₀
    have h2 := hsub' (Fin n × Fin d) _ ψ hb hψ _ _ hφ
    have h1' : Rep x a (fun m => spMap (ψ m) ≫ y₀ m) := by
      have := gt_comp1_pt a hy.1
      rw [← this]
      exact h1
    have e : y = fun m => spMap (ψ m) ≫ y₀ m :=
      ((hR R G d x hx (Fin n × Fin d)).1 a hy.1).unique hy h1'
    subst e
    simp only [Category.assoc]
    exact h2
  · have := hφ'.2 1 _ _ hy₀
    rw [gt_comp1_pt_right] at this
    exact hu _ this
end GlobalTheory.JetMap
