-- Prove2me | solution 1 for GlobalTheory.ChartAction.actSt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:26:30.647317+00:00
-- url     : https://prove2.me/submissions/d08ab938-a473-4c66-8b28-4b0f4cab8d47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ActStOf
import Theorems.Thm_GlobalTheory_ChartAction_rep_unique
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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartAction
namespace GlobalTheory.ChartAction
theorem _root_.solution (_ : JetAlgSt) (hR : RepSt) (hM : MapSt) : ActSt := by
  intro R _ G _ _ d x hx O _ act Gl hF
  have hex : ∀ a, ∃ φ, IsMapOf x x (act.act a) φ := fun a => by
    haveI := act.hom a
    exact (hM R G G d x x hx hx (act.act a) (IsMonHom.one_hom _)).exists
  choose φ hφ using hex
  have hpt : ∀ (n : ℕ) (j : Fin n), ∃ y, Rep x (pt R (n := n) d j) y := fun n j =>
    ((hR R G d x hx (Fin n × Fin d)).1 _ (gp_pt j)).exists
  choose y hy using hpt
  have h1 : ∀ a, Rep x (φ a) (fun m => y 1 0 m ≫ act.act a) := fun a => by
    have := (hφ a).2 1 _ _ (hy 1 0)
    rwa [gt_comp1_pt_right] at this
  refine ⟨⟨φ, fun a => (hφ a).1, fun a => ?_, fun a b => ?_, fun a b => ?_, ?_⟩, hφ⟩
  · haveI := act.hom a
    refine rep_unique hR hx ((hφ a).2 2 _ _ (hF.2 2 _ _ _ _ (hy 2 0) (hy 2 1)))
      (hF.2 2 _ _ _ _ ((hφ a).2 2 _ _ (hy 2 0)) ((hφ a).2 2 _ _ (hy 2 1))) ?_
    funext m
    exact MonObj.mul_comp _ _ _
  · refine rep_unique hR hx (h1 (a + b)) (hF.2 1 _ _ _ _ (h1 a) (h1 b)) ?_
    funext m
    rw [act.add]
    exact MonObj.comp_mul _ _ _
  · refine rep_unique hR hx (h1 (a * b)) ((hφ a).2 1 _ _ (h1 b)) ?_
    funext m
    rw [mul_comm, act.mul, Category.assoc]
  · refine rep_unique hR hx (h1 1) (hy 1 0) ?_
    funext m
    rw [act.one, Category.comp_id]
end GlobalTheory.ChartAction
