-- Prove2me | solution 1 for GlobalTheory.JetSer.isFPt_of_isUnivChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:41:27.861242+00:00
-- url     : https://prove2.me/submissions/440124e5-8f35-4fd1-9b04-589a6ed29240

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RepJetAugCompTrunc
import Theorems.Thm_GlobalTheory_JetSer_rep_jetAug_comp_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp


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
open ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer
variable {R : Type} [CommRing R]
namespace GlobalTheory.JetSer
theorem _root_.solution {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : Fam G (Fin d)}
    (hx : IsUnivChart G d x) : IsFPt x := by
  refine ⟨hx.1, fun m => ?_⟩
  rw [← rep_jetAug_comp_zero, ← spMap_comp, Category.assoc, hx.2.1 m]
  exact MonObj.comp_one _
end GlobalTheory.JetSer
