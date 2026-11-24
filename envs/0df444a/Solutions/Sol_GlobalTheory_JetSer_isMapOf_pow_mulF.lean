-- Prove2me | solution 1 for GlobalTheory.JetSer.isMapOf_pow_mulF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:21:23.077949+00:00
-- url     : https://prove2.me/submissions/a9b5e9df-3b12-4e0e-afa5-7afd22e68296

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RepJetAugCompTrunc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsSeriesOfMorphismInChartsPowMulFormalGroupLaw
import Theorems.Thm_GlobalTheory_JetSer_jetAlg
import Theorems.Thm_GlobalTheory_JetSer_repSt_of_jetAlgSt
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
namespace GlobalTheory.JetSer
theorem _root_.solution : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (d : ℕ) (x : GlobalTheory.JetSer.Fam G (Fin d)), Chart.IsUnivChart G d x → ∀ F : Fin d → PS R 2 d, GlobalTheory.JetSer.IsLawOf x F → ∀ N : ℕ, GlobalTheory.JetSer.IsMapOf x x ((𝟙 G) ^ N : G ⟶ G) (mulF F N) := by
  intro R _ G _ d x hx F hF N
  induction N with
  | zero =>
    refine ⟨gp_zero₂, fun n a y h => ?_⟩
    have h0 := (repSt_of_jetAlgSt jetAlg R G d x hx (Fin n × Fin d)).2.2.2.1
    have e : comp1 (mulF F 0) a = 0 := evP_zero ![a] (single_point_zero_constant h.1)
    rw [e, pow_zero]
    simpa only [MonObj.comp_one] using h0
  | succ N ih =>
    refine ⟨gp_addOf F hF.1 _ _ ih.1 (gp_pt 0), fun n a y h => ?_⟩
    have e : comp1 (mulF F (N + 1)) a = addOf F (comp1 (mulF F N) a) a := by
      have e1 := evP_addOf ![a] (single_point_zero_constant h.1) F (mulF F N) (pt R d 0) ih.1 (gp_pt 0)
      rw [evP_pt _ (single_point_zero_constant h.1)] at e1
      exact e1
    rw [e, pow_succ]
    simpa only [MonObj.comp_mul, Category.comp_id] using hF.2 n _ _ _ _ (ih.2 n a y h) h
end GlobalTheory.JetSer
