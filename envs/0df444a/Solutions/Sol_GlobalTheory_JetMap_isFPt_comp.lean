-- Prove2me | solution 1 for GlobalTheory.JetMap.isFPt_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:23:21.27285+00:00
-- url     : https://prove2.me/submissions/3272592d-dacf-4822-8018-1e5af94e6757

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ToJetOneEqSum

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
theorem _root_.solution {R : Type} [CommRing R] {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [GrpObj G']
    {κ : Type} {y : Fam G κ} (hy : IsFPt y) (f : G ⟶ G') (hf : η[G] ≫ f = η[G']) :
    IsFPt (fun m => y m ≫ f : Fam G' κ) := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · show spMap _ ≫ y (m + 1) ≫ f = y m ≫ f
    rw [← Category.assoc, hy.1 m]
  · show spMap _ ≫ y m ≫ f = 1
    rw [← Category.assoc, hy.2 m, Hom.one_def, Hom.one_def, Category.assoc, hf]
end GlobalTheory.JetMap
