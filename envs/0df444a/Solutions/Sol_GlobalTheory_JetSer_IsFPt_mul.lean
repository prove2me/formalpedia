-- Prove2me | solution 1 for GlobalTheory.JetSer.IsFPt.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:23:23.338885+00:00
-- url     : https://prove2.me/submissions/a2def355-8b69-4562-a76b-5c14b50f32d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AddOfPtPt

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
namespace IsFPt
theorem _root_.solution {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {κ : Type}
    {y z : Fam G κ} (hy : IsFPt y) (hz : IsFPt z) : IsFPt (fun m => y m * z m : Fam G κ) := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · show _ ≫ (y (m + 1) * z (m + 1)) = y m * z m
    rw [MonObj.comp_mul, hy.1 m, hz.1 m]
  · show _ ≫ (y m * z m) = 1
    rw [MonObj.comp_mul, hy.2 m, hz.2 m, _root_.mul_one]
end IsFPt
end GlobalTheory.JetSer
