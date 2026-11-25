-- Prove2me | solution 1 for GlobalTheory.FrameGeo.IsExpOf.neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:31:08.019629+00:00
-- url     : https://prove2.me/submissions/d8bf6fe4-bfbc-4f6f-b3c6-6844e4779caf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGoodConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ThreePointSeriesExponentialOfDefect
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FrameGeo
open GlobalTheory.FramePull ReciprocityTheory.ChartRestriction.G.TB
variable {R : Type} [CommRing R] {d : ℕ} {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace GlobalTheory.FrameGeo
namespace IsExpOf
theorem _root_.solution {v w : PS R 1 d} {f : PS k 1 d} (hf : IsExpOf v f) (hw : v * w = 1) : IsExpOf w (-f) := by
  have n0 : constantCoeff (-f) = 0 := by simp [hf.1]
  refine ⟨n0, ?_⟩
  have h1 : FB.toK k v * FB.toK k w = 1 := by rw [FB.toK, FB.toK, ← map_mul, hw, map_one]
  have h2 : FB.expS k (-f) * FB.expS k f = 1 := by
    unfold FB.expS
    rw [← WickVanishing.exp_add n0 hf.1, neg_add_cancel, WickVanishing.exp_zero]
  rw [hf.2] at h1
  calc FB.toK k w = (FB.expS k (-f) * FB.expS k f) * FB.toK k w := by rw [h2, _root_.one_mul]
    _ = FB.expS k (-f) := by rw [_root_.mul_assoc, h1, _root_.mul_one]
end IsExpOf
end GlobalTheory.FrameGeo
