-- Prove2me | solution 1 for GlobalTheory.FrameGeo.IsExpOf.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:58:02.48+00:00
-- url     : https://prove2.me/submissions/564aae79-86dc-443e-a7d6-823143ae760d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGoodConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ThreePointSeriesExponentialOfDefect
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_add


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
theorem _root_.solution {v w : PS R 1 d} {f g : PS k 1 d} (hf : IsExpOf v f) (hg : IsExpOf w g) :
    IsExpOf (v * w) (f + g) := by
  refine ⟨by simp [hf.1, hg.1], ?_⟩
  rw [FB.toK, map_mul]
  unfold FB.expS
  rw [WickVanishing.exp_add hf.1 hg.1]
  exact congrArg₂ (· * ·) hf.2 hg.2
end IsExpOf
end GlobalTheory.FrameGeo
