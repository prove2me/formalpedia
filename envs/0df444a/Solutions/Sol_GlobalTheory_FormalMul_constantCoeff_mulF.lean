-- Prove2me | solution 1 for GlobalTheory.FormalMul.constantCoeff_mulF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:30.907569+00:00
-- url     : https://prove2.me/submissions/ac1f8487-5a72-4853-8a72-4a27cc3b456a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MulFConstAndMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.FormalMul
namespace GlobalTheory.FormalMul
theorem _root_.solution {T : Type} [CommRing T] {d : ℕ} (F : Fin d → PS T 2 d)
    (hF : ∀ i, constantCoeff (F i) = 0) (N : ℕ) : ∀ j, constantCoeff (mulF F N j) = 0 := by
  induction N with
  | zero => intro j; simp [mulF]
  | succ n ih => exact gp_addOf F hF _ _ ih (gp_pt 0)
end GlobalTheory.FormalMul
