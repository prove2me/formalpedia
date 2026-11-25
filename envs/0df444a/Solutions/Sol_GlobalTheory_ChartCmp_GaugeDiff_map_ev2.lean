-- Prove2me | solution 1 for GlobalTheory.ChartCmp.GaugeDiff.map_ev2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:49:23.768869+00:00
-- url     : https://prove2.me/submissions/52ee9993-f5d1-4f81-a914-d1db03c55def

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqFormalExpIffAndExistsLog
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonicalGaugeDifferenceBiadditiveJet
import Theorems.Thm_GlobalTheory_ChartCmp_GaugeDiff_map_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (transF IsInvPair)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open MvPowerSeries
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.GaugeDiff
variable {R k : Type} [CommRing R] [CommRing k] {d : ℕ} (β : R →+* k)
namespace GlobalTheory.ChartCmp.GaugeDiff
theorem _root_.solution {n : ℕ} (a b : Pt R n d) (ha : GP a) (hb : GP b) (f : PS R 2 d) :
    MvPowerSeries.map β (ev ![a, b] f) = ev ![mapPt β a, mapPt β b] (MvPowerSeries.map β f) := by
  rw [map_ev β _ (pair_points_zero_constant ha hb)]
  congr 1
  funext j; fin_cases j <;> rfl
end GlobalTheory.ChartCmp.GaugeDiff
