-- Prove2me | solution 1 for GlobalTheory.ChartCmp.GaugeDiff.mapPt_addOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:09.913944+00:00
-- url     : https://prove2.me/submissions/3942535e-fc76-45a4-98e3-b7a56c5865a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqFormalExpIffAndExistsLog
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonicalGaugeDifferenceBiadditiveJet
import Theorems.Thm_GlobalTheory_ChartCmp_GaugeDiff_map_ev2

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
theorem _root_.solution {n : ℕ} (F : Fin d → PS R 2 d) (a b : Pt R n d) (ha : GP a) (hb : GP b) :
    mapPt β (addOf F a b) = addOf (mapPt β F) (mapPt β a) (mapPt β b) :=
  funext fun i => map_ev2 β a b ha hb (F i)
end GlobalTheory.ChartCmp.GaugeDiff
