-- Prove2me | solution 1 for GlobalTheory.ChartCmp.GaugeDiff.map_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:31:59.613078+00:00
-- url     : https://prove2.me/submissions/c1ca46de-6288-426a-9048-c0bed9b6bdfc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqFormalExpIffAndExistsLog
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonicalGaugeDifferenceBiadditiveJet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_hasSubst


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
theorem _root_.solution {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j, GP (a j)) (f : PS R m d) :
    MvPowerSeries.map β (ev a f) = ev (fun j => mapPt β (a j)) (MvPowerSeries.map β f) :=
  MvPowerSeries.map_subst (gt_hasSubst a ha) f
end GlobalTheory.ChartCmp.GaugeDiff
