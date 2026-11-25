-- Prove2me | solution 1 for GlobalTheory.ChartCmp.GaugeDiff.jeq_of_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:14:42.402096+00:00
-- url     : https://prove2.me/submissions/c590e72a-56b3-4433-b4ae-11080665a81b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqFormalExpIffAndExistsLog
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonicalGaugeDifferenceBiadditiveJet

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
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.ChartCmp.GaugeDiff
theorem _root_.solution {σ : Type} {m : ℕ} {f g u v : MvPowerSeries σ k} (h : JEq m f g) (e : u - v = f - g) :
    JEq m u v := fun x hx => by
  have := congrArg (MvPowerSeries.coeff x) e
  rw [map_sub, map_sub, h x hx, sub_self] at this
  exact sub_eq_zero.1 this
end GlobalTheory.ChartCmp.GaugeDiff
