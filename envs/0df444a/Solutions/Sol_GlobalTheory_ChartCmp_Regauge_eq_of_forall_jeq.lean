-- Prove2me | solution 1 for GlobalTheory.ChartCmp.Regauge.eq_of_forall_jeq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:39:39.598027+00:00
-- url     : https://prove2.me/submissions/5623e33c-a920-45d4-9c0b-25f4035addca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsCanonicalGaugeSubBiadditive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.Regauge
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
namespace GlobalTheory.ChartCmp.Regauge
theorem _root_.solution {R σ : Type} [CommRing R] {f g : MvPowerSeries σ R} (h : ∀ m, JEq m f g) : f = g :=
  MvPowerSeries.ext fun e => h e.degree e le_rfl
end GlobalTheory.ChartCmp.Regauge
