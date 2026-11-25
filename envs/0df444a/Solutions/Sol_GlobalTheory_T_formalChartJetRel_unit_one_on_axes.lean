-- Prove2me | solution 1 for GlobalTheory.T.formalChartJetRel_unit_one_on_axes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:35:34.349434+00:00
-- url     : https://prove2.me/submissions/47a8b8e1-0efe-4faf-b783-88b8d078e107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxesStatement
import Theorems.Thm_GlobalTheory_ChartCmp_jRel_axes


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (m : ℕ) (B B' : FB R d O) (φ φi : Pt R 1 d) (ε : PS R 2 d), JRel m B B' φ φi ε → MvPowerSeries.constantCoeff ε = 1 ∧ JEq m (ev (n := 1) ![0, pt R (n := 1) d 0] ε) 1 ∧ JEq m (ev (n := 1) ![pt R (n := 1) d 0, 0] ε) 1 := by
  first | exact @GlobalTheory.ChartCmp.jRel_axes | exact GlobalTheory.ChartCmp.jRel_axes | (intros; apply GlobalTheory.ChartCmp.jRel_axes <;> assumption)
end _root_.GlobalTheory.T
