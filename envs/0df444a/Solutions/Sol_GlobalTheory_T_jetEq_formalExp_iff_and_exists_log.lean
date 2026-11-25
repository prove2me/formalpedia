-- Prove2me | solution 1 for GlobalTheory.T.jetEq_formalExp_iff_and_exists_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:51:41.56303+00:00
-- url     : https://prove2.me/submissions/f2e71c02-de34-41c9-892c-c6d5faaac772

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqFormalExpIffAndExistsLog
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqFormalExpIffAndExistsLogStatement
import Theorems.Thm_GlobalTheory_ChartCmp_jeq_expS_iff_and_exists_log


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
theorem _root_.solution : ∀ (k : Type) [CommRing k] [Algebra ℚ k] (n d m : ℕ), (∀ f g : PS k n d, MvPowerSeries.constantCoeff f = 0 → MvPowerSeries.constantCoeff g = 0 → (JEq m f g ↔ JEq m (FB.expS k f) (FB.expS k g))) ∧ ∀ u : PS k n d, MvPowerSeries.constantCoeff u = 1 → ∃ lam : PS k n d, MvPowerSeries.constantCoeff lam = 0 ∧ FB.expS k lam = u := by
  first | exact @GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log | exact GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log | (intros; apply GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log <;> assumption)
end _root_.GlobalTheory.T
