-- Prove2me | solution 1 for GlobalTheory.T.constantCoeff_invariantPolyOperator_jetEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:37:32.335848+00:00
-- url     : https://prove2.me/submissions/06ea2ec1-337a-49f5-8dc5-d98c2ffbb085

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffInvariantPolyOperatorJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffInvariantPolyOperatorJetEqStatement
import Theorems.Thm_GlobalTheory_ChartCmp_constantCoeff_DpolyN_jEq


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
theorem _root_.solution : ∀ (k : Type) [CommRing k] (d n : ℕ) (F : Fin d → PS k 2 d) (Ix : Type) [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k) (P : MvPolynomial Ix k) (m : ℕ) (f g : PS k n d), P.totalDegree ≤ m → JEq m f g → MvPowerSeries.constantCoeff (DpolyN F cp u P f) = MvPowerSeries.constantCoeff (DpolyN F cp u P g) := by
  first | exact @GlobalTheory.ChartCmp.constantCoeff_DpolyN_jEq | exact GlobalTheory.ChartCmp.constantCoeff_DpolyN_jEq | (intros; apply GlobalTheory.ChartCmp.constantCoeff_DpolyN_jEq <;> assumption)
end _root_.GlobalTheory.T
