-- Prove2me | solution 1 for GlobalTheory.ChartCmp.BilAdd.eq_zero_of_double
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:54:26.244612+00:00
-- url     : https://prove2.me/submissions/d0b8eddd-3bae-4ff8-be6f-1221719734e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesJetEqCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqBilinearSeriesOfBiadditive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.BilAdd
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.ChartCmp.BilAdd
theorem _root_.solution [Algebra ℚ k] {a : ℕ} (ha : a ≠ 1) {c : k} (h : 2 ^ a * c = c + c) : c = 0 := by
  have h0 : ((2 : ℚ) ^ a - 2) ≠ 0 := by
    intro h
    apply ha
    have : (2 : ℚ) ^ a = 2 ^ 1 := by linarith
    exact (pow_right_injective₀ (by norm_num) (by norm_num)) this
  have hu : IsUnit ((2 : k) ^ a - 2) := by
    have := (IsUnit.mk0 _ h0).map (algebraMap ℚ k)
    simpa [map_ofNat] using this
  apply hu.mul_right_eq_zero.mp
  linear_combination h
end GlobalTheory.ChartCmp.BilAdd
