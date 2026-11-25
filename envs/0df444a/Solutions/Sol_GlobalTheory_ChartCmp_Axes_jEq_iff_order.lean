-- Prove2me | solution 1 for GlobalTheory.ChartCmp.Axes.jEq_iff_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:17:09.651831+00:00
-- url     : https://prove2.me/submissions/bf83a020-6a6c-486a-8763-ff48d1bc448f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes

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
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.Axes
variable {R : Type} [CommRing R]
namespace GlobalTheory.ChartCmp.Axes
theorem _root_.solution {σ : Type} (m : ℕ) (f g : MvPowerSeries σ R) :
    JEq m f g ↔ ((m + 1 : ℕ) : ℕ∞) ≤ MvPowerSeries.order (f - g) := by
  constructor
  · intro h
    refine MvPowerSeries.nat_le_order fun e he => ?_
    rw [map_sub, h e (by omega), sub_self]
  · intro h e he
    have : MvPowerSeries.coeff e (f - g) = 0 :=
      MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le he) h)
    rwa [map_sub, sub_eq_zero] at this
end GlobalTheory.ChartCmp.Axes
