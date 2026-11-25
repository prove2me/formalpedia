-- Prove2me | solution 1 for GlobalTheory.ChartCmp.Axes.jEq_one_of_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:11:02.475805+00:00
-- url     : https://prove2.me/submissions/50bc6ba8-58ea-470f-98bb-a262f7827974

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
import Theorems.Thm_GlobalTheory_ChartCmp_Axes_jEq_mul_right

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
theorem _root_.solution {σ : Type} {m : ℕ} {e : MvPowerSeries σ R} (hu : IsUnit (MvPowerSeries.constantCoeff e))
    (h : JEq m e (e * e)) : JEq m e 1 := by
  obtain ⟨u, rfl⟩ := MvPowerSeries.isUnit_iff_constantCoeff.2 hu
  have := jEq_mul_right (↑u⁻¹ : MvPowerSeries σ R) h
  rw [_root_.mul_assoc, Units.mul_inv, _root_.mul_one] at this
  exact fun e he => (this e he).symm
end GlobalTheory.ChartCmp.Axes
