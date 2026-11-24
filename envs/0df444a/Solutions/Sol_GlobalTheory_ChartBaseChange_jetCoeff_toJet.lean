-- Prove2me | solution 1 for GlobalTheory.ChartBaseChange.jetCoeff_toJet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:42:48.063724+00:00
-- url     : https://prove2.me/submissions/705fdb4c-9ed3-462d-ba4e-7ff4881b98f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Theorems.Thm_GlobalTheory_ChartBaseChange_jetCoeff_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback pushHom)
open GlobalTheory.JetSer ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartBaseChange
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
namespace GlobalTheory.ChartBaseChange
theorem _root_.solution {κ : Type} [Finite κ] (m : ℕ) (g : MvPowerSeries κ R) :
    jetCoeff R R' κ m (toJet m g) = toJet m (MvPowerSeries.map (algebraMap R R') g) := by
  unfold toJet
  rw [jetCoeff_mk]
  congr 1
  ext e
  rw [MvPolynomial.coeff_map, coeff_truncTotal_eq_ite, coeff_truncTotal_eq_ite]
  split_ifs <;> simp
end GlobalTheory.ChartBaseChange
