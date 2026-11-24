-- Prove2me | solution 1 for GlobalTheory.ChartJLaw.constantCoeff_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:10:55.582981+00:00
-- url     : https://prove2.me/submissions/30cffcf7-18e9-4095-ac41-0391a4ecadaa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsFormalGroupLawOfChartOfJetChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ChartJLaw
variable {T : Type} [CommRing T] {d : ℕ}
namespace GlobalTheory.ChartJLaw
theorem _root_.solution {k n : ℕ} (a : Fin k → Pt T n d) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0)
    (f : PS T k d) (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 := by
  unfold ev
  have h1 : ∀ p : Fin k × Fin d, MvPowerSeries.constantCoeff ((fun p : Fin k × Fin d => a p.1 p.2) p) = 0 :=
    fun p => ha p.1 p.2
  exact MvPowerSeries.constantCoeff_subst_eq_zero (a := fun p : Fin k × Fin d => a p.1 p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero h1) h1 hf
end GlobalTheory.ChartJLaw
