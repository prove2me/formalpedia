-- Prove2me | solution 1 for GlobalTheory.ChartCmp.JCalc.coeff_psTrunc_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:50:39.450815+00:00
-- url     : https://prove2.me/submissions/1c3e011f-7e34-473c-83cb-91f09f63697a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesJetEqCalculus
import Theorems.Thm_GlobalTheory_ChartCmp_JCalc_mem_degLE_iff

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.JCalc
variable {R : Type} [CommRing R] {σ : Type} {m : ℕ}
namespace GlobalTheory.ChartCmp.JCalc
theorem _root_.solution [Fintype σ] [DecidableEq σ] (f : MvPowerSeries σ R) (e : σ →₀ ℕ) :
    (psTrunc m f).coeff e = if e.degree ≤ m then MvPowerSeries.coeff e f else 0 := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp [mem_degLE_iff]
end GlobalTheory.ChartCmp.JCalc
