-- Prove2me | solution 1 for GlobalTheory.ChartCmp.CoordLaw.germCompOne_assoc_of_constantCoeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:38:24.36628+00:00
-- url     : https://prove2.me/submissions/6e55315f-b11e-42fc-aa9a-b46e0f08bb2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ChartLawActionEqTransportedOfCoordRel
import Theorems.Thm_GlobalTheory_ChartCmp_CoordLaw_ev_one_eq

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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.CoordLaw
open Formalism.MainNotions.ModuliIntegralCharts.H1
variable {V : Type} [CommRing V] {d : ℕ}
namespace GlobalTheory.ChartCmp.CoordLaw
theorem _root_.solution {n : ℕ} (ψ φ : Pt V 1 d) (a : Pt V n d) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) : comp1 (comp1 ψ φ) a = comp1 ψ (comp1 φ a) := by
  funext i
  simp only [comp1, ev_one_eq]
  exact MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin d => hφ p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin d => ha p.2) _
end GlobalTheory.ChartCmp.CoordLaw
