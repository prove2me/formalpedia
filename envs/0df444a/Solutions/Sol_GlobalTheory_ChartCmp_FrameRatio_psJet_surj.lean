-- Prove2me | solution 1 for GlobalTheory.ChartCmp.FrameRatio.psJet_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:29:39.858815+00:00
-- url     : https://prove2.me/submissions/8540bb9b-7396-44be-81b3-26f01a07eed2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetFramesDifferByUnitEachOrder
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_psJet_eq_mk


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
open Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.FrameRatio
namespace GlobalTheory.ChartCmp.FrameRatio
theorem _root_.solution {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (m : ℕ) (a : Jet R κ m) :
    ∃ f : MvPowerSeries κ R, psJet m f = a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨(p : MvPowerSeries κ R), GaugeR.psJet_eq_mk m _ p fun e _ => (MvPolynomial.coeff_coe p e).symm⟩
end GlobalTheory.ChartCmp.FrameRatio
