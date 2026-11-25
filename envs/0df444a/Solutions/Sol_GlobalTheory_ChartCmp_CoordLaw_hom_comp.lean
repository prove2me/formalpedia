-- Prove2me | solution 1 for GlobalTheory.ChartCmp.CoordLaw.hom_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:28:53.014518+00:00
-- url     : https://prove2.me/submissions/08beb163-41c2-4126-a3ee-fe66843d7548

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ChartLawActionEqTransportedOfCoordRel
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstPS_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstPS_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jet_hom_ext


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
theorem _root_.solution (m : ℕ) {κ κ' κ'' : Type} [Fintype κ'] [DecidableEq κ'] [Fintype κ''] [DecidableEq κ'']
    (g : κ → MvPowerSeries κ' V) (h : κ' → MvPowerSeries κ'' V) (hg : ∀ i, MvPowerSeries.constantCoeff (g i) = 0)
    (hh : ∀ i, MvPowerSeries.constantCoeff (h i) = 0) :
    Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) h) ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) g) =
      Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun i => MvPowerSeries.subst h (g i)) := by
  rw [GermD.homAt_comp]
  congr 1
  apply GermD.jet_hom_ext
  intro i
  rw [AlgHom.comp_apply, ExpChartJet.jetSubstPS_mk m g hg, ExpChartJet.jetSubstPS_psJet m h hh,
    ExpChartJet.jetSubstPS_mk m _ (fun i => MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero hh) hh (hg i))]
end GlobalTheory.ChartCmp.CoordLaw
