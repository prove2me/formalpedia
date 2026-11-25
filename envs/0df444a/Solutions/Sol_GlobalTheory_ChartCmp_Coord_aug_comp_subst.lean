-- Prove2me | solution 1 for GlobalTheory.ChartCmp.Coord.aug_comp_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:38:19.345647+00:00
-- url     : https://prove2.me/submissions/528c80a7-8d95-4a73-94ac-8129170ff166

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsCoordinateRelationUniversalJets
import Theorems.Thm_GlobalTheory_ChartCmp_Coord_aug_X
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstPS_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_jetAug_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jet_hom_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.Coord
open Formalism.MainNotions.ModuliIntegralCharts.H1
variable {V : Type} [CommRing V]
namespace GlobalTheory.ChartCmp.Coord
theorem _root_.solution {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (m : ℕ)
    (φ : κ → MvPowerSeries κ' V) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    (jetAug : Jet V κ' m →ₐ[V] V).comp (jetSubstPS (m := m) φ) = jetAug := by
  apply GermD.jet_hom_ext
  intro i
  rw [AlgHom.comp_apply, ExpChartJet.jetSubstPS_mk m φ hφ, GaugeR.jetAug_psJet, hφ, aug_X]
end GlobalTheory.ChartCmp.Coord
