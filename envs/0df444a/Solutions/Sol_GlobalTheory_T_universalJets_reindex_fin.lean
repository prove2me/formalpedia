-- Prove2me | solution 1 for GlobalTheory.T.universalJets_reindex_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:46:14.137418+00:00
-- url     : https://prove2.me/submissions/46d337fe-a9be-46ee-9a64-9ee95456b0f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalJetsReindexFin
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalJetsReindexFinStatement
import Theorems.Thm_GlobalTheory_PowGerm_univConv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : UnivConvSt := by
  first | exact @GlobalTheory.PowGerm.univConv | exact GlobalTheory.PowGerm.univConv | (intros; apply GlobalTheory.PowGerm.univConv <;> assumption)
end _root_.GlobalTheory.T
