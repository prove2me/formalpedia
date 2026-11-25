-- Prove2me | solution 1 for GlobalTheory.T.universalJets_power_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:47:18.1678+00:00
-- url     : https://prove2.me/submissions/dc8f34a3-7825-4c95-bc7c-d1793dd06cec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalJetsPowerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalJetsPowerProductStatement
import Theorems.Thm_GlobalTheory_PowGerm_univPow


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
theorem _root_.solution : UnivPowSt := by
  first | exact @GlobalTheory.PowGerm.univPow | exact GlobalTheory.PowGerm.univPow | (intros; apply GlobalTheory.PowGerm.univPow <;> assumption)
end _root_.GlobalTheory.T
