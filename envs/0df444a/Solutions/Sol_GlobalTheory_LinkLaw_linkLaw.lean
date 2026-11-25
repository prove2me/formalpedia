-- Prove2me | solution 1 for GlobalTheory.LinkLaw.linkLaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:14:28.916712+00:00
-- url     : https://prove2.me/submissions/9784d2ff-092c-4939-8d19-f6e021954a14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsLawOfOfMatch
import Theorems.Thm_GlobalTheory_LinkLaw_isLawOf_of_match
import Theorems.Thm_GlobalTheory_LinkLaw_isMapOf_of_match

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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LinkLaw
variable {V : Type} [CommRing V]
namespace GlobalTheory.LinkLaw
theorem _root_.solution : LinkLawSt := by
  intro E _ _ _ H V _ t d BT tg xT eT wPT hC _ _ x _ hM
  letI := H.starRing
  exact ⟨isLawOf_of_match BT.G.F BT.G.const xT hC.law x hM,
    fun α => isMapOf_of_match (BT.A.act α) (BT.A.const α) xT _ (fun m => hC.act m α) x hM⟩
end GlobalTheory.LinkLaw
