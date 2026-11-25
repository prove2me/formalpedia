-- Prove2me | solution 1 for GlobalTheory.LinkSec.comp_psum_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:16:34.815863+00:00
-- url     : https://prove2.me/submissions/93ac732e-25d0-46ed-a55c-5c1bee53fc62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsLawOfOfMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ValSerGermFnVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GsSpMapGermAt

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
open GlobalTheory GlobalTheory.LinkSec
namespace GlobalTheory.LinkSec
theorem _root_.solution {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (s : T ⟶ T') (x₀ x₁ : T' ⟶ G)
    (I : Finset (Fin 2)) : s.left ≫ (psum G ![x₀, x₁] I).left = (psum G ![s ≫ x₀, s ≫ x₁] I).left := by
  have e : s ≫ psum G ![x₀, x₁] I = psum G ![s ≫ x₀, s ≫ x₁] I := by
    fin_cases I
    · exact MonObj.comp_one _
    · exact MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·) (MonObj.comp_one _))
    · exact MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·) (MonObj.comp_one _))
    · exact MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·)
        (MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·) (MonObj.comp_one _))))
  exact congrArg CommaMorphism.left e
end GlobalTheory.LinkSec
