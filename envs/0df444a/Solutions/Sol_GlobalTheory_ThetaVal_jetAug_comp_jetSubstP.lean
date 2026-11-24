-- Prove2me | solution 1 for GlobalTheory.ThetaVal.jetAug_comp_jetSubstP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:32:49.934295+00:00
-- url     : https://prove2.me/submissions/0cea0b23-6fba-48bb-a095-6b26019fc9cc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FrameRigidificationOfCanonicalAxes
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open GlobalTheory GlobalTheory.ThetaVal
namespace GlobalTheory.ThetaVal
theorem _root_.solution {S A B : Type} [CommRing S] (m : ℕ) (φ : A → MvPolynomial B S) :
    (jetAug : Jet S B m →ₐ[S] S).comp (jetSubstP m φ) = (jetAug : Jet S A m →ₐ[S] S) := by
  apply Ideal.Quotient.algHom_ext S
  apply MvPolynomial.algHom_ext
  intro i
  simp [jetSubstP, jetAug, jetMap, liftJet]
  erw [Ideal.Quotient.lift_mk]
  simp
end GlobalTheory.ThetaVal
