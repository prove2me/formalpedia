-- Prove2me | solution 1 for GlobalTheory.SS.ArcInf.TwoVarSetup.laurent_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:16:49.715686+00:00
-- url     : https://prove2.me/submissions/b43c50aa-e3bc-430c-95de-43baa070a47f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasicOpenFactorFieldPointAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsArcQuotientTwoVariableCoords

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.ArcInf GlobalTheory.SS.ArcInf.TwoVarSetup
variable {k : Type} [Field k]
namespace GlobalTheory.SS.ArcInf.TwoVarSetup
theorem _root_.solution {F : Type} [CommRing F] [Algebra k F] {a b : FractionRing (PowerSeries k) →ₐ[k] F}
    (h : ∀ x : PowerSeries k, a (algebraMap _ _ x) = b (algebraMap _ _ x)) : a = b := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (nonZeroDivisors (PowerSeries k))
  exact RingHom.ext h
end GlobalTheory.SS.ArcInf.TwoVarSetup
