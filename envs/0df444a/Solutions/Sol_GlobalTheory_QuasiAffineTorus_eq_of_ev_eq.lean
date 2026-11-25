-- Prove2me | solution 1 for GlobalTheory.QuasiAffineTorus.eq_of_ev_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:07:48.120972+00:00
-- url     : https://prove2.me/submissions/d9275334-1968-4823-bc6b-b2ff618c56df

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyReducedOfPerfectField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiAffineSubgroupContainingTorusEqTorus
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_appTop_eq_of_ev_eq

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
open GlobalTheory GlobalTheory.QuasiAffineTorus
open RationalPoint
variable {k : Type} [Field k]
namespace GlobalTheory.QuasiAffineTorus
theorem _root_.solution {N : Over (Sp k)} [N.left.IsQuasiAffine] {x y : 𝟙_ (Over (Sp k)) ⟶ N}
    (h : ∀ f, ev x f = ev y f) : x = y := by
  have h1 : x.left.appTop = y.left.appTop := by
    ext f
    exact appTop_eq_of_ev_eq (h f)
  ext1
  rw [← cancel_mono N.left.toSpecΓ, Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, h1]
end GlobalTheory.QuasiAffineTorus
