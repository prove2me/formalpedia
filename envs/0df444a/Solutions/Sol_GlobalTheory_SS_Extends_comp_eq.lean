-- Prove2me | solution 1 for GlobalTheory.SS.Extends.comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:16:44.437647+00:00
-- url     : https://prove2.me/submissions/0927c724-120a-421c-b2f5-5b408e38b935

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelExtensionOfDefinedAtPoints

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
open GlobalTheory GlobalTheory.SS
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (Sp K)}
variable [IsDomain R] [IsFractionRing R K]
omit [IsDomain R] [IsFractionRing R K]
namespace GlobalTheory.SS
namespace Extends
theorem _root_.solution {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {U : M.Y.left.Opens}
    {g : U.toScheme ⟶ N.Y.left} (h : Extends M N f U g) {W : Scheme.{0}} (u : W ⟶ U.toScheme)
    (v : W ⟶ A.left) (e : u ≫ U.ι = v ≫ M.j) : u ≫ g = v ≫ f.left ≫ N.j := by
  have P := isPullback_morphismRestrict M.j U
  rw [← P.lift_fst u v e, Category.assoc, h.2, P.lift_snd_assoc]
end Extends
end GlobalTheory.SS
