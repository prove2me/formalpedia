-- Prove2me | solution 1 for GlobalTheory.SS.ptEnd_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:54:53.769901+00:00
-- url     : https://prove2.me/submissions/9d0f2cca-f6c0-483d-a7d6-25c56df7d2eb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPositiveDefiniteQuadraticFormEndomorphismsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyTorsionFiniteEndomorphismDivisibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVectorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPolyNormSqRoots

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
open Polynomial
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
namespace GlobalTheory.SS
theorem _root_.solution (F : End B) (hF : IsMonHom (show B ⟶ B from F)) {Z : Over S} (x : Z ⟶ B) (n : ℕ) :
    (ptEnd F hF Z ^ n) (Additive.ofMul x) = Additive.ofMul (x ≫ (show B ⟶ B from F ^ n)) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact congrArg Additive.ofMul (Category.comp_id x).symm
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, ih]
    exact congrArg Additive.ofMul (Category.assoc x (show B ⟶ B from F ^ n) (show B ⟶ B from F))
end GlobalTheory.SS
