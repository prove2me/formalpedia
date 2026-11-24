-- Prove2me | solution 1 for GlobalTheory.SS.FrobField.over_pow_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:19:14.625228+00:00
-- url     : https://prove2.me/submissions/3ff816c1-cfdb-4bd4-b146-649bbe6d70d8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFrobGBaseChange

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
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobField
namespace GlobalTheory.SS.FrobField
theorem _root_.solution {S : Scheme.{0}} {G : Over S} (F : End G) (m : ℕ) :
    (show G ⟶ G from F ^ m).left = (show G.left ⟶ G.left from
      (show End G.left from (show G ⟶ G from F).left) ^ m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, pow_succ, End.mul_def, End.mul_def]
    exact (Over.comp_left _ _ _ _ _).trans (congrArg _ ih)
end GlobalTheory.SS.FrobField
