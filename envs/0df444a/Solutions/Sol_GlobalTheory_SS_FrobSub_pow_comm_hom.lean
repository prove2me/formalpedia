-- Prove2me | solution 1 for GlobalTheory.SS.FrobSub.pow_comm_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:19:13.330672+00:00
-- url     : https://prove2.me/submissions/a8716cbd-d17a-4bce-9ead-e6e5e0a59562

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FrobGPowAndClosedSubgroup

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobSub
namespace GlobalTheory.SS.FrobSub
theorem _root_.solution {C : Type*} [Category C] {N G : C} (ν : N ⟶ G) (F : End G) (F' : End N)
    (h : (show N ⟶ N from F') ≫ ν = ν ≫ (show G ⟶ G from F)) (m : ℕ) :
    (show N ⟶ N from F' ^ m) ≫ ν = ν ≫ (show G ⟶ G from F ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [pow_succ, End.mul_def, Category.assoc] at *
    rw [ih, reassoc_of% h]
end GlobalTheory.SS.FrobSub
