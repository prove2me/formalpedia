-- Prove2me | solution 1 for GlobalTheory.SS.FrobLB.Fix.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:35:48.416606+00:00
-- url     : https://prove2.me/submissions/a7b6e319-16bc-4017-976a-1ad857764aa0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PullPowOfFix
import Theorems.Thm_GlobalTheory_SS_FrobLB_Fix_id
import Theorems.Thm_GlobalTheory_SS_FrobLB_Fix_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobLB
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw
namespace GlobalTheory.SS.FrobLB
namespace Fix
theorem _root_.solution {S : Scheme.{0}} {G : Over S} {F : End G} {U : G.left.Opens} {f : Γ(G.left, U)} {q m : ℕ}
    (h : Fix (show G ⟶ G from F ^ m).left U f (q ^ m)) (l : ℕ) :
    Fix (show G ⟶ G from F ^ (m * l)).left U f (q ^ (m * l)) := by
  induction l with
  | zero => exact Fix.id U f
  | succ l ih =>
    rw [mul_add, Nat.mul_one, pow_add, pow_add, mul_comm (q ^ _)]
    exact h.comp ih
end Fix
end GlobalTheory.SS.FrobLB
