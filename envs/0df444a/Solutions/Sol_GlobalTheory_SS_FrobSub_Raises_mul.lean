-- Prove2me | solution 1 for GlobalTheory.SS.FrobSub.Raises.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:35:50.416254+00:00
-- url     : https://prove2.me/submissions/dafeef42-b27f-47ee-8a14-8c59e983662f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FrobGPowAndClosedSubgroup
import Theorems.Thm_GlobalTheory_SS_FrobSub_Raises_comp

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
namespace Raises
theorem _root_.solution {S : Scheme.{0}} {G : Over S} (F : End G) (q m : ℕ) {U : G.left.Opens} {f : Γ(G.left, U)}
    (h : Raises (show G ⟶ G from F ^ m).left (q ^ m) U f) (n : ℕ) (hn : 1 ≤ n) :
    Raises (show G ⟶ G from F ^ (m * n)).left (q ^ (m * n)) U f := by
  induction n, hn using Nat.le_induction with
  | base => rwa [Nat.mul_one]
  | succ n hn ih =>
    have := h.comp ih
    rw [Nat.mul_succ, pow_add, pow_add, mul_comm (q ^ (m * n))]
    exact this
end Raises
end GlobalTheory.SS.FrobSub
