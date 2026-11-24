-- Prove2me | solution 1 for GlobalTheory.SS.FrobSub.isMonHom_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:19:12.608709+00:00
-- url     : https://prove2.me/submissions/f67d5298-abc7-4427-bb11-892e28fc12ba

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
theorem _root_.solution {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (F : End G)
    (h : IsMonHom (show G ⟶ G from F)) (m : ℕ) : IsMonHom (show G ⟶ G from F ^ m) := by
  induction m with
  | zero => exact inferInstanceAs (IsMonHom (𝟙 G))
  | succ m ih =>
    rw [pow_succ]
    exact inferInstanceAs (IsMonHom ((show G ⟶ G from F) ≫ (show G ⟶ G from F ^ m)))
end GlobalTheory.SS.FrobSub
