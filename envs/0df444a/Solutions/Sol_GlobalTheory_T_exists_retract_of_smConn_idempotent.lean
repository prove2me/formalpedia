-- Prove2me | solution 1 for GlobalTheory.T.exists_retract_of_smConn_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:33:43.598803+00:00
-- url     : https://prove2.me/submissions/6532ea1e-871b-437b-8b55-3e46ebb02096

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmConnIdempotentSplits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmConnIdempotentSplitsStatement
import Theorems.Thm_GlobalTheory_SS_smConn_idempotent_splits


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], SmConn G → ∀ e : G ⟶ G, IsMonHom e → e ≫ e = e → ∃ (G₁ : Over S) (_ : GrpObj G₁) (i : G₁ ⟶ G) (r : G ⟶ G₁), SmConn G₁ ∧ IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 G₁ ∧ r ≫ i = e := by
  first | exact @GlobalTheory.SS.smConn_idempotent_splits | exact GlobalTheory.SS.smConn_idempotent_splits | (intros; apply GlobalTheory.SS.smConn_idempotent_splits <;> assumption)
end _root_.GlobalTheory.T
