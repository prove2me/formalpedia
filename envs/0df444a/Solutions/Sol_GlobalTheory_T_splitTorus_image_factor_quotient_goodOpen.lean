-- Prove2me | solution 1 for GlobalTheory.T.splitTorus_image_factor_quotient_goodOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:52:46.759396+00:00
-- url     : https://prove2.me/submissions/9ecc1f16-f055-4437-b879-d5ecb7c329e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusImageFactorQuotientGoodOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusImageFactorQuotientGoodOpenStatement
import Theorems.Thm_GlobalTheory_TorusImage_exists_factor_goodOpen


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
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → ∃ (X' : Type) (_ : AddCommGroup X') (_ : Module.Free ℤ X') (_ : Module.Finite ℤ X') (i' : splitTorus (Sp k) X' ⟶ G) (ρ : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X'), IsMonHom i' ∧ IsMonHom ρ ∧ Surjective ρ.left ∧ ρ ≫ i' = i ∧ (∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen i' V) := by
  first | exact @GlobalTheory.TorusImage.exists_factor_goodOpen | exact GlobalTheory.TorusImage.exists_factor_goodOpen | (intros; apply GlobalTheory.TorusImage.exists_factor_goodOpen <;> assumption)
end _root_.GlobalTheory.T
