-- Prove2me | solution 1 for GlobalTheory.T.quasiAffine_subgroup_containing_torus_eq_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:13:09.008417+00:00
-- url     : https://prove2.me/submissions/8cd8967d-4553-4959-bd47-e71c57f6bbe0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiAffineSubgroupContainingTorusEqTorus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiAffineSubgroupContainingTorusEqTorusStatement
import Theorems.Thm_GlobalTheory_IrreducibleGeneralizations_main
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_main


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
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G →  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q → IsAbelianScheme B → ∀ (N : Over (Sp k)) [GrpObj N] (ν : N ⟶ G) (i' : splitTorus (Sp k) X ⟶ N), SmConn N → IsMonHom ν → IsClosedImmersion ν.left → i' ≫ ν = i → (∀ x : N.left, ∃ f : Γ(N.left, ⊤), x ∈ N.left.basicOpen f ∧ IsAffineOpen (N.left.basicOpen f)) → ∀ x : (𝟙_ (Over (Sp k)) ⟶ N), ∃ t : (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X), t ≫ i = x ≫ ν := by
  first | exact @GlobalTheory.QuasiAffineTorus.main | exact GlobalTheory.QuasiAffineTorus.main | (intros; apply GlobalTheory.QuasiAffineTorus.main <;> assumption)
end _root_.GlobalTheory.T
