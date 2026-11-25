-- Prove2me | solution 1 for GlobalTheory.T.abelianVariety_torsion_finite_endomorphism_divisible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:20:10.238407+00:00
-- url     : https://prove2.me/submissions/95b22e03-7e7d-4499-ad15-d76dee0524da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyTorsionFiniteEndomorphismDivisible
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyTorsionFiniteEndomorphismDivisibleStatement
import Theorems.Thm_GlobalTheory_TorsionDivisible_finite_torsion_and_divisible


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
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : k) ≠ 0 → Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ∧ ∀ f : B ⟶ B, IsMonHom f → (∀ x : (𝟙_ (Over (Sp k)) ⟶ B), x ^ n = 1 → x ≫ f = 1) → ∃ g : B ⟶ B, IsMonHom g ∧ f = g ^ n := by
  first | exact @GlobalTheory.TorsionDivisible.finite_torsion_and_divisible | exact GlobalTheory.TorsionDivisible.finite_torsion_and_divisible | (intros; apply GlobalTheory.TorsionDivisible.finite_torsion_and_divisible <;> assumption)
end _root_.GlobalTheory.T
