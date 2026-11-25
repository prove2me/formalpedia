-- Prove2me | solution 1 for GlobalTheory.T.existsUnique_linearLift_of_holomorphic_abelianVariety
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:00:21.338333+00:00
-- url     : https://prove2.me/submissions/00b33c46-3436-489c-b315-767db5f33249

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVarietStatement
import Theorems.Thm_GlobalTheory_existsUnique_linear_lift_of_isHolTo


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g m : ℕ) (u : HolUnif A L g),
  (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) →
  ∀ G : (Fin m → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A), (∀ z w, G (z + w) = G z * G w) →
  IsHolTo (Set.univ : Set (Fin m → ℂ)) (fun z => (G z).left) →
  ∃! F : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = G z := by
  first | exact @GlobalTheory.existsUnique_linear_lift_of_isHolTo | exact GlobalTheory.existsUnique_linear_lift_of_isHolTo | (intros; apply GlobalTheory.existsUnique_linear_lift_of_isHolTo <;> assumption)
end _root_.GlobalTheory.T
