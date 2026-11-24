-- Prove2me | solution 1 for GlobalTheory.T.finrank_le_of_weights_unipotent_symplectic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:31:09.829477+00:00
-- url     : https://prove2.me/submissions/34c9d2b1-c329-4a9b-87a5-a581dd97a635

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankLeOfWeightsUnipotentSymplectic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankLeOfWeightsUnipotentSymplecticStatement
import Theorems.Thm_GlobalTheory_SS_LinCore_finrank_le_of_weights


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
theorem _root_.solution : ∀ (𝕜 V : Type) [Field 𝕜] [CharZero 𝕜] [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V] (B : LinearMap.BilinForm 𝕜 V), B.Nondegenerate → (∀ x y, B y x = - B x y) → ∀ (S Φ : V ≃ₗ[𝕜] V) (q : ℕ), 2 ≤ q → IsNilpotent ((S : V →ₗ[𝕜] V) - 1) → (∀ x y, B (S x) (S y) = B x y) → (∀ x y, B (Φ x) (Φ y) = q * B x y) → Φ * S = S ^ q * Φ → ∀ (W : Submodule 𝕜 V) (P : Polynomial ℤ), (∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < q) → (∀ x ∈ W, Φ x = (q : 𝕜) • x) → (∀ x, S x = x → Polynomial.aeval (Φ : V →ₗ[𝕜] V) P x ∈ W) → Module.finrank 𝕜 V ≤ Module.finrank 𝕜 (LinearMap.ker ((S : V →ₗ[𝕜] V) - 1)) + Module.finrank 𝕜 W := by
  first | exact @GlobalTheory.SS.LinCore.finrank_le_of_weights | exact GlobalTheory.SS.LinCore.finrank_le_of_weights | (intros; apply GlobalTheory.SS.LinCore.finrank_le_of_weights <;> assumption)
end _root_.GlobalTheory.T
