-- Prove2me | solution 1 for GlobalTheory.SS.LinCore.finrank_le_of_weights
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:19:35.958637+00:00
-- url     : https://prove2.me/submissions/17492802-229e-4cee-b635-849a00d8c415

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankLeOfWeightsUnipotentSymplectic
import Theorems.Thm_GlobalTheory_SS_LinCore_core

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LinCore
open Polynomial
namespace GlobalTheory.SS.LinCore
theorem _root_.solution : ∀ (𝕜 V : Type) [Field 𝕜] [CharZero 𝕜] [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V] (B : LinearMap.BilinForm 𝕜 V), B.Nondegenerate → (∀ x y, B y x = - B x y) → ∀ (S Φ : V ≃ₗ[𝕜] V) (q : ℕ), 2 ≤ q → IsNilpotent ((S : V →ₗ[𝕜] V) - 1) → (∀ x y, B (S x) (S y) = B x y) → (∀ x y, B (Φ x) (Φ y) = q * B x y) → Φ * S = S ^ q * Φ → ∀ (W : Submodule 𝕜 V) (P : Polynomial ℤ), (∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < q) → (∀ x ∈ W, Φ x = (q : 𝕜) • x) → (∀ x, S x = x → Polynomial.aeval (Φ : V →ₗ[𝕜] V) P x ∈ W) → Module.finrank 𝕜 V ≤ Module.finrank 𝕜 (LinearMap.ker ((S : V →ₗ[𝕜] V) - 1)) + Module.finrank 𝕜 W := by
  intro 𝕜 V _ _ _ _ _ B hB _ S Φ q hq hS _ hΦ h W P hP hW hPW
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ 𝕜)
  haveI : IsScalarTower ℚ 𝕜 V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  refine core B hB _ (Φ : V →ₗ[𝕜] V) (Φ.symm : V →ₗ[𝕜] V) q hq hS ?_ hΦ ?_ W
    (P.map (algebraMap ℤ ℚ)) ?_ hW ?_
  · ext x
    simp
  · rw [sub_add_cancel]
    have := congrArg (fun e : V ≃ₗ[𝕜] V => (e : V →ₗ[𝕜] V)) h
    have h2 : ∀ k : ℕ, ((S ^ k : V ≃ₗ[𝕜] V) : V →ₗ[𝕜] V) = (S : V →ₗ[𝕜] V) ^ k := by
      intro k
      induction k with
      | zero => rw [pow_zero, pow_zero]; rfl
      | succ k ih => rw [pow_succ, pow_succ, ← ih]; simp
    simpa [h2] using this
  · intro β hβ
    rw [aeval_map_algebraMap] at hβ
    exact hP β hβ
  · intro x hx
    rw [aeval_map_algebraMap]
    exact hPW x (by simpa [sub_eq_zero] using hx)
end GlobalTheory.SS.LinCore
