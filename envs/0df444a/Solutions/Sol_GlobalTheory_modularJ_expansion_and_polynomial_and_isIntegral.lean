-- Prove2me | solution 1 for GlobalTheory.modularJ_expansion_and_polynomial_and_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:31.772741+00:00
-- url     : https://prove2.me/submissions/ff9dc8c7-9951-41bf-848f-210500bb253d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Theorems.Thm_GlobalTheory_isIntegral_modularJ_of_ringOfIntegers
import Theorems.Thm_GlobalTheory_isIntegral_modularJ_of_sq_eq_neg
import Theorems.Thm_GlobalTheory_exists_hasSum_modularJ_sub_inv
import Theorems.Thm_GlobalTheory_exists_polynomial_modularJ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real
noncomputable section
open GlobalTheory
local notation "𝕢" => Function.Periodic.qParam
open NumberField
namespace GlobalTheory
theorem _root_.solution :
    (∃ c : ℕ → ℤ, ∀ τ : ℍ,
      HasSum (fun n ↦ (c n : ℂ) * 𝕢 1 τ ^ n) (modularJ τ - (𝕢 1 τ)⁻¹)) ∧
    (∀ (m : ℕ) (f : ℍ → ℂ), (∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ) → MDiff f →
      (IsBoundedAtImInfty fun τ : ℍ ↦ 𝕢 1 τ ^ m * f τ) →
      ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧
        (∀ i, P.coeff i ∈ AddSubgroup.closure
          (Set.range fun k ↦ coeff k (qExpansion 1 fun τ ↦ 𝕢 1 τ ^ m * f τ))) ∧
        ∀ τ, f τ = P.eval (modularJ τ)) ∧
    (∀ (w : ℍ) (d : ℤ), (2 * (w : ℂ) - 1) ^ 2 = -d → IsIntegral ℤ (modularJ w)) ∧
    (∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (ι : K →+* ℂ) (τ : ℍ),
      (∀ α : 𝓞 K, ∀ x ∈ Submodule.span ℤ {(τ : ℂ), 1},
        ι α * x ∈ Submodule.span ℤ {(τ : ℂ), 1}) → IsIntegral ℤ (modularJ τ)) :=
  ⟨exists_hasSum_modularJ_sub_inv,
    fun _ _ h1 h2 h3 ↦ let ⟨P, a, _, b⟩ := exists_polynomial_modularJ h1 h2 h3; ⟨P, a, b⟩,
    fun _ _ ↦ isIntegral_modularJ_of_sq_eq_neg,
    fun _ _ _ hK ι _ ↦ isIntegral_modularJ_of_ringOfIntegers hK ι⟩
end GlobalTheory
