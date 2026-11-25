-- Prove2me | solution 1 for GlobalTheory.exists_polynomial_modularJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:54:54.841879+00:00
-- url     : https://prove2.me/submissions/8dc5a25a-3311-4f9c-bf4d-3eba9e45051a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Theorems.Thm_GlobalTheory_hasQExpansion_qParam_pow_mul
import Theorems.Thm_GlobalTheory_exists_polynomial_modularJ_of_hasQExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real ArithmeticFunction.sigma
noncomputable section
open GlobalTheory
local notation "𝕢" => Function.Periodic.qParam
namespace GlobalTheory
theorem _root_.solution {m : ℕ} {f : ℍ → ℂ}
    (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty fun τ : ℍ ↦ 𝕢 1 τ ^ m * f τ) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧
      P.coeff m = coeff 0 (qExpansion 1 fun τ ↦ 𝕢 1 τ ^ m * f τ) ∧
      (∀ i, P.coeff i ∈ AddSubgroup.closure
        (Set.range fun k ↦ coeff k (qExpansion 1 fun τ ↦ 𝕢 1 τ ^ m * f τ))) ∧
      ∀ τ, f τ = P.eval (modularJ τ) :=
  exists_polynomial_modularJ_of_hasQExpansion _ hinv (hasQExpansion_qParam_pow_mul hinv hhol hbdd)
    fun k ↦ AddSubgroup.subset_closure ⟨k, rfl⟩
end GlobalTheory
