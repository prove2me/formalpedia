-- Prove2me | solution 1 for GlobalTheory.hasQExpansion_qParam_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:36:16.981653+00:00
-- url     : https://prove2.me/submissions/0f1a5ece-52ff-4564-88f5-7235d6e0ab58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Theorems.Thm_GlobalTheory_periodic_comp_ofComplex_of_vadd
import Theorems.Thm_GlobalTheory_qParam_one_vadd
import Theorems.Thm_GlobalTheory_HasQExpansion_mdifferentiable
import Theorems.Thm_GlobalTheory_HasQExpansion_mul
import Theorems.Thm_GlobalTheory_HasQExpansion_of_periodic
import Theorems.Thm_GlobalTheory_HasQExpansion_pow


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
theorem _root_.solution {f : ℍ → ℂ} (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ)
    (hhol : MDiff f) {m : ℕ} (hbdd : IsBoundedAtImInfty fun τ : ℍ ↦ 𝕢 1 τ ^ m * f τ) :
    HasQExpansion 1 (fun τ ↦ 𝕢 1 τ ^ m * f τ) (qExpansion 1 fun τ ↦ 𝕢 1 τ ^ m * f τ) := by
  refine .of_periodic one_pos (periodic_comp_ofComplex_of_vadd fun τ ↦ ?_) ?_ hbdd
  · rw [qParam_one_vadd, ← modular_T_smul, hinv]
  · exact (((HasQExpansion.qParam 1).mdifferentiable one_pos).pow m).mul hhol
end GlobalTheory
