-- Prove2me | solution 1 for GlobalTheory.modularJ_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:54.782829+00:00
-- url     : https://prove2.me/submissions/34c59bd7-0d33-464d-8907-080c142fe8f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion

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
theorem _root_.solution (γ : SL(2, ℤ)) (τ : ℍ) : modularJ (γ • τ) = modularJ τ := by
  have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have h1 := SlashInvariantForm.slash_action_eqn'' E₄ hγ τ
  have h2 := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
  have h3 := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
  have h4 := discriminant_ne_zero τ
  change E₄ ((γ : GL (Fin 2) ℝ) • τ) ^ 3 / CuspForm.discriminant ((γ : GL (Fin 2) ℝ) • τ) =
    E₄ τ ^ 3 / CuspForm.discriminant τ
  rw [h1, h2]
  change _ / (_ * discriminant τ) = _ / discriminant τ
  field_simp
end GlobalTheory
