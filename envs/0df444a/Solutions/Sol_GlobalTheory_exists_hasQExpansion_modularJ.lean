-- Prove2me | solution 1 for GlobalTheory.exists_hasQExpansion_modularJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:39:18.537428+00:00
-- url     : https://prove2.me/submissions/d1a1ca31-7b5a-4448-b8b8-e1535968bdbb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Theorems.Thm_GlobalTheory_modularJ_def
import Theorems.Thm_GlobalTheory_modularJ_smul
import Theorems.Thm_GlobalTheory_mdifferentiable_modularJ
import Theorems.Thm_GlobalTheory_hasQExpansion_qParam_pow_mul
import Theorems.Thm_P2M_GlobalTheory_qExpansion_E__026e1fb3b144
import Theorems.Thm_GlobalTheory_exists_hasQExpansion_discriminant
import Theorems.Thm_GlobalTheory_HasQExpansion_congr
import Theorems.Thm_GlobalTheory_HasQExpansion_mul
import Theorems.Thm_GlobalTheory_HasQExpansion_of_qParam_mul
import Theorems.Thm_GlobalTheory_HasQExpansion_pow
import Theorems.Thm_GlobalTheory_HasQExpansion_tendsto
import Theorems.Thm_GlobalTheory_HasQExpansion_unique
import Theorems.Thm_GlobalTheory_hasQExpansion_modularForm


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
theorem _root_.solution : ∃ J : ℤ⟦X⟧, coeff 0 J = 1 ∧
    HasQExpansion 1 (fun τ ↦ 𝕢 1 τ * modularJ τ) (PowerSeries.map (Int.castRingHom ℂ) J) := by
  obtain ⟨U, hU0, hU⟩ := exists_hasQExpansion_discriminant
  have hq (τ : ℍ) : 𝕢 1 τ ≠ 0 := Periodic.qParam_ne_zero _
  have hu : HasQExpansion 1 (fun τ ↦ discriminant τ / 𝕢 1 τ)
      (PowerSeries.map (Int.castRingHom ℂ) U) :=
    .of_qParam_mul (hU.congr fun τ ↦ by field_simp [hq τ])
  have hE := (hasQExpansion_modularForm E₄).pow 3
  have heq (τ : ℍ) : 𝕢 1 τ ^ 1 * modularJ τ = E₄ τ ^ 3 / (discriminant τ / 𝕢 1 τ) := by
    rw [modularJ_def]; field_simp
  have hbdd : IsBoundedAtImInfty fun τ : ℍ ↦ 𝕢 1 τ ^ 1 * modularJ τ := by
    simp_rw [heq]
    exact ((hE.tendsto one_pos).div (hu.tendsto one_pos) (by simp [hU0])).isBigO_one ℝ
  have h1 := hasQExpansion_qParam_pow_mul modularJ_smul mdifferentiable_modularJ hbdd
  set φ := qExpansion 1 fun τ : ℍ ↦ 𝕢 1 τ ^ 1 * modularJ τ
  have h2 := (h1.mul hu).unique one_pos (hE.congr fun τ ↦ by
    rw [modularJ_def]; field_simp [hq τ, discriminant_ne_zero τ])
  rw [qExpansion_E₄, ← map_pow] at h2
  set E : ℤ⟦X⟧ := (1 + 240 * PowerSeries.mk fun n ↦ (σ 3 n : ℤ)) ^ 3 with hE'
  have hUV : U * U.invOfUnit 1 = 1 := mul_invOfUnit U 1 (by simpa using hU0)
  refine ⟨E * U.invOfUnit 1, by simp [hE'], ?_⟩
  rw [map_mul, ← h2, mul_assoc, ← map_mul, hUV, map_one, mul_one]
  simpa using h1
end GlobalTheory
