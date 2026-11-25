-- Prove2me | solution 1 for GlobalTheory.isIntegral_modularJ_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:32:53.126281+00:00
-- url     : https://prove2.me/submissions/784e9f5e-70e0-4cac-91fb-1ae51ddbb01c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Theorems.Thm_GlobalTheory_isIntegral_modularJ_of_mul_mem

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
theorem _root_.solution {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (ι : K →+* ℂ) {τ : ℍ}
    (h : ∀ α : 𝓞 K, ∀ x ∈ Submodule.span ℤ {(τ : ℂ), 1},
      ι α * x ∈ Submodule.span ℤ {(τ : ℂ), 1}) :
    IsIntegral ℤ (modularJ τ) := by
  obtain ⟨α, hα⟩ : ∃ α : 𝓞 K, ∀ m : ℤ, α ≠ m := by
    by_contra! hc
    have := finrank_le_one (R := ℤ) (1 : 𝓞 K) fun α ↦ by
      obtain ⟨m, hm⟩ := hc α
      exact ⟨m, by simp [hm]⟩
    rw [RingOfIntegers.rank, hK] at this
    omega
  refine isIntegral_modularJ_of_mul_mem (fun m hm ↦ hα m ?_) (h α)
  ext
  apply ι.injective
  simpa using hm
end GlobalTheory
