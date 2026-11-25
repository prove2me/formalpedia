-- Prove2me | solution 1 for GlobalTheory.exists_hasSum_modularJ_sub_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:21.828501+00:00
-- url     : https://prove2.me/submissions/b92352b4-c0ca-4950-8715-5e2b082110d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Theorems.Thm_GlobalTheory_HasQExpansion_congr
import Theorems.Thm_GlobalTheory_HasQExpansion_const
import Theorems.Thm_GlobalTheory_HasQExpansion_of_qParam_mul
import Theorems.Thm_GlobalTheory_HasQExpansion_sub
import Theorems.Thm_GlobalTheory_exists_hasQExpansion_modularJ


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
namespace GlobalTheory
theorem _root_.solution : ∃ c : ℕ → ℤ, ∀ τ : ℍ,
    HasSum (fun n ↦ (c n : ℂ) * 𝕢 1 τ ^ n) (modularJ τ - (𝕢 1 τ)⁻¹) := by
  obtain ⟨J, hJ0, hJ⟩ := exists_hasQExpansion_modularJ
  obtain ⟨K, hK⟩ : X ∣ J - 1 := X_dvd_iff.mpr (by
    rw [map_sub, map_one, ← coeff_zero_eq_constantCoeff_apply, hJ0, sub_self])
  have h1 := hJ.sub (HasQExpansion.const 1 1)
  rw [map_one, ← map_one (PowerSeries.map (Int.castRingHom ℂ)), ← map_sub, hK, map_mul,
    map_X] at h1
  have h2 : HasQExpansion 1 (fun τ ↦ modularJ τ - (𝕢 1 τ)⁻¹) _ :=
    .of_qParam_mul (h1.congr fun τ ↦ by
      rw [mul_sub, mul_inv_cancel₀ (Periodic.qParam_ne_zero _)])
  exact ⟨fun n ↦ coeff n K, fun τ ↦ by simpa using h2 τ⟩
end GlobalTheory
