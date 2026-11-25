-- Prove2me | solution 1 for GlobalTheory.exists_hasQExpansion_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:46:14.11419+00:00
-- url     : https://prove2.me/submissions/1e65cb0f-14f2-44aa-b51d-52565087c34d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Theorems.Thm_GlobalTheory_twelve_dvd_sigma
import Theorems.Thm_P2M_GlobalTheory_qExpansion_E__026e1fb3b144
import Theorems.Thm_P2M_GlobalTheory_qExpansion_E__5e6e9facd55b
import Theorems.Thm_GlobalTheory_HasQExpansion_congr
import Theorems.Thm_GlobalTheory_HasQExpansion_const
import Theorems.Thm_GlobalTheory_HasQExpansion_mul
import Theorems.Thm_GlobalTheory_HasQExpansion_pow
import Theorems.Thm_GlobalTheory_HasQExpansion_sub
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
theorem _root_.solution : ∃ U : ℤ⟦X⟧, coeff 0 U = 1 ∧
    HasQExpansion 1 discriminant (X * PowerSeries.map (Int.castRingHom ℂ) U) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk fun n ↦ (σ 3 n : ℤ) with hA
  set B : ℤ⟦X⟧ := PowerSeries.mk fun n ↦ (σ 5 n : ℤ) with hB
  obtain ⟨S, hS⟩ : ∃ S : ℤ⟦X⟧, 5 * A + 7 * B = 12 * S := by
    choose c hc using twelve_dvd_sigma
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    rw [show (5 : ℤ⟦X⟧) = C 5 from rfl, show (7 : ℤ⟦X⟧) = C 7 from rfl,
      show (12 : ℤ⟦X⟧) = C 12 from rfl, map_add, coeff_C_mul, coeff_C_mul, coeff_C_mul]
    simpa [hA, hB] using hc n
  set D : ℤ⟦X⟧ := S + 100 * A ^ 2 + 8000 * A ^ 3 - 147 * B ^ 2 with hD
  have hD' : (1 + 240 * A) ^ 3 - (1 - 504 * B) ^ 2 = 1728 * D := by
    rw [hD]; linear_combination 144 * hS
  have h1 := (HasQExpansion.const 1 (1728⁻¹ : ℂ)).mul
    (((hasQExpansion_modularForm E₄).pow 3).sub ((hasQExpansion_modularForm E₆).pow 2))
  rw [qExpansion_E₄, qExpansion_E₆, ← map_pow, ← map_pow, ← map_sub, hD', map_mul, ← mul_assoc,
    show (C (1728⁻¹ : ℂ) * PowerSeries.map (Int.castRingHom ℂ) 1728 : ℂ⟦X⟧) = 1 by
      rw [show (1728 : ℤ⟦X⟧) = C 1728 from rfl, map_C, ← map_mul]; simp, one_mul] at h1
  have h2 : HasQExpansion 1 discriminant (PowerSeries.map (Int.castRingHom ℂ) D) :=
    h1.congr fun τ ↦ by rw [discriminant_eq_E₄_cube_sub_E₆_sq]; ring
  have h3 : HasQExpansion 1 discriminant (qExpansion 1 discriminant) := fun τ ↦
    ModularForm.hasSum_qExpansion CuspForm.discriminant one_pos one_mem_strictPeriods_SL τ
  have h4 := h2.unique one_pos h3
  have h5 : coeff 0 D = 0 := by
    have := CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos
      one_mem_strictPeriods_SL
    rw [CuspForm.coe_discriminant, ← h4, coeff_map] at this
    simpa using this
  have h6 : coeff 1 D = 1 := by
    have := discriminant_qExpansion_coeff_one
    rw [← h4, coeff_map] at this
    simpa using this
  obtain ⟨U, hU⟩ : X ∣ D := X_dvd_iff.mpr (by simpa using h5)
  refine ⟨U, by rw [← h6, hU, coeff_succ_X_mul], ?_⟩
  rwa [hU, map_mul, map_X] at h2
end GlobalTheory
