-- Prove2me | solution 1 for GlobalTheory.CMVal.exists_idele_section_of_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:37:06.882302+00:00
-- url     : https://prove2.me/submissions/63c99e4f-f26c-46c5-bbbf-6f9d4f3cb718

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSectionIntegralFiniteIdeleUpToUnits
import Theorems.Thm_GlobalTheory_CMVal_IdeleIdeal_modF_eq
import Theorems.Thm_GlobalTheory_CMVal_IdeleIdeal_val_eq_of_idealOf_eq
import Theorems.Thm_GlobalTheory_CMVal_Euler_inv_coord
import Theorems.Thm_GlobalTheory_CMVal_Euler_mul_coord
import Theorems.Thm_GlobalTheory_CMVal_IdeleModule_coord_ne
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open scoped nonZeroDivisors
open GlobalTheory.CMVal.IdeleIdeal
namespace GlobalTheory.CMVal
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] , ∃ g : Ideal (𝓞 E) → (Af E)ˣ, ∀ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) ≤ 1) → ∃ J : Ideal (𝓞 E), modF y = ((Ideal.absNorm J : ℕ) : ℝ)⁻¹ ∧ ∀ w, Valued.v ((((g J)⁻¹ * y : (Af E)ˣ) : Af E) w) = 1 := by
  intro E _ _
  classical
  refine ⟨fun J => if h : ∃ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) ≤ 1) ∧ idealOf y = J then h.choose else 1,
    fun y hy => ⟨idealOf y, modF_eq hy, fun w => ?_⟩⟩
  have h : ∃ y' : (Af E)ˣ, (∀ w, Valued.v ((y' : Af E) w) ≤ 1) ∧ idealOf y' = idealOf y := ⟨y, hy, rfl⟩
  simp only [dif_pos h]
  rw [Units.val_mul, mul_coord, inv_coord, map_mul, map_inv₀,
    val_eq_of_idealOf_eq h.choose_spec.1 hy h.choose_spec.2 w, inv_mul_cancel₀ (IdeleModule.coord_ne y w)]
end GlobalTheory.CMVal
