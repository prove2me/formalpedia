-- Prove2me | solution 1 for GroundTheory.LocalField.ringHom_ext_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:38.632991+00:00
-- url     : https://prove2.me/submissions/796414cf-e95a-4b08-837a-24285b128c7a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramifiedIntegers
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnitMulPowAdic
import Definitions.Def_GroundTheory_LocalFields_CompletedUnramified
import Theorems.Thm_GroundTheory_LocalField_eq_zero_of_forall_mem_maximalIdeal_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open IsLocalRing ValuativeRel
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
local notation "𝔅" => AdicCompletion (maximalIdeal R) R
namespace GroundTheory.LocalField
theorem _root_.solution {ϖ : R} (hϖ : Irreducible ϖ) {τ₁ τ₂ : 𝔅 →+* 𝔅}
    (h : ∀ r, τ₁ (algebraMap R 𝔅 r) = τ₂ (algebraMap R 𝔅 r))
    (hmem : τ₁ (algebraMap R 𝔅 ϖ) ∈ maximalIdeal 𝔅) : τ₁ = τ₂ := by
  have hm := maximalIdeal_adicCompletion_eq_span hϖ
  refine RingHom.ext fun x ↦ ?_
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_mem_maximalIdeal_pow fun n ↦ ?_
  obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_pow x n
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hr
  obtain ⟨c, hc⟩ := hr
  have hx : x = algebraMap R 𝔅 r + c * algebraMap R 𝔅 ϖ ^ n := by rw [hc]; ring
  rw [hx, map_add, map_add, map_mul, map_mul, map_pow, map_pow, h r, ← h ϖ]
  have : τ₁ (algebraMap R 𝔅 ϖ) ^ n ∈ maximalIdeal 𝔅 ^ n := Ideal.pow_mem_pow hmem n
  convert Ideal.mul_mem_left _ (τ₁ c - τ₂ c) this using 1
  ring
end GroundTheory.LocalField
