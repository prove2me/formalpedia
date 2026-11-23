-- Prove2me | solution 1 for GlobalTheory.ae_encard_smul_mem_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:03.444525+00:00
-- url     : https://prove2.me/submissions/88a18c54-dd51-4c16-a37d-982e4d7c52f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Theorems.Thm_GlobalTheory_encard_smul_mem_le_encard_smul_inter_nonempty
import Theorems.Thm_GlobalTheory_tsum_indicator_smul_eq_encard
import Theorems.Thm_GlobalTheory_sum_restrict_preimage_smul_le
import Theorems.Thm_GlobalTheory_setLIntegral_le_mul_of_ae_covers
import Theorems.Thm_GlobalTheory_setIntegral_le_mul_of_ae_covers
import Theorems.Thm_GlobalTheory_setLIntegral_le_mul_of_isFundamentalDomain
import Theorems.Thm_GlobalTheory_setLIntegral_le_encard_mul_of_ae_covers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
open GlobalTheory
variable {G X : Type*} [Group G] [MulAction G X]
variable [MeasurableSpace X] {μ : Measure X} [MeasurableConstSMul G X]
  [SMulInvariantMeasure G X μ] [Countable G] {B D : Set X}
omit [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ]
namespace GlobalTheory
theorem _root_.solution (hD : IsFundamentalDomain G D μ) :
    ∀ᵐ x ∂μ, {g : G | g • x ∈ D}.encard ≤ 1 := by
  have h : ∀ᵐ x ∂μ, ∀ g₁ g₂ : G, g₁ ≠ g₂ → x ∉ g₁ • D ∩ g₂ • D := by
    refine ae_all_iff.2 fun g₁ => ae_all_iff.2 fun g₂ => ?_
    by_cases h : g₁ = g₂
    · simp [h]
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hD.aedisjoint h)] with x hx _ using hx
  filter_upwards [h] with x hx
  rw [encard_le_one_iff]
  intro a b ha hb
  by_contra hab
  refine hx a⁻¹ b⁻¹ (by simpa using hab) ⟨?_, ?_⟩
  · rw [mem_smul_set_iff_inv_smul_mem, inv_inv]; exact ha
  · rw [mem_smul_set_iff_inv_smul_mem, inv_inv]; exact hb
end GlobalTheory
