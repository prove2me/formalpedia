-- Prove2me | solution 1 for GlobalTheory.residueClass_relativelyDense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:31:25.529853+00:00
-- url     : https://prove2.me/submissions/455878bf-33b2-4d5f-bd92-a3527b9c15ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsResidueClassNearRealEmbeddings
import Theorems.Thm_GlobalTheory_exists_integer_near

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (m : Ideal (𝓞 F)) (a₀ : 𝓞 F), m ≠ ⊥ →
    ∃ C : ℝ, ∀ y : (F →+* ℝ) → ℝ, ∃ a : 𝓞 F, a - a₀ ∈ m ∧
      ∀ τ : F →+* ℝ, |τ (a : F) - y τ| ≤ C := by
  intro F _ _ _ m a₀ hm
  obtain ⟨C, hC⟩ := exists_integer_near F
  have hMpos : 0 < Ideal.absNorm m := Nat.pos_of_ne_zero (fun h => hm (Ideal.absNorm_eq_zero_iff.1 h))
  set M : ℕ := Ideal.absNorm m with hMdef
  have hMmem : ((M : ℕ) : 𝓞 F) ∈ m := Ideal.absNorm_mem m
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hMpos
  refine ⟨M * C, fun y => ?_⟩
  obtain ⟨z, hz⟩ := hC (fun τ => (y τ - τ (a₀ : F)) / M)
  refine ⟨a₀ + (M : 𝓞 F) * z, ?_, fun τ => ?_⟩
  · simpa using m.mul_mem_right z hMmem
  · have h := hz τ
    have h3 : τ (((a₀ + (M : 𝓞 F) * z : 𝓞 F)) : F) - y τ
        = M * (τ (z : F) - (y τ - τ (a₀ : F)) / M) := by
      have : τ (((a₀ + (M : 𝓞 F) * z : 𝓞 F)) : F) = τ (a₀ : F) + M * τ (z : F) := by
        simp
      rw [this]
      field_simp
      ring
    rw [h3, abs_mul, abs_of_pos hM0]
    exact mul_le_mul_of_nonneg_left h hM0.le
end GlobalTheory
