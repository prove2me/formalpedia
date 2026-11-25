-- Prove2me | solution 1 for GlobalTheory.exists_mul_pow_mem_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:14.306852+00:00
-- url     : https://prove2.me/submissions/24782e9a-59a1-47de-b5a2-e4877518aa1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsIntegralMulPowOfSubalgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {J : Type*}
namespace GlobalTheory
theorem _root_.solution (t : J → Ω) {i : J} (j : J) (hi : t i ≠ 0) {r : Ω}
    (hr : r ∈ Algebra.adjoin o (Set.range fun k => t k / t i)) :
    ∃ n : ℕ, r * (t i / t j) ^ n ∈ Algebra.adjoin o (Set.range fun k => t k / t j) := by
  have hu : t i / t j ∈ Algebra.adjoin o (Set.range fun k => t k / t j) :=
    Algebra.subset_adjoin ⟨i, rfl⟩
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    refine ⟨1, ?_⟩
    have : t k / t i * (t i / t j) ^ 1 = t k / t j := by
      rw [pow_one, div_mul_div_cancel₀ hi]
    rw [this]
    exact Algebra.subset_adjoin ⟨k, rfl⟩
  | algebraMap a => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hx⟩ := hx
    obtain ⟨m, hy⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x + y) * (t i / t j) ^ (n + m) = x * (t i / t j) ^ n * (t i / t j) ^ m +
      y * (t i / t j) ^ m * (t i / t j) ^ n := by ring
    rw [this]
    exact add_mem (mul_mem hx (pow_mem hu _)) (mul_mem hy (pow_mem hu _))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hx⟩ := hx
    obtain ⟨m, hy⟩ := hy
    refine ⟨n + m, ?_⟩
    have : x * y * (t i / t j) ^ (n + m) = x * (t i / t j) ^ n * (y * (t i / t j) ^ m) := by ring
    rw [this]
    exact mul_mem hx hy
end GlobalTheory
