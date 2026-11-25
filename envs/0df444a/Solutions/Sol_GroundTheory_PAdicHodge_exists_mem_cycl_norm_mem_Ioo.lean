-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_mem_cycl_norm_mem_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:50:07.146648+00:00
-- url     : https://prove2.me/submissions/7b572998-6902-4e36-afe4-c21f486ad9aa

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_FWCyclotomicNorm
import Theorems.Thm_GroundTheory_PAdicHodge_exists_isPrimitiveRoot
import Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_pow_totient
import Theorems.Thm_GroundTheory_PAdicHodge_one_lt_p_real
import Theorems.Thm_GroundTheory_PAdicHodge_pow_eq_one_mem_cycl
import Theorems.Thm_GroundTheory_PAdicHodge_totient_prime_pow_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {r : ℝ} (hr : r < 1) :
    ∃ n, ∃ x ∈ cycl p n, r < ‖x‖ ∧ ‖x‖ < 1 := by
  have hp1 : (1 : ℝ) < p := one_lt_p_real
  have hpinv : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (by linarith)
  have hpinv1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1

  obtain ⟨N, hN⟩ : ∃ N : ℕ, max r 0 ^ N < (p : ℝ)⁻¹ := by
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (le_max_right r 0) (max_lt hr one_pos)
    obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hpinv)).exists_forall_of_atTop
    exact ⟨N, hN N le_rfl⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) (N + 1)
  set d := Nat.totient (p ^ (N + 1))
  have hrd := norm_sub_one_pow_totient hζ
  have hd : N ≤ d := by
    have h1 : d = p ^ N * (p - 1) := Nat.totient_prime_pow_succ (Fact.out : p.Prime) N
    have h2 : N < p ^ N := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
    have h3 : 1 ≤ p - 1 := by have := (Fact.out : p.Prime).two_le; omega
    rw [h1]; nlinarith
  refine ⟨N + 1, ζ - 1, sub_mem (pow_eq_one_mem_cycl hζ.pow_eq_one) (one_mem _), ?_, ?_⟩
  · have h1 : max r 0 ^ d < ‖ζ - 1‖ ^ d := by
      rw [hrd]
      exact lt_of_le_of_lt (pow_le_pow_of_le_one (le_max_right _ _) (max_lt hr one_pos).le hd) hN
    have hd0 : d ≠ 0 := (Nat.totient_pos.2 (pow_pos (Fact.out : p.Prime).pos _)).ne'
    exact lt_of_le_of_lt (le_max_left r 0)
      ((pow_lt_pow_iff_left₀ (le_max_right _ _) (norm_nonneg _) hd0).1 h1)
  · by_contra h
    have h1 : 1 ≤ ‖ζ - 1‖ ^ d := one_le_pow₀ (not_lt.1 h)
    rw [hrd] at h1
    linarith
end GroundTheory.PAdicHodge
