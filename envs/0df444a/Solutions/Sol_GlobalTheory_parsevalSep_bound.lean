-- Prove2me | solution 1 for GlobalTheory.parsevalSep_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:43:14.930092+00:00
-- url     : https://prove2.me/submissions/fab49e52-301c-46e1-9c75-ac5d4cf5dea6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ParsevalBoundIntegerVectorSmallFourierSupport
import Theorems.Thm_GlobalTheory_parsevalSep_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (n N : ℕ) (ω : ℂ) (c : ℕ → ℤ) (S : Finset ℕ), 0 < n → 0 < N → IsPrimitiveRoot ω N → ∑ k ∈ Finset.range N, c k ^ 2 = 2 * n → |∑ k ∈ Finset.range N, c k| ≤ (n : ℤ) - 1 → (∀ j : ℕ, 0 < j → j < N → j ∉ S → ∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k) = 0) → 2 * n * N ≤ (n - 1) ^ 2 + 4 * n ^ 2 * S.card := by
  intro n N ω c S hn hN hω h2 h0 hS
  have h1 : ‖ω‖ = 1 := hω.norm'_eq_one hN.ne'
  have hP := parsevalSep_identity N ω hN hω c
  rw [h2] at hP
  set F : ℕ → ℂ := fun j => ∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k) with hF
  have hb : ∀ j, ‖F j‖ ≤ 2 * n := by
    intro j
    have h2' : ∑ k ∈ Finset.range N, (c k : ℝ) ^ 2 = 2 * n := by exact_mod_cast h2
    rw [← h2']
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_pow, h1, one_pow, mul_one, Complex.norm_intCast]
    have : |c k| ≤ c k ^ 2 := by
      rw [← sq_abs]
      have := abs_nonneg (c k)
      nlinarith [Int.le_self_sq |c k|]
    exact_mod_cast this
  have hz : ‖F 0‖ ≤ (n : ℝ) - 1 := by
    have : F 0 = ((∑ k ∈ Finset.range N, c k : ℤ) : ℂ) := by simp [hF]
    rw [this, Complex.norm_intCast]
    exact_mod_cast h0
  have hle : ∀ j ∈ Finset.range N, ‖F j‖ ^ 2 ≤
      (if j = 0 then ((n : ℝ) - 1) ^ 2 else 0) + (if j ∈ S then 4 * (n : ℝ) ^ 2 else 0) := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      have : ‖F 0‖ ^ 2 ≤ ((n : ℝ) - 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      rw [if_pos rfl]
      split_ifs
      · have : (0 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by positivity
        linarith
      · linarith
    · rw [if_neg hj0, zero_add]
      split_ifs with hjS
      · have := pow_le_pow_left₀ (norm_nonneg _) (hb j) 2
        linarith [show (2 * (n : ℝ)) ^ 2 = 4 * (n : ℝ) ^ 2 by ring]
      · have : F j = 0 := hS j (Nat.pos_of_ne_zero hj0) (Finset.mem_range.1 hj) hjS
        simp [this]
  have hsum := Finset.sum_le_sum hle
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_range.2 hN),
    Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul] at hsum
  have hc : ((Finset.range N ∩ S).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hP' : ∑ j ∈ Finset.range N, ‖F j‖ ^ 2 = (N : ℝ) * (2 * n) := by
    rw [hP]; push_cast; ring
  have key : (2 * n * N : ℝ) ≤ ((n : ℝ) - 1) ^ 2 + 4 * (n : ℝ) ^ 2 * S.card := by
    have : ((Finset.range N ∩ S).card : ℝ) * (4 * (n : ℝ) ^ 2) ≤ S.card * (4 * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    linarith
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; simp
  rw [← hn1] at key
  exact_mod_cast key
end GlobalTheory
