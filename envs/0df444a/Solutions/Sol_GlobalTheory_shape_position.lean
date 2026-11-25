-- Prove2me | solution 1 for GlobalTheory.shape_position
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:55:04.289826+00:00
-- url     : https://prove2.me/submissions/eeecb165-2eff-4f44-b418-25d5eb7dd33f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CardFilterFinBounds
import Theorems.Thm_GlobalTheory_abs_lowK_sub_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
namespace GlobalTheory
private lemma four_sq_add_le_of_large_bv {n : ℕ} {bv : ℝ} (hn : 2 ≤ n) (hb : 10 ^ 6 * (n : ℝ) ^ 7 ≤ bv) :
    4 * (n : ℝ) ^ 2 + 2 + n ≤ bv / 32 - bv / 100 := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h7 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hsq : 4 * (n : ℝ) ^ 2 + 2 + n ≤ 6 * (n : ℝ) ^ 2 := by nlinarith
  linarith
end GlobalTheory
end

set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (n kk j : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (bv : ℝ), Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → 0 < bv ∧ (∀ ω : Fin n → ℝ, ∑ a, |ω a - lowK ε μ a| ≤ j → ∀ a : Fin n, (a.val + 1 < kk → -bv / 8 - bv / 32 ≤ -ω a ∧ -ω a ≤ bv / 32) ∧ (kk ≤ a.val + 1 → bv - bv / 32 ≤ -ω a ∧ -ω a ≤ 2 * bv + bv / 32)) ∧ ∀ a : Fin n, (a.val + 1 < kk → -bv / 8 - bv / 32 ≤ -μ a + (1 - (n : ℝ)) / 2 ∧ -μ a + (1 - (n : ℝ)) / 2 ≤ bv / 32) ∧ (kk ≤ a.val + 1 → bv - bv / 32 ≤ -μ a + (1 - (n : ℝ)) / 2 ∧ -μ a + (1 - (n : ℝ)) / 2 ≤ 2 * bv + bv / 32) := by
  intro n kk j ε μ bv hS hj
  obtain ⟨hk1, hkn, -, hcl, hnd, hb⟩ := hS
  have hn : 2 ≤ n := by omega
  have hm := four_sq_add_le_of_large_bv hn hb
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hbpos : 0 < bv := by
    have : (0 : ℝ) < (n : ℝ) ^ 7 := by positivity
    linarith
  have hjr : (j : ℝ) ≤ 4 * (n : ℝ) ^ 2 + 2 := by exact_mod_cast hj
  refine ⟨hbpos, ?_, ?_⟩
  · intro ω hω a
    have hle : |ω a - lowK ε μ a| ≤ j :=
      le_trans (Finset.single_le_sum (f := fun b => |ω b - lowK ε μ b|)
        (fun b _ => abs_nonneg _) (Finset.mem_univ a)) hω
    obtain ⟨hl1, hl2⟩ := abs_lowK_sub_le ε μ a
    obtain ⟨ha1, ha2⟩ := abs_le.mp hle
    constructor
    · intro ha
      obtain ⟨-, h1, h2⟩ := hcl a ha
      constructor <;> linarith
    · intro ha
      obtain ⟨h1, h2⟩ := hnd a ha
      constructor <;> linarith
  · intro a
    constructor
    · intro ha
      obtain ⟨-, h1, h2⟩ := hcl a ha
      constructor <;> linarith
    · intro ha
      obtain ⟨h1, h2⟩ := hnd a ha
      constructor <;> linarith
end GlobalTheory
