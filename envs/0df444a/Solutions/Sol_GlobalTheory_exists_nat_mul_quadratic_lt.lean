-- Prove2me | solution 1 for GlobalTheory.exists_nat_mul_quadratic_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:44:49.467203+00:00
-- url     : https://prove2.me/submissions/7fd67b63-2326-45a3-8cad-c267d8515957

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNatMulQuadraticLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (N : ℕ) (hN : 1 ≤ N) (a b q c : ℚ) (hq : q < 0) :
    ∃ k : ℕ, a + ((N : ℚ) * k) * b + ((N : ℚ) * k) ^ 2 * q < c := by
  set B : ℚ := (|b| + |a - c| + 1) / (-q) with hB
  have hq' : 0 < -q := by linarith
  have hBpos : 0 < B := div_pos (by positivity) hq'
  obtain ⟨k, hk⟩ := exists_nat_gt B
  refine ⟨k, ?_⟩
  have hk1 : (1 : ℚ) ≤ k := by
    have : (0 : ℚ) < k := lt_trans hBpos hk
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at this)
  have hN1 : (1 : ℚ) ≤ N := by exact_mod_cast hN
  set m : ℚ := (N : ℚ) * k with hm
  have hm1 : 1 ≤ m := by nlinarith
  have hmk : (k : ℚ) ≤ m := by nlinarith
  have hmB : B < m := lt_of_lt_of_le hk hmk
  have h1 : |b| + |a - c| + 1 < m * (-q) := by
    rw [hB, div_lt_iff₀ hq'] at hmB; linarith
  have h2 : m * (|b| + |a - c| + 1) < m * (m * (-q)) := mul_lt_mul_of_pos_left h1 (by linarith)
  have h3 : m * b ≤ m * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) (by linarith)
  have h4 : a - c ≤ |a - c| := le_abs_self _
  have h5 : 0 ≤ (m - 1) * (|a - c| + 1) := mul_nonneg (by linarith) (by positivity)
  nlinarith
end GlobalTheory
