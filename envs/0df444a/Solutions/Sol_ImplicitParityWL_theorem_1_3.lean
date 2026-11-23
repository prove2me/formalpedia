-- Prove2me | solution 1 for ImplicitParityWL.theorem_1_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:19:44.140977+00:00
-- url     : https://prove2.me/submissions/d8f87021-c3ad-4905-9d0f-87ae4d5636f0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_VariableWL
import Theorems.Thm_ImplicitParityWL_theorem_1_3_colored
import Theorems.Thm_ImplicitParityWL_footnote_3_color_removal

theorem solution (k : ℕ) (hk : 3 ≤ k) : ∃ c : ℝ, 0 < c ∧ ∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧
    ∃ (G₀ G₁ : SimpleGraph (Fin n)) (T : ℕ),
      OAI.VariableWL.histogram ⟨n, G₀⟩ k T ≠ OAI.VariableWL.histogram ⟨n, G₁⟩ k T ∧
      (∀ r < T, OAI.VariableWL.histogram ⟨n, G₀⟩ k r = OAI.VariableWL.histogram ⟨n, G₁⟩ k r) ∧
      c * (n : ℝ) ^ (k - 1) ≤ (T : ℝ) := by
  obtain ⟨Ck, b, hCk, _, hcol⟩ := ImplicitParityWL.theorem_1_3_colored k hk
  obtain ⟨Cr, hrem⟩ := ImplicitParityWL.footnote_3_color_removal
  let M : ℕ := max 1 (Cr * Ck)
  have hM_pos : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hM_ge : Cr * Ck ≤ M := le_max_right _ _
  have hM_real_pos : (0 : ℝ) < (M : ℝ) ^ (k - 1) := pow_pos (Nat.cast_pos.mpr hM_pos) _
  refine ⟨1 / ((M : ℝ) ^ (k - 1)), one_div_pos.mpr hM_real_pos, ?_⟩
  intro n₀
  let ℓ : ℕ := max 1 (max n₀ (2 * k))
  have hℓ1 : 1 ≤ ℓ := le_max_left _ _
  have hn₀_ℓ : n₀ ≤ ℓ := le_trans (le_max_left _ _) (le_max_right _ _)
  have h2k_ℓ : 2 * k ≤ ℓ := le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨hcard_eq, hN_lo, hN_hi, T₀, hFirst, hT₀_lo, _⟩ := hcol ℓ hℓ1
  set N := Fintype.card ((ImplicitParityWL.counter k ℓ).Vertex 0)
  have h2ℓ_pos : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hN1 : 1 ≤ N := by
    have : 1 ≤ 2 * k * 2 ^ ℓ := by nlinarith
    exact le_trans this hN_lo
  obtain ⟨n, hn_lo, hn_hi, G₀, G₁, T, hneq, heq, hTT⟩ :=
    hrem k (by omega) ((ImplicitParityWL.counter k ℓ).graph 0)
      ((ImplicitParityWL.counter k ℓ).graph 1) N T₀ hN1 rfl hcard_eq.symm hFirst
  have hn₀_n : n₀ ≤ n := by
    have h1 : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
    have h2 : 2 ^ ℓ ≤ 2 * k * 2 ^ ℓ := by nlinarith
    omega
  have hn_upper : n ≤ M * 2 ^ ℓ := by
    calc n ≤ Cr * N := hn_hi
      _ ≤ Cr * (Ck * 2 ^ ℓ) := Nat.mul_le_mul_left Cr hN_hi
      _ = (Cr * Ck) * 2 ^ ℓ := (Nat.mul_assoc Cr Ck (2 ^ ℓ)).symm
      _ ≤ M * 2 ^ ℓ := Nat.mul_le_mul_right (2 ^ ℓ) hM_ge
  have hT_lower : (2 ^ ℓ) ^ (k - 1) ≤ T := by
    have hm_ge : ℓ ≤ (k - 1) * ℓ - 1 := by
      have : 2 * ℓ ≤ (k - 1) * ℓ := Nat.mul_le_mul_right ℓ (by omega)
      omega
    have hm_pos : 1 ≤ (k - 1) * ℓ := by
      have : 2 * 1 ≤ (k - 1) * ℓ := Nat.mul_le_mul (by omega) hℓ1
      omega
    have hpow_split : 3 * 2 ^ ((k - 1) * ℓ - 1) = 2 ^ ((k - 1) * ℓ) + 2 ^ ((k - 1) * ℓ - 1) := by
      have : 2 ^ ((k - 1) * ℓ) = 2 * 2 ^ ((k - 1) * ℓ - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hm_pos, Nat.pow_succ, Nat.mul_comm]
      omega
    have h2k_pow : 2 * k ≤ 2 ^ ((k - 1) * ℓ - 1) := by
      have hlt : 2 * k < 2 ^ (2 * k) := Nat.lt_two_pow_self
      have hle : 2 ^ (2 * k) ≤ 2 ^ ((k - 1) * ℓ - 1) :=
        Nat.pow_le_pow_right (by omega) (le_trans h2k_ℓ hm_ge)
      omega
    have hpow_eq : (2 ^ ℓ) ^ (k - 1) = 2 ^ ((k - 1) * ℓ) := by
      rw [← Nat.pow_mul, Nat.mul_comm]
    omega
  refine ⟨n, hn₀_n, G₀, G₁, T, hneq, heq, ?_⟩
  have hn_real : (n : ℝ) ^ (k - 1) ≤ (M : ℝ) ^ (k - 1) * (T : ℝ) := by
    have h1 : (n : ℝ) ≤ (M : ℝ) * (2 ^ ℓ : ℕ) := by exact_mod_cast hn_upper
    have h2 : (n : ℝ) ^ (k - 1) ≤ ((M : ℝ) * (2 ^ ℓ : ℕ)) ^ (k - 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg n) h1 (k - 1)
    rw [mul_pow] at h2
    have h3 : (((2 ^ ℓ : ℕ) : ℝ)) ^ (k - 1) ≤ (T : ℝ) := by exact_mod_cast hT_lower
    exact le_trans h2 (mul_le_mul_of_nonneg_left h3 (le_of_lt hM_real_pos))
  rw [one_div_mul_eq_div, div_le_iff₀ hM_real_pos, mul_comm]
  exact hn_real
