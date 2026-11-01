-- Prove2me | solution 1 for HomotopyProxVM.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-31T12:13:40.481988+00:00
-- url     : https://prove2.me/submissions/2a031eb2-aaa4-424c-869e-1fb335aa0720

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution {M q : ℝ} {τ : ℕ → ℝ} (hM : 0 < M) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hτ : ∀ k, τ k ∈ Set.Ioo (0 : ℝ) 1)
    (hrec : ∀ k, τ (k + 1) ≤ τ k + M * q ^ k * τ k * τ (k + 1)) (k : ℕ)
    (hden : 0 < 1 - q - τ 0 * M * (1 - q ^ k)) :
    τ k ≤ τ 0 * (1 - q) / (1 - q - τ 0 * M * (1 - q ^ k)) ∧
    ((1 - τ 0) * (1 - q) - τ 0 * M + τ 0 * M * q ^ k) / (1 - q - τ 0 * M * (1 - q ^ k))
      ≤ 1 - τ k := by
  have hq1 : 0 < 1 - q := sub_pos.mpr hq.2
  have hstep (n : ℕ) : 1 / τ n - M * q ^ n ≤ 1 / τ (n + 1) := by
    have ht := (hτ n).1
    have hu := (hτ (n + 1)).1
    apply (le_div_iff₀ hu).mpr
    rw [sub_mul, div_mul_eq_mul_div]
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ ht).mpr
    nlinarith [hrec n]
  have hbound (n : ℕ) : 1 / τ 0 - M * (1 - q ^ n) / (1 - q) ≤ 1 / τ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hs := hstep n
      have heq : M * (1 - q ^ (n + 1)) / (1 - q) =
          M * (1 - q ^ n) / (1 - q) + M * q ^ n := by
        rw [pow_succ]
        field_simp
        <;> ring
      rw [heq]
      linarith
  have hscaled := (le_div_iff₀ (hτ k).1).mp (hbound k)
  have heq : (1 / τ 0 - M * (1 - q ^ k) / (1 - q)) * τ k =
      (1 - q - τ 0 * M * (1 - q ^ k)) * τ k / (τ 0 * (1 - q)) := by
    field_simp [(hτ 0).1.ne', hq1.ne']
    <;> ring
  rw [heq] at hscaled
  have hmul := (div_le_iff₀ (mul_pos (hτ 0).1 hq1)).mp hscaled
  have hupper : τ k ≤ τ 0 * (1 - q) / (1 - q - τ 0 * M * (1 - q ^ k)) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  refine ⟨hupper, ?_⟩
  apply (div_le_iff₀ hden).mpr
  have hupper' := (le_div_iff₀ hden).mp hupper
  nlinarith

#print axioms solution
