-- Prove2me | solution 1 for LubyMIS.MonteCarlo.pi_injective_prob
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:45:17.436301+00:00
-- url     : https://prove2.me/submissions/1cc30c1f-d900-4817-a5eb-901ad07b6629

import Mathlib
import Definitions.Def_LubyMIS_MonteCarlo_Basic

namespace LubyMIS.MonteCarlo

theorem aux_piinj_desc (N : ℕ) : ∀ k : ℕ, k ≤ N →
    2 * (N : ℝ) ^ (k + 1) - (k : ℝ) * ((k : ℝ) - 1) * (N : ℝ) ^ k
      ≤ 2 * (N : ℝ) * (N.descFactorial k : ℝ) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : k ≤ N := by omega
    have h := ih hk'
    rw [Nat.descFactorial_succ]
    push_cast [Nat.cast_sub hk']
    have hNk : (0 : ℝ) ≤ (N : ℝ) - k := by
      have : (k : ℝ) ≤ N := by exact_mod_cast hk'
      linarith
    have hpow : (0 : ℝ) ≤ (N : ℝ) ^ k := by positivity
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hkk : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) * (N : ℝ) ^ k * k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; simp
      · have : (1 : ℝ) ≤ k := by exact_mod_cast h0
        have : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
        positivity
    have := mul_le_mul_of_nonneg_left h hNk
    have e1 : (N : ℝ) ^ (k + 1 + 1) = (N : ℝ) ^ k * N * N := by ring
    have e2 : (N : ℝ) ^ (k + 1) = (N : ℝ) ^ k * N := by ring
    rw [e1, e2]
    rw [e2] at this
    nlinarith

theorem aux_piinj_inj {V : Type*} {n : ℕ} (π₀ : V → Fin (n ^ 4)) :
    Function.Injective (prioA π₀) ↔ Function.Injective π₀ := by
  constructor
  · intro h i j hij
    apply h
    simp [prioA, hij]
  · intro h i j hij
    apply h
    simp only [prioA] at hij
    exact Fin.ext (by omega)

end LubyMIS.MonteCarlo

open LubyMIS.MonteCarlo

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (n : ℕ) (hn : 1 ≤ n)
    (hV : Fintype.card V ≤ n) :
    probA (V := V) n (fun π => Function.Injective π) ≥ 1 - 1 / (2 * (n : ℝ) ^ 2) := by
  classical
  set N := n ^ 4 with hN
  set k := Fintype.card V with hk
  have hcard : ((Finset.univ.filter (fun π₀ : V → Fin (n ^ 4) =>
      Function.Injective (prioA π₀))).card : ℝ) = (N.descFactorial k : ℝ) := by
    have h1 : (Finset.univ.filter (fun π₀ : V → Fin (n ^ 4) =>
        Function.Injective (prioA π₀))) =
        (Finset.univ.filter (fun π₀ : V → Fin (n ^ 4) => Function.Injective π₀)) := by
      ext π₀; simp [aux_piinj_inj]
    rw [h1]
    have h2 := Fintype.card_subtype (fun π₀ : V → Fin (n ^ 4) => Function.Injective π₀)
    rw [← h2]
    rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding V (Fin (n ^ 4)))]
    rw [Fintype.card_embedding_eq]
    simp [N, k]
  unfold probA
  beta_reduce
  rw [← hk]
  convert_to (N.descFactorial k : ℝ) / ((n : ℝ) ^ 4) ^ k ≥ 1 - 1 / (2 * (n : ℝ) ^ 2)
  · rw [← hcard]; congr 3; ext x; simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hkN : k ≤ N := by
    have : n ≤ n ^ 4 := Nat.le_self_pow (by norm_num) n
    omega
  have key := aux_piinj_desc N k hkN
  have hNr : (N : ℝ) = (n : ℝ) ^ 4 := by simp [N]
  rw [hNr] at key
  have hkr : (k : ℝ) ≤ n := by exact_mod_cast hV
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hNpos : (0 : ℝ) < (n : ℝ) ^ 4 := by positivity
  have hPpos : (0 : ℝ) < ((n : ℝ) ^ 4) ^ k := by positivity
  rw [ge_iff_le, le_div_iff₀ hPpos]
  -- key : 2 M^(k+1) - k(k-1) M^k ≤ 2 M D  where M = n^4
  set M := (n : ℝ) ^ 4 with hM
  set D := (N.descFactorial k : ℝ)
  have hkk : (k : ℝ) * ((k : ℝ) - 1) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hMk : (0 : ℝ) ≤ M ^ k := by positivity
  have e : M ^ (k + 1) = M ^ k * M := by ring
  rw [e] at key
  -- goal: (1 - 1/(2 n^2)) * M^k ≤ D
  have h2 : 2 * M * ((1 - 1 / (2 * (n : ℝ) ^ 2)) * M ^ k) ≤ 2 * M * D := by
    have : 2 * M * ((1 - 1 / (2 * (n : ℝ) ^ 2)) * M ^ k)
        = 2 * M ^ k * M - (n : ℝ) ^ 2 * M ^ k := by
      rw [hM]; field_simp
    rw [this]
    have : (k : ℝ) * ((k : ℝ) - 1) * M ^ k ≤ (n : ℝ) ^ 2 * M ^ k :=
      mul_le_mul_of_nonneg_right hkk hMk
    linarith
  have h2M : (0 : ℝ) < 2 * M := by positivity
  exact le_of_mul_le_mul_left h2 h2M
