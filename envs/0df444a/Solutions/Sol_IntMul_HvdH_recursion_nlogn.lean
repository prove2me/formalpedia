-- Prove2me | solution 1 for IntMul.HvdH.recursion_nlogn
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T14:09:13.524086+00:00
-- url     : https://prove2.me/submissions/f8cd229c-ee57-4741-923a-f3b6a755ae58

import Mathlib

namespace IntMul.HvdH.RecPf

/-- **Closing an `n log n` recursion.** If every `n ≥ n₀` satisfies
`M n ≤ Σ cᵢ M(mᵢ) + K·n·L n` with `cᵢ ≥ 0`, `1 ≤ mᵢ < n` and `Σ cᵢ mᵢ L(mᵢ) ≤ ρ n L n` for a fixed
`ρ < 1`, where `L ≥ 1`, then `M n ≤ C n L n` for all `n ≥ 1`. -/
theorem recursion_nlogn (M : ℕ → ℝ) (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (n₀ : ℕ) (K ρ : ℝ)
    (hK : 0 ≤ K) (hρ : ρ < 1)
    (step : ∀ n, n₀ ≤ n → 1 ≤ n → ∃ l : List (ℝ × ℕ),
      (∀ q ∈ l, 0 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.2 < n) ∧
      (l.map (fun q => q.1 * (q.2 * L q.2))).sum ≤ ρ * (n * L n) ∧
      M n ≤ (l.map (fun q => q.1 * M q.2)).sum + K * (n * L n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, 1 ≤ n → M n ≤ C * (n * L n) := by
  set B : ℝ := ∑ n ∈ Finset.range n₀, |M n|
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h1ρ : 0 < 1 - ρ := by linarith
  set C : ℝ := B + K / (1 - ρ)
  have hKC : 0 ≤ K / (1 - ρ) := div_nonneg hK h1ρ.le
  have hC : 0 ≤ C := by positivity
  have hCK : K ≤ C * (1 - ρ) := by
    have : C * (1 - ρ) = B * (1 - ρ) + K := by
      simp only [C]; field_simp
    rw [this]; nlinarith
  refine ⟨C, hC, fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  have hX : 1 ≤ (n : ℝ) * L n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [hL n]
  by_cases hn0 : n < n₀
  · have h1 : M n ≤ B := by
      calc M n ≤ |M n| := le_abs_self _
        _ ≤ B := Finset.single_le_sum (f := fun n => |M n|) (fun _ _ => abs_nonneg _)
            (Finset.mem_range.2 hn0)
    have h2 : B ≤ C := by simp only [C]; linarith
    nlinarith
  · obtain ⟨l, hl, hsum, hM⟩ := step n (by omega) hn
    have hle : (l.map (fun q => q.1 * M q.2)).sum ≤
        (l.map (fun q => C * (q.1 * (q.2 * L q.2)))).sum := by
      apply List.sum_le_sum
      intro q hq
      obtain ⟨hc, hm1, hmn⟩ := hl q hq
      have := ih q.2 hmn hm1
      nlinarith
    rw [List.sum_map_mul_left] at hle
    have : C * (l.map (fun q => q.1 * (q.2 * L q.2))).sum ≤ C * (ρ * (n * L n)) :=
      mul_le_mul_of_nonneg_left hsum hC
    nlinarith

end IntMul.HvdH.RecPf

open IntMul.HvdH

theorem solution (M : ℕ → ℝ) (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (n₀ : ℕ) (K ρ : ℝ)
    (hK : 0 ≤ K) (hρ : ρ < 1)
    (step : ∀ n, n₀ ≤ n → 1 ≤ n → ∃ l : List (ℝ × ℕ),
      (∀ q ∈ l, 0 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.2 < n) ∧
      (l.map (fun q => q.1 * (q.2 * L q.2))).sum ≤ ρ * (n * L n) ∧
      M n ≤ (l.map (fun q => q.1 * M q.2)).sum + K * (n * L n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, 1 ≤ n → M n ≤ C * (n * L n) := IntMul.HvdH.RecPf.recursion_nlogn M L hL n₀ K ρ hK hρ step
