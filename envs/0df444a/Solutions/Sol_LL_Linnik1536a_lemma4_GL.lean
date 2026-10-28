-- Prove2me | solution 1 for LL_Linnik1536a.lemma4_GL
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T22:00:45.156543+00:00
-- url     : https://prove2.me/submissions/4b329ebb-390b-4bd3-b000-beecb68dc388

import Mathlib
import Definitions.Def_LL_Linnik1536a_Gpow
import Definitions.Def_LL_Linnik1536a_Spow
import Definitions.Def_LL_Linnik1536a_EL
import Definitions.Def_LL_Linnik1536a_devSet
import Theorems.Thm_LL_Linnik1536a_exp_le_even_partial
import Theorems.Thm_LL_Linnik1536a_moment_binom
import Theorems.Thm_LL_Linnik1536a_four_pow_le
import Theorems.Thm_LL_Linnik1536a_even_partial_le_int_exp
import Theorems.Thm_LL_Linnik1536a_moment_SL_nonneg
open Real MeasureTheory Finset

namespace A3S89LLg
open LL_Linnik1536a

lemma G_cont (L : ℕ) : Continuous (Gpow L) := by
  unfold Gpow; fun_prop

lemma S_cont (L : ℕ) : Continuous (Spow L) := by
  unfold Spow; fun_prop

lemma G_norm_le (L : ℕ) (x : ℝ) : ‖Gpow L x‖ ≤ L := by
  unfold Gpow
  refine (norm_sum_le _ _).trans ?_
  have : ∀ j ∈ range L, ‖Complex.exp (2 * π * Complex.I * ((2 : ℂ) ^ j * x))‖ = 1 := by
    intro j _
    rw [Complex.norm_exp]
    simp
    left
    exact_mod_cast Complex.ofReal_im ((2 : ℝ) ^ j)
  rw [Finset.sum_congr rfl this]
  simp

end A3S89LLg

open LL_Linnik1536a A3S89LLg in
theorem solution (L : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ x in (0 : ℝ)..1, Real.exp (lam * ‖LL_Linnik1536a.Gpow L x‖) ≤
      11 * (1 + lam * L) * LL_Linnik1536a.EL L lam := by
  set A : ℝ := lam * L with hA
  have hA0 : 0 ≤ A := mul_nonneg hlam (Nat.cast_nonneg _)
  set n := ⌈A⌉₊ with hn
  set K := 2 * n + 1 with hK
  set s : ℕ → ℝ := fun j => ∫ x in (0 : ℝ)..1, Spow L x ^ (2 * j) with hs
  set E := EL L lam with hE
  have hGc := G_cont L
  have hSc := S_cont L
  -- moments of S nonnegative, E ≥ partial sums
  have hmom : ∀ k : ℕ, 0 ≤ ∫ x in (0 : ℝ)..1, Spow L x ^ k := fun k =>
    LL_Linnik1536a.moment_SL_nonneg L k
  have hpart := LL_Linnik1536a.even_partial_le_int_exp hSc hmom hlam K
  have hE1 : 1 ≤ E := by
    have h1 := LL_Linnik1536a.even_partial_le_int_exp hSc hmom hlam 1
    simpa [hE, EL] using h1
  -- pointwise bound
  have hpt : ∀ x, Real.exp (lam * ‖Gpow L x‖) ≤
      2 * ∑ j ∈ range K, lam ^ (2 * j) / ((2 * j).factorial : ℝ) * ‖Gpow L x‖ ^ (2 * j) + 1 := by
    intro x
    have h := LL_Linnik1536a.exp_le_even_partial (A := A) (r := lam * ‖Gpow L x‖)
      (mul_nonneg hlam (norm_nonneg _)) (mul_le_mul_of_nonneg_left (G_norm_le L x) hlam)
    refine h.trans (le_of_eq ?_)
    congr 1; congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow]; ring
  have hint : ∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖) ≤
      2 * ∑ j ∈ range K, lam ^ (2 * j) / ((2 * j).factorial : ℝ) *
        (∫ x in (0 : ℝ)..1, ‖Gpow L x‖ ^ (2 * j)) + 1 := by
    have hc : ∀ j : ℕ, Continuous fun x => lam ^ (2 * j) / ((2 * j).factorial : ℝ) * ‖Gpow L x‖ ^ (2 * j) :=
      fun j => by fun_prop
    calc ∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖)
        ≤ ∫ x in (0 : ℝ)..1, (2 * ∑ j ∈ range K, lam ^ (2 * j) / ((2 * j).factorial : ℝ) *
            ‖Gpow L x‖ ^ (2 * j) + 1) := by
          apply intervalIntegral.integral_mono_on zero_le_one
          · exact (by fun_prop : Continuous fun x => Real.exp (lam * ‖Gpow L x‖)).intervalIntegrable _ _
          · exact (by fun_prop : Continuous fun x => (2 * ∑ j ∈ range K, lam ^ (2 * j) /
              ((2 * j).factorial : ℝ) * ‖Gpow L x‖ ^ (2 * j) + 1)).intervalIntegrable _ _
          · intro x _; exact hpt x
      _ = _ := by
          rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
            intervalIntegral.integral_finsetSum]
          · simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_const, sub_zero, one_smul, smul_eq_mul, mul_one]
          · intro j _; exact (hc j).intervalIntegrable _ _
          · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
          · exact intervalIntegrable_const
  -- moment comparison
  have hmb : ∀ j : ℕ, ∫ x in (0 : ℝ)..1, ‖Gpow L x‖ ^ (2 * j) ≤ (2 * j + 1) * s j := by
    intro j
    have h1 := LL_Linnik1536a.moment_binom L j
    have h2 := LL_Linnik1536a.four_pow_le j
    have hC : (0 : ℝ) < Nat.centralBinom j := by exact_mod_cast Nat.centralBinom_pos j
    have h4 : (0 : ℝ) < 4 ^ j := by positivity
    have hG0 : 0 ≤ ∫ x in (0 : ℝ)..1, ‖Gpow L x‖ ^ (2 * j) :=
      intervalIntegral.integral_nonneg zero_le_one (fun x _ => by positivity)
    have hs0 : 0 ≤ s j := hmom (2 * j)
    -- I ≤ 4^j / C * s ≤ (2j+1) s
    have h3 : ∫ x in (0 : ℝ)..1, ‖Gpow L x‖ ^ (2 * j) ≤ 4 ^ j / Nat.centralBinom j * s j := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hC]
      rw [div_mul_eq_mul_div, div_le_iff₀ h4] at h1
      linarith
    refine h3.trans (mul_le_mul_of_nonneg_right ?_ hs0)
    rw [div_le_iff₀ hC]; exact h2
  set a : ℕ → ℝ := fun j => lam ^ (2 * j) / ((2 * j).factorial : ℝ) * s j with ha
  have ha0 : ∀ j, 0 ≤ a j := fun j => mul_nonneg (by positivity) (hmom _)
  have hsum : ∑ j ∈ range K, lam ^ (2 * j) / ((2 * j).factorial : ℝ) *
      ∫ x in (0 : ℝ)..1, ‖Gpow L x‖ ^ (2 * j) ≤ (2 * K - 1) * ∑ j ∈ range K, a j := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjK : (j : ℝ) + 1 ≤ K := by
      have := Finset.mem_range.mp hj; exact_mod_cast this
    have hw : 0 ≤ lam ^ (2 * j) / ((2 * j).factorial : ℝ) := by positivity
    calc lam ^ (2 * j) / ((2 * j).factorial : ℝ) * ∫ x in (0 : ℝ)..1, ‖Gpow L x‖ ^ (2 * j)
        ≤ lam ^ (2 * j) / ((2 * j).factorial : ℝ) * ((2 * j + 1) * s j) :=
          mul_le_mul_of_nonneg_left (hmb j) hw
      _ = (2 * j + 1) * a j := by simp only [ha]; ring
      _ ≤ (2 * K - 1) * a j := mul_le_mul_of_nonneg_right (by linarith) (ha0 j)
  have hpartE : ∑ j ∈ range K, a j ≤ E := hpart
  have hnA : (n : ℝ) < A + 1 := Nat.ceil_lt_add_one hA0
  have hKr : (2 * (K : ℝ) - 1) ≤ 4 * A + 5 := by
    simp only [hK]; push_cast; linarith
  have hK1 : (0 : ℝ) ≤ 2 * K - 1 := by simp only [hK]; push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hE0 : 0 ≤ E := by linarith
  calc ∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖)
      ≤ 2 * ((2 * K - 1) * ∑ j ∈ range K, a j) + 1 :=
        hint.trans (by
          have h2 := mul_le_mul_of_nonneg_left hsum (show (0:ℝ) ≤ 2 by norm_num)
          linarith)
    _ ≤ 2 * ((4 * A + 5) * E) + E := by
        have := mul_le_mul hKr hpartE (Finset.sum_nonneg fun j _ => ha0 j) (by linarith)
        nlinarith
    _ ≤ 11 * (1 + A) * E := by nlinarith
