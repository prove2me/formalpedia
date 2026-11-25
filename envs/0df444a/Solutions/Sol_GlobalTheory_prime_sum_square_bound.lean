-- Prove2me | solution 1 for GlobalTheory.prime_sum_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:48:44.950567+00:00
-- url     : https://prove2.me/submissions/934af0af-9979-4d98-b281-1b06fb31abf9

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimePowerVonMangoldtSumBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeomIccOneLeTwoMulSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqTail
import Theorems.Thm_GlobalTheory_sum_vonMangoldt_div_sq_tail
import Theorems.Thm_GlobalTheory_large_prime_sum_bound
import Theorems.Thm_GlobalTheory_prime_power_von_mangoldt_sum_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : Formalism.HermitianLattices.GL2a2.SizeSpSq := by
  intro hψ
  obtain ⟨C, hC⟩ := prime_power_von_mangoldt_sum_bound
  have hL : Formalism.HermitianLattices.GL2a2.SizeSpLarge := GlobalTheory.large_prime_sum_bound
  have hψ' : ∀ N : ℕ, ∑ n ∈ Icc 1 N, Λ n ≤ 2 * (N : ℝ) := fun N => by
    simpa using hψ N (Nat.cast_nonneg N)
  refine ⟨6 * C ^ 2 + 12800, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  set N : ℕ := ⌊x ^ (400 : ℝ)⌋₊ with hN
  have hNz : (N : ℝ) ≤ x ^ (400 : ℝ) := Nat.floor_le (by positivity)
  set M : ℕ := ⌊x⌋₊ with hM
  have hM1 : 1 ≤ M := Nat.le_floor (by simpa using (by linarith : (1 : ℝ) ≤ x))
  have hMx : (M : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxM : x < M + 1 := Nat.lt_floor_add_one x
  have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  set K : ℕ := ⌊√x⌋₊ with hK
  have hKx : (K : ℝ) ≤ √x := Nat.floor_le (Real.sqrt_nonneg x)
  have hxK : √x < K + 1 := Nat.lt_floor_add_one _
  have hs0 : 0 < √x := Real.sqrt_pos.2 hx0
  have hlogs : Real.log √x = Real.log x / 2 := Real.log_sqrt hx0.le
  have hsP : ∀ p : ℕ, 0 ≤ Formalism.HermitianLattices.GL2a2.sP x p := fun p => by
    unfold Formalism.HermitianLattices.GL2a2.sP Formalism.HermitianLattices.GL2PrimeSums.cn
    exact sum_nonneg fun i _ => mul_nonneg vonMangoldt_nonneg (le_min zero_le_one (by positivity))
  let f₁ : ℕ → ℝ := fun n => if n ∈ Icc 1 K then C ^ 2 * Real.log x ^ 2 else 0
  let f₂ : ℕ → ℝ := fun n => if n ∈ Icc 1 M then 2 * C ^ 2 * Real.log x * Λ n else 0
  let f₃ : ℕ → ℝ := fun n => if n ∈ Ioc M N then 1600 * x ^ 2 * Real.log x * (Λ n / (n : ℝ) ^ 2) else 0
  have hf₁ : ∀ n, 0 ≤ f₁ n := fun n => by simp only [f₁]; split_ifs <;> positivity
  have hf₂ : ∀ n, 0 ≤ f₂ n := fun n => by
    have : 0 ≤ Λ n := vonMangoldt_nonneg
    simp only [f₂]; split_ifs <;> positivity
  have hf₃ : ∀ n, 0 ≤ f₃ n := fun n => by
    have : 0 ≤ Λ n := vonMangoldt_nonneg
    simp only [f₃]; split_ifs <;> positivity
  have hterm : ∀ p ∈ (Icc 1 N).filter (fun p => p.Prime),
      Formalism.HermitianLattices.GL2a2.sP x p ^ 2 ≤ f₁ p + f₂ p + f₃ p := by
    intro p hp
    simp only [mem_filter, mem_Icc] at hp
    obtain ⟨⟨hp1, hpN⟩, hp⟩ := hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hall : Formalism.HermitianLattices.GL2a2.sP x p ^ 2 ≤ C ^ 2 * Real.log x ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (hsP p) (hC x hx p hp) 2
    by_cases h1 : p ≤ K
    · have : f₁ p = C ^ 2 * Real.log x ^ 2 := if_pos (mem_Icc.2 ⟨hp1, h1⟩)
      linarith [hf₂ p, hf₃ p]
    by_cases h2 : p ≤ M
    · have e : f₂ p = 2 * C ^ 2 * Real.log x * Λ p := if_pos (mem_Icc.2 ⟨hp1, h2⟩)
      rw [vonMangoldt_apply_prime hp] at e
      have hKp : (K : ℝ) + 1 ≤ p := by exact_mod_cast (by omega : K + 1 ≤ p)
      have : Real.log √x ≤ Real.log p := Real.log_le_log hs0 (by linarith)
      have h3 : Real.log x ≤ 2 * Real.log p := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ C ^ 2 * Real.log x)
      nlinarith [hf₁ p, hf₃ p]
    · have e : f₃ p = 1600 * x ^ 2 * Real.log x * (Λ p / (p : ℝ) ^ 2) :=
        if_pos (mem_Ioc.2 ⟨by omega, hpN⟩)
      rw [vonMangoldt_apply_prime hp] at e
      have hMp : (M : ℝ) + 1 ≤ p := by exact_mod_cast (by omega : M + 1 ≤ p)
      have h3 : Formalism.HermitianLattices.GL2a2.sP x p ^ 2 ≤ (2 * x * Real.log p / p) ^ 2 :=
        pow_le_pow_left₀ (hsP p) (hL x hx0 p hp (by linarith)) 2
      have hpN' : (p : ℝ) ≤ N := by exact_mod_cast hpN
      have h4 : Real.log p ≤ 400 * Real.log x := by
        rw [← Real.log_rpow hx0]
        exact Real.log_le_log hp0 (hpN'.trans hNz)
      have h5 := mul_le_mul_of_nonneg_left h4
        (by positivity : 0 ≤ 4 * x ^ 2 * (Real.log p / (p : ℝ) ^ 2))
      have e2 : (2 * x * Real.log p / p) ^ 2 = 4 * x ^ 2 * (Real.log p / (p : ℝ) ^ 2) * Real.log p := by
        ring
      nlinarith [hf₁ p, hf₂ p]
  have hsum : ∀ (S T : Finset ℕ) (g : ℕ → ℝ), (∀ n, 0 ≤ g n) →
      ∑ n ∈ S, (if n ∈ T then g n else 0) ≤ ∑ n ∈ T, g n := by
    intro S T g hg
    rw [sum_ite_mem]
    exact sum_le_sum_of_subset_of_nonneg inter_subset_right fun n _ _ => hg n
  have s₁ : ∑ p ∈ (Icc 1 N).filter (fun p => p.Prime), f₁ p ≤ 2 * C ^ 2 * x * Real.log x := by
    refine (hsum _ _ _ fun n => by positivity).trans ?_
    simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    have h1 : Real.log √x ≤ √x - 1 := Real.log_le_sub_one_of_pos hs0
    have h2 : √x * √x = x := Real.mul_self_sqrt hx0.le
    have h3 : (K : ℝ) * Real.log x ≤ 2 * x := by
      have : (K : ℝ) * Real.log x ≤ √x * (2 * √x) :=
        mul_le_mul hKx (by linarith) hlx hs0.le
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ C ^ 2 * Real.log x)
    nlinarith
  have s₂ : ∑ p ∈ (Icc 1 N).filter (fun p => p.Prime), f₂ p ≤ 4 * C ^ 2 * x * Real.log x := by
    refine (hsum _ _ _ fun n => by
      have : 0 ≤ Λ n := vonMangoldt_nonneg
      positivity).trans ?_
    rw [← mul_sum]
    have h4 := mul_le_mul_of_nonneg_left ((hψ' M).trans (by linarith : 2 * (M : ℝ) ≤ 2 * x))
      (by positivity : 0 ≤ 2 * C ^ 2 * Real.log x)
    linarith
  have s₃ : ∑ p ∈ (Icc 1 N).filter (fun p => p.Prime), f₃ p ≤ 12800 * x * Real.log x := by
    refine (hsum _ _ _ fun n => by
      have : 0 ≤ Λ n := vonMangoldt_nonneg
      positivity).trans ?_
    rw [← mul_sum]
    have h1 : 4 / (M : ℝ) ≤ 8 / x := by
      rw [div_le_div_iff₀ (by linarith) hx0]
      linarith
    have h4 := mul_le_mul_of_nonneg_left ((sum_vonMangoldt_div_sq_tail hψ' M hM1 N).trans h1)
      (by positivity : 0 ≤ 1600 * x ^ 2 * Real.log x)
    have e : 1600 * x ^ 2 * Real.log x * (8 / x) = 12800 * x * Real.log x := by
      field_simp
      ring
    linarith
  have := sum_le_sum hterm
  rw [sum_add_distrib, sum_add_distrib] at this
  linarith
end GlobalTheory
