-- Prove2me | solution 1 for GlobalTheory.sum_cn_isSquare_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:48:45.531776+00:00
-- url     : https://prove2.me/submissions/4213cc1b-3350-44a4-9b45-d9645b362a5a

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimePowerVonMangoldtSumBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqIocLe
import Theorems.Thm_GlobalTheory_sum_vonMangoldt_div_sq_Ioc_le

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
theorem _root_.solution
    (h : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) (x : ℝ) (hx : 1 ≤ x) (N : ℕ) :
    ∑ n ∈ (Icc 1 N).filter (fun n => IsSquare n), Formalism.HermitianLattices.GL2PrimeSums.cn x n ≤ 10 * Real.sqrt x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hcn : ∀ n : ℕ, 0 ≤ Formalism.HermitianLattices.GL2PrimeSums.cn x n := fun n =>
    mul_nonneg vonMangoldt_nonneg (le_min zero_le_one (div_nonneg hx0 (Nat.cast_nonneg _)))
  set y := Real.sqrt x with hy
  have hy1 : 1 ≤ y := Real.one_le_sqrt.mpr hx
  have hyy : y * y = x := Real.mul_self_sqrt hx0
  set K : ℕ := ⌊y⌋₊ with hKdef
  have hK1 : 1 ≤ K := Nat.le_floor (by simpa using hy1)
  have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hKy : (K : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyK : y < K + 1 := Nat.lt_floor_add_one y
  have hsub : (Icc 1 N).filter (fun n => IsSquare n) ⊆ (Icc 1 K ∪ Ioc K N).image (fun m => m ^ 2) := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨h1, h2⟩, r, rfl⟩ := hn
    refine mem_image.mpr ⟨r, ?_, sq r⟩
    have hr : 1 ≤ r := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
    have hrN : r ≤ N := le_trans (Nat.le_mul_self r) h2
    simp only [mem_union, mem_Icc, mem_Ioc]
    omega
  have hdisj : Disjoint (Icc 1 K) (Ioc K N) := by
    rw [disjoint_left]
    intro a h1 h2
    simp only [mem_Icc, mem_Ioc] at h1 h2
    omega
  have hA : ∑ m ∈ Icc 1 K, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) ≤ 2 * y := by
    calc ∑ m ∈ Icc 1 K, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) ≤ ∑ m ∈ Icc 1 K, Λ m := by
          refine sum_le_sum fun m _ => ?_
          unfold Formalism.HermitianLattices.GL2PrimeSums.cn
          rw [vonMangoldt_apply_pow (by norm_num)]
          exact mul_le_of_le_one_right vonMangoldt_nonneg (min_le_left _ _)
      _ ≤ 2 * (K : ℝ) := h K
      _ ≤ 2 * y := by linarith
  have hB : ∑ m ∈ Ioc K N, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) ≤ 8 * y := by
    calc ∑ m ∈ Ioc K N, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) ≤ ∑ m ∈ Ioc K N, x * (Λ m / (m : ℝ) ^ 2) := by
          refine sum_le_sum fun m _ => ?_
          unfold Formalism.HermitianLattices.GL2PrimeSums.cn
          rw [vonMangoldt_apply_pow (by norm_num)]
          calc Λ m * min 1 (x / ((m ^ 2 : ℕ) : ℝ)) ≤ Λ m * (x / ((m ^ 2 : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) vonMangoldt_nonneg
            _ = x * (Λ m / (m : ℝ) ^ 2) := by push_cast; ring
      _ = x * ∑ m ∈ Ioc K N, Λ m / (m : ℝ) ^ 2 := by rw [mul_sum]
      _ ≤ x * (4 / (K : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_vonMangoldt_div_sq_Ioc_le h K hK1 N) hx0
      _ ≤ 8 * y := by
          rw [← mul_div_assoc, div_le_iff₀ (by linarith), ← hyy]
          nlinarith
  calc ∑ n ∈ (Icc 1 N).filter (fun n => IsSquare n), Formalism.HermitianLattices.GL2PrimeSums.cn x n
      ≤ ∑ n ∈ (Icc 1 K ∪ Ioc K N).image (fun m => m ^ 2), Formalism.HermitianLattices.GL2PrimeSums.cn x n :=
        sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hcn n
    _ = ∑ m ∈ Icc 1 K ∪ Ioc K N, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) :=
        sum_image fun a _ b _ hab => Nat.pow_left_injective (by norm_num : 2 ≠ 0) hab
    _ = ∑ m ∈ Icc 1 K, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) + ∑ m ∈ Ioc K N, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) :=
        sum_union hdisj
    _ ≤ 10 * y := by linarith
end GlobalTheory
