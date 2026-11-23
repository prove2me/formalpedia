-- Prove2me | solution 1 for GrothendieckPD.Digits.claim_C_2_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:27:42.498853+00:00
-- url     : https://prove2.me/submissions/fc76453b-85e1-4e68-b91c-530a1d7085bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_ArcsineTail
import Theorems.Thm_GrothendieckPD_Digits_claim_C_2_5_arcsine_tail
import Theorems.Thm_GrothendieckPD_Digits_claim_C_2_5_cauchy_tail
import Theorems.Thm_GrothendieckPD_Digits_claim_C_2_5_numeric

open GrothendieckPD.Digits

theorem solution :
    (∀ i ∈ Finset.Icc 17 31, Summable fun k => |Hcoef i (k + 682)|) ∧
      ∑ i ∈ Finset.Icc 17 31, lam i * ∑' k, |Hcoef i (k + 682)| <
        (0.000002623422117515 : ℝ) := by
  have hlam : ∀ i ∈ Finset.Icc 17 31, 0 ≤ lam i := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi0 : 17 ≤ i := hi.1
    have hi1 : i ≤ 31 := hi.2
    interval_cases i <;> norm_num [lam]
  let T : ℕ → ℝ := fun i => ∑' k, |Hcoef i (k + 682)|
  have hsum : ∀ i ∈ Finset.Icc 17 31, Summable fun k => |Hcoef i (k + 682)| := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    by_cases hi17 : i = 17
    · subst i
      exact claim_C_2_5_cauchy_tail.1.1
    by_cases hi18 : i = 18
    · subst i
      exact claim_C_2_5_cauchy_tail.2.1
    · exact (claim_C_2_5_arcsine_tail i (Finset.mem_Icc.mpr ⟨by omega, hi.2⟩)).1
  refine ⟨hsum, ?_⟩
  have h17 : lam 17 * T 17 ≤ lam 17 * (6.982e-54 : ℝ) :=
    mul_le_mul_of_nonneg_left claim_C_2_5_cauchy_tail.1.2.le (hlam 17 (by simp))
  have h18 : lam 18 * T 18 ≤ lam 18 * (1.223e-13 : ℝ) :=
    mul_le_mul_of_nonneg_left claim_C_2_5_cauchy_tail.2.2.le (hlam 18 (by simp))
  have hmiddle : (∑ i ∈ Finset.Icc 19 31, lam i * T i) ≤
      ∑ i ∈ Finset.Icc 19 31, lam i * (1 - arcsinHead i) := by
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left (claim_C_2_5_arcsine_tail i hi).2
    have hi' := Finset.mem_Icc.mp hi
    exact hlam i (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hsplit : Finset.Icc 17 31 =
      insert 17 (insert 18 (Finset.Icc 19 31)) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  change (∑ i ∈ Finset.Icc 17 31, lam i * T i) < (0.000002623422117515 : ℝ)
  rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
  linarith [claim_C_2_5_numeric]
