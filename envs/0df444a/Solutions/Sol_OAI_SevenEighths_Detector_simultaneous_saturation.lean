-- Prove2me | solution 1 for OAI.SevenEighths.Detector.simultaneous_saturation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:53:47.592544+00:00
-- url     : https://prove2.me/submissions/dbfe15b4-a559-4cc7-a918-d296ec699e9e

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Detector
namespace OAI.SevenEighths.Detector
theorem _root_.solution {U δ r m ε A B : ℝ}
    (hU : 1 < U) (hδ : (1 / 50 : ℝ) ≤ δ) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hprod : U ^ (δ * (r + m) - ε) ≤ A * B)
    (hupperA : A ≤ U ^ (δ * r + ε))
    (hupperB : B ≤ U ^ (δ * min m (1 - m) + ε)) :
    m ≤ 1 / 2 + 75 * ε ∧
      U ^ (δ * r - 2 * ε) ≤ A ∧ U ^ (δ * m - 2 * ε) ≤ B := by
  have hU0 : 0 < U := by linarith
  have hδ0 : 0 ≤ δ := by linarith
  have hBcoarse : B ≤ U ^ (δ * m + ε) := by
    apply hupperB.trans
    exact Real.rpow_le_rpow_of_exponent_le hU.le
      (by have h := mul_le_mul_of_nonneg_left (min_le_left m (1 - m)) hδ0; linarith)
  have hpupper : A * B ≤ U ^ (δ * r + ε + (δ * min m (1 - m) + ε)) := by
    rw [Real.rpow_add hU0]
    exact mul_le_mul hupperA hupperB hB (Real.rpow_nonneg hU0.le _)
  have hexp := (Real.rpow_le_rpow_left_iff hU).mp (hprod.trans hpupper)
  have hlength : m ≤ 1 / 2 + 75 * ε := by
    by_cases hm : m ≤ 1 / 2
    · linarith
    · have hmin : min m (1 - m) = 1 - m := min_eq_right (by linarith)
      rw [hmin] at hexp
      have hm0 : 0 ≤ m - 1 / 2 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hδ hm0
      nlinarith
  have hlowerA : U ^ (δ * r - 2 * ε) ≤ A := by
    have hp : U ^ (δ * r - 2 * ε) * U ^ (δ * m + ε) ≤
        A * U ^ (δ * m + ε) := by
      calc
        _ = U ^ (δ * (r + m) - ε) := by rw [← Real.rpow_add hU0]; congr 1; ring
        _ ≤ A * B := hprod
        _ ≤ _ := mul_le_mul_of_nonneg_left hBcoarse hA
    have hpos := Real.rpow_pos_of_pos hU0 (δ * m + ε)
    nlinarith
  have hlowerB : U ^ (δ * m - 2 * ε) ≤ B := by
    have hp : U ^ (δ * m - 2 * ε) * U ^ (δ * r + ε) ≤
        B * U ^ (δ * r + ε) := by
      calc
        _ = U ^ (δ * (r + m) - ε) := by rw [← Real.rpow_add hU0]; congr 1; ring
        _ ≤ A * B := hprod
        _ ≤ _ := by simpa [mul_comm] using mul_le_mul_of_nonneg_right hupperA hB
    have hpos := Real.rpow_pos_of_pos hU0 (δ * r + ε)
    nlinarith
  exact ⟨hlength, hlowerA, hlowerB⟩
end OAI.SevenEighths.Detector
