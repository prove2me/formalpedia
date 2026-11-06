-- Prove2me | solution 1 for OAI.PowerExtraction.from_mean_square_and_prime_rows_with_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:48:00.200674+00:00
-- url     : https://prove2.me/submissions/cf7cd50a-f936-4dcd-897b-f7c1996b36c5

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open OAI.PowerExtraction
namespace OAI.PowerExtraction
theorem _root_.solution
    (D ε J A C M : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hC : 1 ≤ C) (hM : 1 ≤ M)
    (hcount : D ^ ((11 / 60 : ℝ) - ε) ≤ M * J)
    (hmean : J * A ^ 2 ≤
      2 * M * D ^ ((21 / 10 : ℝ) + ε) +
        2 * J * C ^ 2 * D ^ (49 / 30 : ℝ)) :
    A ≤ 2 * (M + C) * D ^ ((23 / 24 : ℝ) + ε) := by
  let E : ℝ := (23 / 24 : ℝ) + ε
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hMJpos : 0 < M * J :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hDpos _) hcount
  have hJpos : 0 < J := by
    nlinarith
  have hbase : D ^ ((21 / 10 : ℝ) + ε) ≤
      (M * J) * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      D ^ ((21 / 10 : ℝ) + ε) =
          D ^ ((11 / 60 : ℝ) - ε) *
            D ^ ((23 / 12 : ℝ) + 2 * ε) := by
              rw [← Real.rpow_add hDpos]
              congr 1
              ring
      _ ≤ (M * J) * D ^ ((23 / 12 : ℝ) + 2 * ε) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
  have hpow : M * D ^ ((21 / 10 : ℝ) + ε) ≤
      M ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      M * D ^ ((21 / 10 : ℝ) + ε) ≤
          M * ((M * J) * D ^ ((23 / 12 : ℝ) + 2 * ε)) :=
            mul_le_mul_of_nonneg_left hbase hMpos.le
      _ = M ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by ring
  have herr : D ^ (49 / 30 : ℝ) ≤
      D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hD
    linarith
  have hcoeff : 2 * M ^ 2 + 2 * C ^ 2 ≤ 4 * (M + C) ^ 2 := by
    nlinarith [mul_nonneg hMpos.le hCpos.le]
  have hT : 0 ≤ J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by positivity
  have hmain : J * A ^ 2 ≤
      4 * (M + C) ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      J * A ^ 2 ≤
          2 * M * D ^ ((21 / 10 : ℝ) + ε) +
            2 * J * C ^ 2 * D ^ (49 / 30 : ℝ) := hmean
      _ ≤ 2 * (M ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε)) +
            2 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
              have hleft :
                  2 * M * D ^ ((21 / 10 : ℝ) + ε) ≤
                    2 * (M ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε)) := by
                nlinarith [hpow]
              have hright :
                  2 * J * C ^ 2 * D ^ (49 / 30 : ℝ) ≤
                    2 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
                exact mul_le_mul_of_nonneg_left herr (by positivity)
              linarith
      _ = (2 * M ^ 2 + 2 * C ^ 2) *
            (J * D ^ ((23 / 12 : ℝ) + 2 * ε)) := by ring
      _ ≤ 4 * (M + C) ^ 2 *
            (J * D ^ ((23 / 12 : ℝ) + 2 * ε)) :=
              mul_le_mul_of_nonneg_right hcoeff hT
      _ = 4 * (M + C) ^ 2 * J *
            D ^ ((23 / 12 : ℝ) + 2 * ε) := by ring
  have hsq : A ^ 2 ≤
      4 * (M + C) ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    nlinarith
  have hexp : (23 / 12 : ℝ) + 2 * ε = E * 2 := by
    dsimp [E]
    ring
  have hpow2 : (D ^ E) ^ 2 = D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      (D ^ E) ^ 2 = D ^ (E * 2) :=
        (Real.rpow_mul_natCast hDpos.le E 2).symm
      _ = D ^ ((23 / 12 : ℝ) + 2 * ε) := by rw [hexp]
  have htarget : 0 ≤ 2 * (M + C) * D ^ E := by positivity
  apply (sq_le_sq₀ hA htarget).mp
  rw [mul_pow, mul_pow, hpow2]
  nlinarith
end OAI.PowerExtraction
