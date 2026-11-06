-- Prove2me | solution 1 for OAI.PowerExtraction.from_mean_square_and_prime_rows_with_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:25:17.073477+00:00
-- url     : https://prove2.me/submissions/1f0880aa-3d82-45f2-9e62-5f6f70d44790

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
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
open OAI.PowerExtraction
namespace OAI.PowerExtraction
theorem _root_.solution
    (D ε J A C : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hJ : D ^ ((11 / 60 : ℝ) - ε) ≤ J)
    (hmean : J * A ^ 2 ≤
      2 * D ^ ((21 / 10 : ℝ) + ε) +
      2 * J * C ^ 2 * D ^ (49 / 30 : ℝ)) :
    A ≤ 2 * C * D ^ ((23 / 24 : ℝ) + ε) := by
  let E : ℝ := (23 / 24 : ℝ) + ε
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hJpos : 0 < J := lt_of_lt_of_le (Real.rpow_pos_of_pos hDpos _) hJ
  have hpow :
      D ^ ((21 / 10 : ℝ) + ε) ≤
        J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      D ^ ((21 / 10 : ℝ) + ε) =
          D ^ ((11 / 60 : ℝ) - ε) *
            D ^ ((23 / 12 : ℝ) + 2 * ε) := by
            rw [← Real.rpow_add hDpos]
            congr 1
            ring
      _ ≤ J * D ^ ((23 / 12 : ℝ) + 2 * ε) :=
          mul_le_mul_of_nonneg_right hJ (by positivity)
  have herr : D ^ (49 / 30 : ℝ) ≤
      D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hD
    linarith
  have hC2 : 1 ≤ C ^ 2 := by nlinarith
  have hP : 0 ≤ J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by positivity
  have hsq : A ^ 2 ≤
      4 * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    have hmain : J * A ^ 2 ≤
        4 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
      calc
        J * A ^ 2 ≤
            2 * D ^ ((21 / 10 : ℝ) + ε) +
            2 * J * C ^ 2 * D ^ (49 / 30 : ℝ) := hmean
        _ ≤ 2 * (J * D ^ ((23 / 12 : ℝ) + 2 * ε)) +
            2 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
              gcongr
        _ ≤ 4 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hC2) hP]
    nlinarith
  have hexp : (23 / 12 : ℝ) + 2 * ε = E * 2 := by
    dsimp [E]
    ring
  have hpow2 : (D ^ E) ^ 2 = D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      (D ^ E) ^ 2 = D ^ (E * 2) :=
        (Real.rpow_mul_natCast hDpos.le E 2).symm
      _ = D ^ ((23 / 12 : ℝ) + 2 * ε) := by rw [hexp]
  have htwo : 0 ≤ 2 * C * D ^ E := by positivity
  apply (sq_le_sq₀ hA htwo).mp
  rw [mul_pow, mul_pow, hpow2]
  nlinarith
end OAI.PowerExtraction
