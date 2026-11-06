-- Prove2me | solution 1 for OAI.PowerExtraction.dyadic_prime_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:25:20.493269+00:00
-- url     : https://prove2.me/submissions/d7938f33-8ac8-4b33-b501-6e694f8f84c9

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization

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
theorem _root_.solution (D N : ℕ) (hD : 1 ≤ D)
    (hN : (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤ (N : ℝ)) :
    ((64 * (D / N + 1) : ℕ) : ℝ) ≤
      192 * (D : ℝ) ^ (49 / 60 : ℝ) := by
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hYpos : 0 < (D : ℝ) ^ (11 / 60 : ℝ) :=
    Real.rpow_pos_of_pos hDpos _
  have hNpos : (0 : ℝ) < N := by linarith
  have hpow :
      (D : ℝ) ^ (49 / 60 : ℝ) *
        (D : ℝ) ^ (11 / 60 : ℝ) = D := by
    rw [← Real.rpow_add hDpos]
    norm_num
  have hfrac : (D : ℝ) / N ≤
      2 * (D : ℝ) ^ (49 / 60 : ℝ) := by
    apply (div_le_iff₀ hNpos).mpr
    calc
      (D : ℝ) =
          (D : ℝ) ^ (49 / 60 : ℝ) *
            (D : ℝ) ^ (11 / 60 : ℝ) := hpow.symm
      _ =
          (2 * (D : ℝ) ^ (49 / 60 : ℝ)) *
            ((D : ℝ) ^ (11 / 60 : ℝ) / 2) := by
              ring
      _ ≤ (2 * (D : ℝ) ^ (49 / 60 : ℝ)) * N :=
          mul_le_mul_of_nonneg_left hN (by positivity)
  have hcast : ((D / N : ℕ) : ℝ) ≤ (D : ℝ) / N :=
    Nat.cast_div_le
  have hone : (1 : ℝ) ≤ (D : ℝ) ^ (49 / 60 : ℝ) :=
    Real.one_le_rpow hDreal (by norm_num)
  have hnatcast : ((64 * (D / N + 1) : ℕ) : ℝ) =
      64 * (((D / N : ℕ) : ℝ) + 1) := by push_cast; ring
  rw [hnatcast]
  nlinarith
end OAI.PowerExtraction
