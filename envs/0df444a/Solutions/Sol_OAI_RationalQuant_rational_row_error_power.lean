-- Prove2me | solution 1 for OAI.RationalQuant.rational_row_error_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:27:29.605172+00:00
-- url     : https://prove2.me/submissions/18baeafc-37fb-4110-88cb-69f665a1e4f9

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
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
open ActualEisensteinCubic
open Filter
open OAI.RationalQuant
namespace OAI.RationalQuant
theorem _root_.solution
    (D r : ℕ) (hD : 1 ≤ D)
    (hrlo : (D : ℝ) ^ (4 / 45 : ℝ) / 3 < (r : ℝ)) :
    ((128 * (D / r + 1) : ℕ) : ℝ) ≤
      512 * (D : ℝ) ^ (41 / 45 : ℝ) := by
  let X : ℝ := (D : ℝ) ^ (4 / 45 : ℝ)
  let P : ℝ := (D : ℝ) ^ (41 / 45 : ℝ)
  let q : ℝ := (D / r : ℕ)
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hXpos : 0 < X := Real.rpow_pos_of_pos hDpos _
  have hqnonneg : 0 ≤ q := by positivity
  have hP1 : 1 ≤ P := by
    calc
      1 = (D : ℝ) ^ (0 : ℝ) := by simp
      _ ≤ (D : ℝ) ^ (41 / 45 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hDreal (by norm_num)
  have hDP : (D : ℝ) = X * P := by
    dsimp [X, P]
    rw [← Real.rpow_add hDpos]
    norm_num
  have hdivnat : D / r * r ≤ D := Nat.div_mul_le_self D r
  have hdivreal : q * (r : ℝ) ≤ (D : ℝ) := by
    change ((D / r : ℕ) : ℝ) * (r : ℝ) ≤ (D : ℝ)
    exact_mod_cast hdivnat
  have hXr : X ≤ 3 * (r : ℝ) := by
    dsimp [X] at hrlo ⊢
    linarith
  have hXq : X * q ≤ 3 * (D : ℝ) := by
    calc
      X * q ≤ (3 * (r : ℝ)) * q :=
        mul_le_mul_of_nonneg_right hXr hqnonneg
      _ ≤ 3 * (D : ℝ) := by nlinarith [hdivreal]
  have hq : q ≤ 3 * P := by
    apply le_of_mul_le_mul_left (a := X) ?_ hXpos
    calc
      X * q ≤ 3 * (D : ℝ) := hXq
      _ = X * (3 * P) := by rw [hDP]; ring
  have hfinal : (128 : ℝ) * (q + 1) ≤ 512 * P := by
    nlinarith [hq, hP1]
  simpa [q, P] using hfinal
end OAI.RationalQuant
