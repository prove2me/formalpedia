-- Prove2me | solution 1 for OAI.RationalPrimeExtraction.selected_rows_in_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:27:42.89352+00:00
-- url     : https://prove2.me/submissions/f24547b9-f087-4a10-b0bb-e100e9f16aee

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Theorems.Thm_OAI_ActualEisensteinCubic_rational_qNat_pow
import Theorems.Thm_OAI_ShortDraftLatticeCount_mem_rowNormBall_of_qNat_le


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
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open OAI.RationalPrimeExtraction
namespace OAI.RationalPrimeExtraction
theorem _root_.solution [DecidableEq O] (D : ℕ) (hD : 1 ≤ D) :
    (selected ((D : ℝ) ^ (4 / 45 : ℝ))).image
      (fun r : ℕ => (r : O) ^ 6) ⊆
      rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊ := by
  classical
  intro u hu
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hu
  have hrI : r ∈ Finset.Ioc
      ⌊(D : ℝ) ^ (4 / 45 : ℝ) / 3⌋₊
      ⌊(D : ℝ) ^ (4 / 45 : ℝ)⌋₊ :=
    (Finset.mem_filter.mp hr).1
  have hrprime : r.Prime := (Finset.mem_filter.mp hr).2
  have hrupper : r ≤ ⌊(D : ℝ) ^ (4 / 45 : ℝ)⌋₊ :=
    (Finset.mem_Ioc.mp hrI).2
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hYpos : 0 ≤ (D : ℝ) ^ (4 / 45 : ℝ) :=
    Real.rpow_nonneg hDpos.le _
  have hrupperCast : (r : ℝ) ≤
      (⌊(D : ℝ) ^ (4 / 45 : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast hrupper
  have hrupperReal : (r : ℝ) ≤ (D : ℝ) ^ (4 / 45 : ℝ) :=
    hrupperCast.trans (Nat.floor_le hYpos)
  have hnorm : qNat ((r : O) ^ 6) = r ^ 12 := by
    rw [rational_qNat_pow r 6 hrprime.ne_zero]
    ring
  have hpow : (r : ℝ) ^ 12 ≤
      ((D : ℝ) ^ (4 / 45 : ℝ)) ^ 12 := by gcongr
  have hYpow : ((D : ℝ) ^ (4 / 45 : ℝ)) ^ 12 =
      (D : ℝ) ^ (16 / 15 : ℝ) := by
    calc
      ((D : ℝ) ^ (4 / 45 : ℝ)) ^ 12 =
          (D : ℝ) ^ ((4 / 45 : ℝ) * (12 : ℕ)) :=
          (Real.rpow_mul_natCast hDpos.le _ 12).symm
      _ = (D : ℝ) ^ (16 / 15 : ℝ) := by congr 1; norm_num
  have hnormreal : (qNat ((r : O) ^ 6) : ℝ) ≤
      (⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊ : ℝ) := by
    rw [hnorm]
    exact (by exact_mod_cast hpow :
      ((r ^ 12 : ℕ) : ℝ) ≤ ((D : ℝ) ^ (4 / 45 : ℝ)) ^ 12).trans
        (hYpow.le.trans (Nat.le_ceil _))
  exact mem_rowNormBall_of_qNat_le _ _ (by exact_mod_cast hnormreal)
end OAI.RationalPrimeExtraction
