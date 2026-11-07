-- Prove2me | solution 1 for OAI.RationalQuant.scale_large_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:27:42.300194+00:00
-- url     : https://prove2.me/submissions/634d6eeb-c915-4b98-9b9f-640ab54bf7a5

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
theorem _root_.solution (Y₀ : ℝ) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
      2 ≤ D ∧ Y₀ ≤ D ^ (4 / 45 : ℝ) := by
  let M : ℝ := max 1 Y₀
  refine ⟨max 2 (M ^ (45 / 4 : ℝ)), ?_⟩
  intro D hD
  have hD2 : 2 ≤ D := (le_max_left _ _).trans hD
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_max_left _ _)
  have hpowle : M ^ (45 / 4 : ℝ) ≤ D :=
    (le_max_right _ _).trans hD
  have hroot : M ≤ D ^ (4 / 45 : ℝ) := by
    calc
      M = (M ^ (45 / 4 : ℝ)) ^ (4 / 45 : ℝ) := by
        rw [← Real.rpow_mul hMpos.le]
        have hmul : (45 / 4 : ℝ) * (4 / 45 : ℝ) = 1 := by norm_num
        rw [hmul]
        simp
      _ ≤ D ^ (4 / 45 : ℝ) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hMpos.le _) hpowle (by norm_num)
  exact ⟨hD2, (le_max_right _ _).trans hroot⟩
end OAI.RationalQuant
