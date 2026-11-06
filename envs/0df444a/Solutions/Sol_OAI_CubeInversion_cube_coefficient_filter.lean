-- Prove2me | solution 1 for OAI.CubeInversion.cube_coefficient_filter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:14:27.230864+00:00
-- url     : https://prove2.me/submissions/6d71aa06-92a4-43af-bfb4-7198a3281ea5

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Theorems.Thm_OAI_CubeInversion_cube_index_filter_complex
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
open OAI.CubeInversion
namespace OAI.CubeInversion
theorem _root_.solution
    (m : ℕ) (c W : ℕ → ℂ)
    (hc : ∀ a b, c (a * b) = c a * c b) :
    (∑ h ∈ m.divisors,
      (ArithmeticFunction.moebius h : ℂ) * c h * c (m / h) * W m) =
      if m = 1 then c m * W m else 0 := by
  have heq (h : ℕ) (hh : h ∈ m.divisors) :
      c h * c (m / h) = c m := by
    rw [← hc]
    congr 1
    exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hh)
  calc
    (∑ h ∈ m.divisors,
      (ArithmeticFunction.moebius h : ℂ) * c h * c (m / h) * W m) =
      (∑ h ∈ m.divisors,
        (ArithmeticFunction.moebius h : ℂ)) * (c m * W m) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro h hh
        calc
          (ArithmeticFunction.moebius h : ℂ) * c h * c (m / h) * W m =
              (ArithmeticFunction.moebius h : ℂ) * (c h * c (m / h)) * W m := by ring
          _ = (ArithmeticFunction.moebius h : ℂ) * (c m * W m) := by
              rw [heq h hh]
              ring
    _ = if m = 1 then c m * W m else 0 := by
      rw [cube_index_filter_complex]
      split_ifs <;> simp
end OAI.CubeInversion
