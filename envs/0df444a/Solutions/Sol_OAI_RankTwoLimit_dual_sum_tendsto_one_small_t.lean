-- Prove2me | solution 1 for OAI.RankTwoLimit.dual_sum_tendsto_one_small_t
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:48:43.018479+00:00
-- url     : https://prove2.me/submissions/b8cacaff-099d-474e-834f-b88d3ef07913

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Theorems.Thm_OAI_RankTwoLimit_dual_sum_tendsto_one
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
open OAI.RankTwoLimit
open scoped Topology
open Filter
namespace OAI.RankTwoLimit
theorem _root_.solution (x y : ℝ) :
    Tendsto (fun t : ℝ => ∑' z : ℤ × ℤ, dualTerm (4 / (3 * t)) x y z)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
  have hT : Tendsto (fun t : ℝ => (4 / 3 : ℝ) * t⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 4 / 3)).2
      tendsto_inv_nhdsGT_zero
  have h := (dual_sum_tendsto_one x y).comp hT
  simpa [Function.comp_def, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h
end OAI.RankTwoLimit
