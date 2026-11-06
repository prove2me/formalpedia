-- Prove2me | solution 1 for OAI.EisensteinAbelFiber.shifted_gaussian_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:50:41.497669+00:00
-- url     : https://prove2.me/submissions/b6ec46a9-e38e-489d-b5cb-5caa5ab3cbf5

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Theorems.Thm_OAI_EisensteinGaussianPrefactor_complex_eta_times_prefactor
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_RankTwoEisShift_shifted_eisenstein_gaussian_poisson
import Theorems.Thm_OAI_RankTwoLimit_dual_sum_tendsto_one_small_t
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
open OAI.EisensteinAbelFiber
open scoped Topology
open Filter
namespace OAI.EisensteinAbelFiber
theorem _root_.solution (x y : ℝ) :
    Tendsto (fun t : ℝ => (t : ℂ) *
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t x y z))
      (𝓝[>] (0 : ℝ)) (𝓝 (((2 / Real.sqrt 3 : ℝ) : ℂ))) := by
  have hpoint (t : ℝ) (ht : 0 < t) :
      (t : ℂ) * (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t x y z) =
        ((2 / Real.sqrt 3 : ℝ) : ℂ) *
          (∑' z : ℤ × ℤ, RankTwoLimit.dualTerm (4 / (3 * t)) x y z) := by
    rw [RankTwoEisShift.shifted_eisenstein_gaussian_poisson ht x y]
    have hpre := EisensteinGaussianPrefactor.complex_eta_times_prefactor
      t 1 ht (by norm_num)
    simp only [mul_one] at hpre
    change (t : ℂ) *
        ((1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / (((3 * t / 4 : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
          (∑' z : ℤ × ℤ,
            RankTwoLimit.dualTerm (4 / (3 * t)) x y z)) = _
    calc
      (t : ℂ) * ((1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / (((3 * t / 4 : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
          (∑' z : ℤ × ℤ,
            RankTwoLimit.dualTerm (4 / (3 * t)) x y z)) =
        (((t : ℂ) * (1 / (t : ℂ) ^ (1 / 2 : ℂ))) *
          (1 / (((3 * t / 4 : ℝ) : ℂ) ^ (1 / 2 : ℂ)))) *
          (∑' z : ℤ × ℤ,
            RankTwoLimit.dualTerm (4 / (3 * t)) x y z) := by ring
      _ = _ := by rw [hpre]
  have hlim := (RankTwoLimit.dual_sum_tendsto_one_small_t x y).const_mul
    (((2 / Real.sqrt 3 : ℝ) : ℂ))
  have heq : (fun t : ℝ => (t : ℂ) *
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t x y z)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ((2 / Real.sqrt 3 : ℝ) : ℂ) *
        (∑' z : ℤ × ℤ, RankTwoLimit.dualTerm (4 / (3 * t)) x y z)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hpoint t ht
  simpa using hlim.congr' heq.symm
end OAI.EisensteinAbelFiber
