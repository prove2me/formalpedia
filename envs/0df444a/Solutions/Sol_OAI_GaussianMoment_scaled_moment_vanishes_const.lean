-- Prove2me | solution 1 for OAI.GaussianMoment.scaled_moment_vanishes_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:29:25.84847+00:00
-- url     : https://prove2.me/submissions/a82589f8-b061-44b0-ac37-6fba179fb426

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Theorems.Thm_OAI_GaussianMoment_scaled_moment_vanishes
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
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open OAI.GaussianMoment
open scoped Topology
open Filter
namespace OAI.GaussianMoment
theorem _root_.solution (K : ℝ) (hK : 0 < K) :
    Tendsto
      (fun η : ℝ => η ^ 3 *
        (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss (K * η) z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hscale : Tendsto (fun η : ℝ => K * η)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun η : ℝ => K * η) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with η hη
      change 0 < η at hη
      exact mul_pos hK hη
  have h := scaled_moment_vanishes.comp hscale
  have h' := h.const_mul (1 / K ^ 3)
  convert h' using 1
  · funext η
    dsimp [Function.comp_def]
    field_simp [hK.ne']
  · simp
end OAI.GaussianMoment
