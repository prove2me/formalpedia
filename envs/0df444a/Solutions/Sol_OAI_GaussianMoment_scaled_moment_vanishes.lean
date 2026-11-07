-- Prove2me | solution 1 for OAI.GaussianMoment.scaled_moment_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:27:52.081293+00:00
-- url     : https://prove2.me/submissions/361c17f9-229c-4b72-8795-039ee765eafa

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Theorems.Thm_OAI_GaussianMoment_realGauss_nonneg
import Theorems.Thm_OAI_GaussianMoment_realGauss_summable
import Theorems.Thm_OAI_GaussianMoment_real_gaussian_mass
import Theorems.Thm_OAI_GaussianMoment_gaussian_moment_term_bound
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_RankTwoPoisson_eisQ_lower
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
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
namespace OscSpecial
end OscSpecial
namespace ActualEisensteinCubic
section
open EisensteinEmbedding ConcreteTraceCRT Complex
end
section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace GaussianMoment
open scoped Topology
open Filter
end GaussianMoment
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace OscSpecial
open scoped Topology
open Filter
end OscSpecial
namespace GaussianMoment
open scoped Topology
open Filter
private theorem eisQ_nonneg (z : ℤ × ℤ) : 0 ≤ RankTwoPoisson.eisQ z := by
  have h := RankTwoPoisson.eisQ_lower z
  nlinarith [sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]
private theorem moment_term_bound {t : ℝ} (ht : 0 < t) (z : ℤ × ℤ) :
    RankTwoPoisson.eisQ z * realGauss t z ≤
      (2 / (Real.pi * t)) * realGauss (t / 2) z := by
  have h := gaussian_moment_term_bound (RankTwoPoisson.eisQ z) (Real.pi * t)
    (eisQ_nonneg z) (mul_pos Real.pi_pos ht)
  convert h using 1 <;> dsimp [realGauss] <;> ring_nf
private theorem moment_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun z : ℤ × ℤ => RankTwoPoisson.eisQ z * realGauss t z) := by
  have hmajor : Summable (fun z : ℤ × ℤ =>
      (2 / (Real.pi * t)) * realGauss (t / 2) z) :=
    (realGauss_summable (t := t / 2) (half_pos ht)).mul_left _
  exact hmajor.of_nonneg_of_le
    (fun z => mul_nonneg (eisQ_nonneg z) (realGauss_nonneg t z))
    (moment_term_bound ht)
private theorem moment_tsum_bound {t : ℝ} (ht : 0 < t) :
    (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z) ≤
      (2 / (Real.pi * t)) *
        (∑' z : ℤ × ℤ, realGauss (t / 2) z) := by
  have hmajor : Summable (fun z : ℤ × ℤ =>
      (2 / (Real.pi * t)) * realGauss (t / 2) z) :=
    (realGauss_summable (t := t / 2) (half_pos ht)).mul_left _
  have h := Summable.tsum_le_tsum (moment_term_bound ht)
    (moment_summable ht) hmajor
  simpa only [tsum_mul_left] using h
private theorem moment_tsum_nonneg (t : ℝ) :
    0 ≤ (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z) := by
  exact tsum_nonneg fun z => mul_nonneg (eisQ_nonneg z) (realGauss_nonneg t z)
private theorem half_tendsto_within :
    Tendsto (fun t : ℝ => t / 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun t : ℝ => t / 2) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact half_pos ht
private theorem t_tendsto_zero :
    Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
  tendsto_id.mono_left nhdsWithin_le_nhds
private theorem scaled_half_mass_tendsto :
    Tendsto
      (fun t : ℝ => (t / 2) *
        (∑' z : ℤ × ℤ, realGauss (t / 2) z))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 / Real.sqrt 3)) := by
  simpa only [Function.comp_def] using real_gaussian_mass.comp half_tendsto_within
end GaussianMoment
end
end OAI
end

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
open OAI.GaussianMoment
open scoped Topology
open Filter
namespace OAI.GaussianMoment
theorem _root_.solution :
    Tendsto
      (fun t : ℝ => t ^ 3 *
        (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hright : Tendsto
      (fun t : ℝ => (4 / Real.pi) * t *
        ((t / 2) * (∑' z : ℤ × ℤ, realGauss (t / 2) z)))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := (t_tendsto_zero.mul scaled_half_mass_tendsto).const_mul (4 / Real.pi)
    simpa only [zero_mul, mul_zero, Function.comp_def, mul_assoc] using h
  have hleft : Tendsto (fun _ : ℝ => (0 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact mul_nonneg (pow_nonneg ht.le _) (moment_tsum_nonneg t)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    have h := moment_tsum_bound ht
    have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht.le _
    have hmul := mul_le_mul_of_nonneg_left h ht3
    calc
      t ^ 3 * (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z) ≤
          t ^ 3 * ((2 / (Real.pi * t)) *
            (∑' z : ℤ × ℤ, realGauss (t / 2) z)) := hmul
      _ = (4 / Real.pi) * t *
          ((t / 2) * (∑' z : ℤ × ℤ, realGauss (t / 2) z)) := by
        field_simp [ht.ne']
        ring
end OAI.GaussianMoment
