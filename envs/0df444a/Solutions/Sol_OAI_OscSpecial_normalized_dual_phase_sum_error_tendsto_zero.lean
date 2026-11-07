-- Prove2me | solution 1 for OAI.OscSpecial.normalized_dual_phase_sum_error_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:32:36.825534+00:00
-- url     : https://prove2.me/submissions/f792a734-560b-449b-90cf-b18d43541f05

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Theorems.Thm_OAI_OscSpecial_normalized_dual_phase_sum_error
import Theorems.Thm_OAI_GaussianMoment_scaled_moment_vanishes_const
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
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
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace OscSpecial
open scoped Topology
open Filter
private theorem dual_moment_reindex (t : ℝ) :
    (∑' z : ℤ × ℤ, dualQ z * dualRealGauss t z) =
      ∑' z : ℤ × ℤ,
        RankTwoPoisson.eisQ z * GaussianMoment.realGauss t z := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  calc
    (∑' z : ℤ × ℤ, dualQ z * dualRealGauss t z) =
        ∑' z : ℤ × ℤ,
          RankTwoPoisson.eisQ (e z) * GaussianMoment.realGauss t (e z) := by
      apply tsum_congr
      intro z
      have hQ : RankTwoPoisson.eisQ (e z) = dualQ z := by
        rcases z with ⟨k,l⟩
        change (k : ℝ) ^ 2 - (k : ℝ) * ((-l : ℤ) : ℝ) +
          ((-l : ℤ) : ℝ) ^ 2 =
          (k : ℝ) ^ 2 + (k : ℝ) * (l : ℝ) + (l : ℝ) ^ 2
        push_cast
        ring
      simp only [GaussianMoment.realGauss, dualRealGauss, hQ]
    _ = ∑' z : ℤ × ℤ,
          RankTwoPoisson.eisQ z * GaussianMoment.realGauss t z :=
      e.tsum_eq (fun z : ℤ × ℤ =>
        RankTwoPoisson.eisQ z * GaussianMoment.realGauss t z)
end OscSpecial
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT
end ActualEisensteinCubic
open Filter
open scoped Topology
namespace ActualEisensteinCubic
section
open EisensteinEmbedding ConcreteTraceCRT Complex
end
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
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
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open OAI.OscSpecial
open scoped Topology
open Filter
namespace OAI.OscSpecial
theorem _root_.solution {a b : ℝ}
    (hq : 0 < q a b) :
    Tendsto
      (fun η : ℝ =>
        η * ‖(∑' z : ℤ × ℤ, dualVarTerm η a b z) -
          (∑' z : ℤ × ℤ, dualFixedTerm η a b z)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  let K : ℝ := q a b / 8
  have hK : 0 < K := by dsimp [K]; positivity
  have hmoment :
      Tendsto
        (fun η : ℝ => η ^ 3 *
          (∑' z : ℤ × ℤ,
            dualQ z * dualRealGauss (η * q a b / 8) z))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    convert GaussianMoment.scaled_moment_vanishes_const K hK using 1
    funext η
    dsimp [K]
    rw [dual_moment_reindex]
    ring_nf
  have hright :
      Tendsto
        (fun η : ℝ => phaseErrorConstant a b * η ^ 3 *
          (∑' z : ℤ × ℤ,
            dualQ z * dualRealGauss (η * q a b / 8) z))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    convert hmoment.const_mul (phaseErrorConstant a b) using 1
    · funext η
      ring
    · simp
  have hr_lim : Tendsto (fun η : ℝ => r η a b)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hc : ContinuousAt (fun η : ℝ => r η a b) 0 := by
      unfold r
      fun_prop
    simpa [r] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hrle : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), r η a b ≤ 2 := by
    have hevent : ∀ᶠ x : ℝ in 𝓝 (1 : ℝ), x ≤ 2 :=
      eventually_le_nhds (by norm_num)
    exact hr_lim.eventually hevent
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) hright
  · filter_upwards [self_mem_nhdsWithin] with η hη
    exact mul_nonneg hη.le (norm_nonneg _)
  · filter_upwards [self_mem_nhdsWithin, hrle] with η hη hbound
    exact normalized_dual_phase_sum_error hη hq hbound
end OAI.OscSpecial
