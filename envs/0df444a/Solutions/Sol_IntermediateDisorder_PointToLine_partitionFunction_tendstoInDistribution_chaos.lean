-- Prove2me | solution 1 for IntermediateDisorder.PointToLine.partitionFunction_tendstoInDistribution_chaos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T17:24:36.793193+00:00
-- url     : https://prove2.me/submissions/4283685a-f7c0-4ed8-b893-07bf21dc6e96

import Mathlib
import Definitions.Def_IntermediateDisorder_PointToLine_Environment
import Definitions.Def_IntermediateDisorder_PointToLine_WienerChaos
import Theorems.Thm_IntermediateDisorder_PointToLine_modifiedPartitionFunction_tendstoInDistribution_chaos
import Theorems.Thm_IntermediateDisorder_PointToLine_partitionFunction_sub_modified_eLpNorm_tendsto_zero

set_option autoImplicit false

namespace P65ecb5d3
open MeasureTheory ProbabilityTheory Filter Topology IntermediateDisorder.PointToLine

lemma measurable_partitionFunction {Ω : Type*} [MeasurableSpace Ω] {ω : ℕ × ℤ → Ω → ℝ}
    (hm : ∀ p, Measurable (ω p)) (n : ℕ) (b : ℝ) : Measurable (partitionFunction ω n b) := by
  unfold partitionFunction energy
  refine Measurable.const_mul (Finset.measurable_sum _ (fun s _ => ?_)) _
  exact (Measurable.const_mul (Finset.measurable_sum _ (fun m _ => hm _)) b).exp

lemma measurable_modifiedPartitionFunction {Ω : Type*} [MeasurableSpace Ω]
    {ω : ℕ × ℤ → Ω → ℝ} (hm : ∀ p, Measurable (ω p)) (n : ℕ) (b : ℝ) :
    Measurable (modifiedPartitionFunction ω n b) := by
  unfold modifiedPartitionFunction
  refine Measurable.const_mul (Finset.measurable_sum _ (fun s _ => ?_)) _
  exact Finset.measurable_prod _ (fun m _ => measurable_const.add ((hm _).const_mul b))

end P65ecb5d3

open MeasureTheory ProbabilityTheory Filter IntermediateDisorder.PointToLine P65ecb5d3 in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ}
    (hω : IsStdEnvironment ω Q)
    (hexp : ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ b : ℝ, 0 < b → b < β₀ →
      Integrable (fun a => Real.exp (b * ω (1, 0) a)) Q)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'} [IsProbabilityMeasure Q']
    (W : Set (ℝ × ℝ) → Ω' → ℝ) (I : (k : ℕ) → Lp ℝ 2 (kernelMeasure k) →L[ℝ] Lp ℝ 2 Q')
    (hW : IsWhiteNoise W Q') (hI : IsMultipleIntegral W Q' I) (β : ℝ) (hβ : 0 < β) :
    TendstoInDistribution
      (fun (n : ℕ) a => Real.exp (-(n : ℝ) * cgf (ω (1, 0)) Q (β * (n : ℝ) ^ (-(1 / 4 : ℝ)))) *
        partitionFunction ω n (β * (n : ℝ) ^ (-(1 / 4 : ℝ))) a)
      atTop (wienerChaos I (Real.sqrt 2 * β)) (fun _ => Q) Q' := by
  have hX := modifiedPartitionFunction_tendstoInDistribution_chaos hω W I hW hI β hβ
  have hL2 := partitionFunction_sub_modified_eLpNorm_tendsto_zero hω hexp β hβ
  have hY : ∀ n : ℕ, Measurable (fun a =>
      Real.exp (-(n : ℝ) * cgf (ω (1, 0)) Q (β * (n : ℝ) ^ (-(1 / 4 : ℝ)))) *
        partitionFunction ω n (β * (n : ℝ) ^ (-(1 / 4 : ℝ))) a) := fun n =>
    (measurable_partitionFunction hω.measurable n _).const_mul _
  have hZ : ∀ n : ℕ, Measurable (modifiedPartitionFunction ω n (β * (n : ℝ) ^ (-(1 / 4 : ℝ)))) :=
    fun n => measurable_modifiedPartitionFunction hω.measurable n _
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hX ?_ (fun n => (hY n).aemeasurable)
  refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero
    (fun n => ((hY n).sub (hZ n)).aestronglyMeasurable) aestronglyMeasurable_const ?_
  simpa [Pi.sub_def] using hL2
