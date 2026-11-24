-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_restricted_cdf_laplace_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:35:07.255558+00:00
-- url     : https://prove2.me/submissions/6ddcab61-b57a-446e-a247-a6436423765d

import Theorems.Thm_AvramDividend_Classical_positiveLIntegral_exp_neg_mul_Ioi
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
/-- Truncated cumulative Laplace calculation. -/
theorem solution :
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (φ b : ℝ), 0 < φ → 0 ≤ b →
      (∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-φ*t)) *
        (ν.restrict (Iic b)) (Iic t)) =
      (∫⁻ t in Ioc 0 b, ENNReal.ofReal (Real.exp (-φ*t)) * ν (Iic t)) +
        ENNReal.ofReal (Real.exp (-φ*b) / φ) * ν (Iic b) := by
  intro ν hν φ b hφ hb
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-φ*t))
  let β := ν.restrict (Iic b)
  have hs : Ioc (0 : ℝ) b ∪ Ioi b = Ioi 0 := Ioc_union_Ioi_eq_Ioi hb
  have hd : Disjoint (Ioc (0 : ℝ) b) (Ioi b) := by
    exact Set.disjoint_left.mpr (fun t ht hu => not_lt_of_ge ht.2 hu)
  change (∫⁻ t in Ioi 0, w t * β (Iic t)) = _
  rw [← hs, Measure.restrict_union hd measurableSet_Ioi, lintegral_add_measure]
  have hleft : (∫⁻ t in Ioc 0 b, w t * β (Iic t)) =
      ∫⁻ t in Ioc 0 b, w t * ν (Iic t) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Measure.restrict_apply measurableSet_Iic,
      Set.inter_eq_left.mpr (Iic_subset_Iic.mpr ht.2)]
  have hright : (∫⁻ t in Ioi b, w t * β (Iic t)) =
      ENNReal.ofReal (Real.exp (-φ*b) / φ) * ν (Iic b) := by
    calc
      _ = ∫⁻ t in Ioi b, w t * ν (Iic b) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [Measure.restrict_apply measurableSet_Iic,
          Set.inter_eq_right.mpr (Iic_subset_Iic.mpr ht.le)]
      _ = _ := by
        rw [lintegral_mul_const _ (by dsimp [w]; fun_prop)]
        exact congrArg (fun z => z * ν (Iic b))
          (AvramDividend.Classical.positiveLIntegral_exp_neg_mul_Ioi φ b hφ)
  rw [hleft, hright]
