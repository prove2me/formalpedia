-- Prove2me | solution 1 for IsLowerSemianalytic.analyticSet_epigraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:06:55.009561+00:00
-- url     : https://prove2.me/submissions/3b8f9735-8fa3-4e68-b165-b8da11899d0f

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LowerSemianalytic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Theorems.Thm_P2M_MeasureTheory_AnalyticSet_union__2545ead870ad
import Theorems.Thm_MeasureTheory_AnalyticSet_preimage_of_continuous
import Theorems.Thm_IsLowerSemianalytic_analyticSet_le

set_option autoImplicit false
open Set Topology MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {X Y : Type*}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
namespace IsLowerSemianalytic
theorem _root_.solution
    {f : X × Y → ℝ≥0∞} (hf : IsLowerSemianalytic (X := X × Y) f) :
    AnalyticSet {pb : (X × Y) × ℝ | f pb.1 ≤ ENNReal.ofReal pb.2} := by
  have heq : {pb : (X × Y) × ℝ | f pb.1 ≤ ENNReal.ofReal pb.2}
      = ⋂ q : ℚ,
          ({pb : (X × Y) × ℝ |
              ENNReal.ofReal pb.2 < (Real.toNNReal q : ℝ≥0∞)}ᶜ
            ∪ (Prod.fst ⁻¹' {p : X × Y | f p ≤ (Real.toNNReal q : ℝ≥0∞)})) := by
    ext ⟨p, b⟩
    simp only [mem_iInter, mem_union, mem_compl_iff, mem_ofPred_eq,
      mem_preimage, not_lt]
    constructor
    · intro h q
      rcases le_or_gt (Real.toNNReal q : ℝ≥0∞) (ENNReal.ofReal b) with hle | hlt
      · exact Or.inl hle
      · exact Or.inr (h.trans hlt.le)
    · intro h
      by_contra hcon
      rw [not_le] at hcon
      obtain ⟨q, _, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hcon
      rcases h q with h3 | h3
      · exact absurd h1 (not_lt.mpr h3)
      · exact absurd h2 (not_lt.mpr h3)
  rw [heq]
  refine AnalyticSet.iInter fun q => ?_
  refine AnalyticSet.union' ?_ ?_
  · refine IsClosed.analyticSet ?_
    exact (isOpen_Iio.preimage
      (ENNReal.continuous_ofReal.comp continuous_snd)).isClosed_compl
  · exact (hf.analyticSet_le (by finiteness)).preimage_of_continuous
      continuous_fst
end IsLowerSemianalytic
