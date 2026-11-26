-- Prove2me | solution 1 for IsLowerSemianalytic.analyticSet_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:06:06.373902+00:00
-- url     : https://prove2.me/submissions/72f18dbb-3128-4f33-8cb3-114331d18310

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LowerSemianalytic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Theorems.Thm_ennreal_le_iff_forall_lt_add_inv

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
    {f : X × Y → ℝ≥0∞} (hf : IsLowerSemianalytic (X := X × Y) f)
    {q : ℝ≥0∞} (hq : q ≠ ∞) :
    AnalyticSet {p : X × Y | f p ≤ q} := by
  have heq : {p : X × Y | f p ≤ q}
      = ⋂ k : ℕ, {p | f p < q + ((k : ℝ≥0∞) + 1)⁻¹} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter]
    exact ennreal_le_iff_forall_lt_add_inv hq
  rw [heq]
  exact AnalyticSet.iInter fun k => hf _
end IsLowerSemianalytic
