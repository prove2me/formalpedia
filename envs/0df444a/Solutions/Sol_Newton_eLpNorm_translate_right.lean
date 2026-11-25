-- Prove2me | solution 1 for Newton.eLpNorm_translate_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:09:59.651136+00:00
-- url     : https://prove2.me/submissions/3f9cfc70-d4d1-435f-857b-0c3ad8a2210a

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.MetricSpace.Holder
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
import Definitions.Def_Newton_Analysis_Convolution_Auxiliary

set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    {G : Type*} [AddCommGroup G] [MeasurableSpace G] [TopologicalSpace G]
    [MeasurableAdd₂ G]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (f : G → ℂ) (p : ℝ≥0∞) (a : G)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => f (x - a)) p μ = eLpNorm f p μ := by
  -- Use the general lemma `eLpNorm_comp_measurePreserving` with the translation map.
  have hmp : MeasurePreserving (fun x : G => x - a) μ μ := by
    -- `fun x => x - a` is right addition by `-a`.
    simpa [sub_eq_add_neg] using
      measurePreserving_add_right (μ := μ) (-a)
  -- Apply the composition lemma.
  simpa [Function.comp_def, sub_eq_add_neg] using
    (MeasureTheory.eLpNorm_comp_measurePreserving (μ := μ) (ν := μ)
      (g := f) (p := p) hf hmp)
end Newton
