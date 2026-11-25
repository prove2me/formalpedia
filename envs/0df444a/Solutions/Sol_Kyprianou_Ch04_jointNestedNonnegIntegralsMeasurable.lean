-- Prove2me | solution 1 for Kyprianou.Ch04.jointNestedNonnegIntegralsMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:20:42.813877+00:00
-- url     : https://prove2.me/submissions/3e85e7c8-4f76-4f00-b81c-429768709951

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
open Kyprianou.Ch04

/-- Reassociate the three variables and apply the measurable parameter integral theorem twice, for both extended and Bochner integrals. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (mu nu : Measure Real) [SigmaFinite mu] [SigmaFinite nu]
    (f : Omega × (Real × Real) → Real) (hf : Measurable f) :
    Measurable (fun w => ∫⁻ s, ∫⁻ x, ENNReal.ofReal (f (w,(s,x))) ∂nu ∂mu) ∧
    Measurable (fun w => ∫ s, ∫ x, f (w,(s,x)) ∂nu ∂mu) := by
  let g (p : (Omega × Real) × Real) := f (p.1.1,(p.1.2,p.2))
  have hg : Measurable g := hf.comp
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have h1 : Measurable (fun p : Omega × ℝ => ∫⁻ x,
      ENNReal.ofReal (g (p,x)) ∂nu) :=
    Measurable.lintegral_prod_right (f := fun p x => ENNReal.ofReal (g (p,x)))
      (ENNReal.measurable_ofReal.comp hg)
  have h2 : StronglyMeasurable (fun p : Omega × ℝ => ∫ x, g (p,x) ∂nu) :=
    StronglyMeasurable.integral_prod_right (f := fun p x => g (p,x))
      (show StronglyMeasurable (Function.uncurry (fun p x => g (p,x))) from
        hg.stronglyMeasurable)
  exact ⟨Measurable.lintegral_prod_right
    (f := fun w s => ∫⁻ x, ENNReal.ofReal (g ((w,s),x)) ∂nu) h1,
    (StronglyMeasurable.integral_prod_right
      (f := fun w s => ∫ x, g ((w,s),x) ∂nu) h2).measurable⟩
