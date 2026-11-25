-- Prove2me | solution 1 for Newton.convolution_kernel_aestronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:34:06.300973+00:00
-- url     : https://prove2.me/submissions/3442c797-98d9-4d21-880c-043ffa9a5581

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality
import Definitions.Def_Newton_Analysis_Convolution_Minkowski

set_option autoImplicit false
open MeasureTheory ENNReal NNReal
open scoped ENNReal
open Newton
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E]
variable {G : Type*}
variable [NormedAddCommGroup G] [MeasurableSpace G]
variable [MeasurableAdd₂ G] [MeasurableNeg G]
variable (μ : Measure G) [SFinite μ] [μ.IsAddRightInvariant]
namespace Newton
theorem _root_.solution
    (f g : G → ℂ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ) := by
  have hf_aemeas : AEMeasurable f μ := hf.aemeasurable
  have hg_aemeas : AEMeasurable g μ := hg.aemeasurable
  have h_sub_qmp :
      Measure.QuasiMeasurePreserving (fun q : G × G => q.1 - q.2)
        (μ.prod μ) μ := by
    have h_sub_prod :
        MeasurePreserving (fun q : G × G => (q.1 - q.2, q.2))
          (μ.prod μ) (μ.prod μ) :=
      measurePreserving_sub_prod (μ := μ) (ν := μ)
    have h_fst_qmp :
        Measure.QuasiMeasurePreserving (fun q : G × G => q.1)
          (μ.prod μ) μ :=
      MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)
    exact h_fst_qmp.comp h_sub_prod.quasiMeasurePreserving
  have hf_prod_aemeas :
      AEMeasurable (fun q : G × G => f (q.1 - q.2)) (μ.prod μ) :=
    hf_aemeas.comp_quasiMeasurePreserving h_sub_qmp
  have hg_prod_aemeas :
      AEMeasurable (fun q : G × G => g q.2) (μ.prod μ) :=
    hg_aemeas.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
  have h_mul_aemeas :
      AEMeasurable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ) := by
    exact hf_prod_aemeas.mul hg_prod_aemeas
  exact h_mul_aemeas.aestronglyMeasurable
end Newton
