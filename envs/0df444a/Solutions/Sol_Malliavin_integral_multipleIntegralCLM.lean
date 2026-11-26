-- Prove2me | solution 1 for Malliavin.integral_multipleIntegralCLM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:12.06898+00:00
-- url     : https://prove2.me/submissions/d6b6ab3c-c016-43ec-9fea-2e1b2dc0c7af

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
import Theorems.Thm_Malliavin_multipleIntegralCLM_apply
import Theorems.Thm_Malliavin_integral_iteratedIntegralCLM


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) {n : ℕ} (hn : 0 < n)
    (f : IteratedKernel n) :
    ∫ ω, multipleIntegralCLM hB n f ω ∂P = 0 := by
  let sf := symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f
  have hcoe : (fun ω => multipleIntegralCLM hB n f ω) =ᵐ[P]
      fun ω => (n.factorial : ℝ) * iteratedIntegralCLM hB n sf ω := by
    change (⇑(multipleIntegralCLM hB n f) : Ω → ℝ) =ᵐ[P]
      (n.factorial : ℝ) • ⇑(iteratedIntegralCLM hB n sf)
    rw [multipleIntegralCLM_apply]
    exact Lp.coeFn_smul (n.factorial : ℝ) (iteratedIntegralCLM hB n sf)
  calc
    (∫ ω, multipleIntegralCLM hB n f ω ∂P) =
        ∫ ω, (n.factorial : ℝ) * iteratedIntegralCLM hB n sf ω ∂P :=
      integral_congr_ae hcoe
    _ = (n.factorial : ℝ) * ∫ ω, iteratedIntegralCLM hB n sf ω ∂P :=
      integral_const_mul _ _
    _ = 0 := by rw [integral_iteratedIntegralCLM hB hn sf, mul_zero]
end Malliavin
