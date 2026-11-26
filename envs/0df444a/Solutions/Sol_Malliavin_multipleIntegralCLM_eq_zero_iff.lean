-- Prove2me | solution 1 for Malliavin.multipleIntegralCLM_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:07:48.037502+00:00
-- url     : https://prove2.me/submissions/8848e4aa-c2dc-4fe3-93b5-a3e5ae8f0d83

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
import Theorems.Thm_Malliavin_multipleIntegralCLM_symmetrize
import Theorems.Thm_Malliavin_norm_sq_multipleIntegralCLM

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    multipleIntegralCLM hB n f = 0 ↔
      symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f = 0 := by
  constructor
  · intro hI
    have hnorm := norm_sq_multipleIntegralCLM hB n f
    rw [hI, norm_zero, zero_pow (by decide)] at hnorm
    have hprod : (n.factorial : ℝ) *
        ‖symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f‖ ^ 2 = 0 := hnorm.symm
    rcases mul_eq_zero.mp hprod with hfac | hsq
    · exact absurd hfac (by exact_mod_cast n.factorial_ne_zero)
    · exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · intro hs
    rw [← multipleIntegralCLM_symmetrize hB n f, hs, map_zero]
end Malliavin
