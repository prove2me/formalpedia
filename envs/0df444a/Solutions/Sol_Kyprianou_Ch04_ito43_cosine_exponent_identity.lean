-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cosine_exponent_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:37:41.953117+00:00
-- url     : https://prove2.me/submissions/611fec57-53c4-427e-94a1-f4a022c0541a

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
import Theorems.Thm_ProbabilityTheory_levyCompensatedIntegrand_def
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution (tr : ProbabilityTheory.LevyKhintchineTriple) (a : ℝ) (ha : 0 < a) :
    -(Kyprianou.Ch01.levyTripleExponent tr a).re/a^2 =
      (tr.gaussianVariance:ℝ)/2 +
        ∫ z, (1-Real.cos (a*z))/a^2 ∂tr.levyMeasure := by
  have hi := ProbabilityTheory.integrable_levyCompensatedIntegrand tr.levyMeasure_isLevyMeasure a
  have hj (x : ℝ) :
      (ProbabilityTheory.levyCompensatedIntegrand a x).re = Real.cos (a*x)-1 := by
    rw [ProbabilityTheory.levyCompensatedIntegrand_def]
    by_cases hx : |x| < 1 <;>
      simp [hx,Complex.exp_re,Complex.mul_re,Complex.mul_im,Complex.sub_re,mul_comm]
  have hJ : (∫ x, ProbabilityTheory.levyCompensatedIntegrand a x ∂tr.levyMeasure).re =
      ∫ x, Real.cos (a*x)-1 ∂tr.levyMeasure := by
    change RCLike.re (K := ℂ) (∫ x, ProbabilityTheory.levyCompensatedIntegrand a x ∂tr.levyMeasure) = _
    rw [← integral_re hi]
    exact integral_congr_ae (Eventually.of_forall hj)
  have hneg : (∫ x, 1-Real.cos (a*x) ∂tr.levyMeasure) =
      -(∫ x, Real.cos (a*x)-1 ∂tr.levyMeasure) := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [integral_div,hneg]
  unfold Kyprianou.Ch01.levyTripleExponent
  simp [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im,
    Complex.div_re,Complex.normSq,pow_two] at hJ ⊢
  rw [hJ]
  field_simp
  <;> ring
