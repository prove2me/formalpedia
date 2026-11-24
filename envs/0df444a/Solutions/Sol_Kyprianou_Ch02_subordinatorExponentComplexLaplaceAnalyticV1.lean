-- Prove2me | solution 1 for Kyprianou.Ch02.subordinatorExponentComplexLaplaceAnalyticV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:50:50.769016+00:00
-- url     : https://prove2.me/submissions/348dcec3-40d0-4eb8-8bce-9f4a53e9776e

import Theorems.Thm_Kyprianou_Ch02_positiveLaplaceIntegralDiffContOnClV1
import Theorems.Thm_Kyprianou_Ch02_positiveLaplaceIntegralRealNonnegV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (ν.restrict (Set.Ioi (0 : ℝ)))) (d : ℝ) (hd : 0 ≤ d) (t : ℝ≥0) :
    let Ξ : ℂ → ℂ := fun z =>
      (d : ℂ) * z +
      ∫ x in Set.Ioi (0 : ℝ), (1 - Complex.exp (-z * (x : ℂ))) ∂ν
    DiffContOnCl ℂ (fun z => Complex.exp (-(((t : ℝ) : ℂ)) * Ξ z))
      {z : ℂ | 0 < z.re} ∧
    ∀ z : ℂ, 0 ≤ z.re → ‖Complex.exp (-(((t : ℝ) : ℂ)) * Ξ z)‖ ≤ 1 := by
  dsimp
  let J : ℂ → ℂ := fun z => ∫ x in Set.Ioi (0 : ℝ), (1 - Complex.exp (-z * (x : ℂ))) ∂ν
  let A : ℂ → ℂ := fun z => (d : ℂ) * z + J z
  have hJ := Kyprianou.Ch02.positiveLaplaceIntegralDiffContOnClV1 ν hint
  have hA : DiffContOnCl ℂ A {z : ℂ | 0 < z.re} :=
    ((show Differentiable ℂ (fun z : ℂ => (d : ℂ) * z) by fun_prop).diffContOnCl).add hJ
  constructor
  · exact (show Differentiable ℂ (fun w : ℂ => Complex.exp (-(((t : ℝ) : ℂ)) * w)) by
      fun_prop).comp_diffContOnCl hA
  · intro z hz
    have hJre := Kyprianou.Ch02.positiveLaplaceIntegralRealNonnegV1 ν hint z hz
    have hAre : 0 ≤ (A z).re := by
      dsimp [A,J]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      exact add_nonneg (mul_nonneg hd hz) hJre
    rw [Complex.norm_exp, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    change (-(((t : ℝ) : ℂ)) * A z).re ≤ 0
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact neg_nonpos.mpr (mul_nonneg t.coe_nonneg hAre)
