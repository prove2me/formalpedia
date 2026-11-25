-- Prove2me | solution 1 for Kyprianou.Ch04.smallMarginalExactFiniteApprox
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T08:26:53.765686+00:00
-- url     : https://prove2.me/submissions/7c854187-ccf0-4076-8ac5-b12a3b581ee1

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch03_momentSmallJumpBandFiniteV1
import Theorems.Thm_Kyprianou_Ch03_momentFiniteBoundedGaussianJumpLawV1
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulSmallJumpExponentBandLimitV1
import Theorems.Thm_FamousTheorems_levy_continuity
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Retain the exact moments of the finite-band approximants. -/
theorem solution
    (T : LevyKhintchineTriple)
    (e : Nat → Real) (he : ∀ n, 0 < e n ∧ e n < 1)
    (hzero : Tendsto e atTop (nhds 0))
    (nu : ProbabilityMeasure Real)
    (hnu : ∀ xi : Real, charFun (nu : Measure Real) xi =
      Complex.exp (Complex.I * ((T.drift * xi : Real) : Complex) +
        ∫ x in Ioo (-1 : Real) 1,
          levyCompensatedIntegrand xi x ∂T.levyMeasure)) :
    ∃ q : Nat → ProbabilityMeasure Real,
      Tendsto q atTop (nhds nu) ∧
      ∀ n (b : Real), Integrable (fun x : Real => Real.exp (b*x)) (q n : Measure Real) ∧
        (∫ x, Real.exp (b*x) ∂(q n : Measure Real)) =
        Real.exp (T.drift*b + ∫ x in {x : Real | e n ≤ |x| ∧ |x| < 1},
          (Real.exp (b*x)-1-b*x) ∂T.levyMeasure) := by
  let B (n : ℕ) := {x : ℝ | e n ≤ |x| ∧ |x| < 1}
  let m (n : ℕ) := T.levyMeasure.restrict (B n)
  have hQ (n : ℕ) := by
    letI := Kyprianou.Ch03.momentSmallJumpBandFiniteV1 T (e n) (he n).1
    have hm : MeasurableSet (B n) :=
      (measurableSet_le measurable_const continuous_abs.measurable).inter
        (measurableSet_lt continuous_abs.measurable measurable_const)
    have ha : ∀ᵐ x ∂m n, |x| < 1 :=
      (ae_restrict_mem hm).mono fun x hx => hx.2
    exact Kyprianou.Ch03.momentFiniteBoundedGaussianJumpLawV1 (m n) ha T.drift 0 1
  choose q hc hr using hQ
  refine ⟨q, FamousTheorems.levy_continuity.mpr ?_, ?_⟩
  · intro xi
    rw [hnu]
    have hl := Kyprianou.Ch02.sourceFaithfulSmallJumpExponentBandLimitV1
      T.levyMeasure T.levyMeasure_isLevyMeasure e he hzero 1 xi
    simp only [NNReal.coe_one, Complex.ofReal_one, one_mul] at hl
    simp_rw [hc, NNReal.coe_one, NNReal.coe_zero, Complex.ofReal_one,
      zero_mul, zero_div, Complex.ofReal_zero, sub_zero, one_mul, Complex.exp_add]
    exact hl.const_mul (Complex.exp (Complex.I * ((T.drift*xi : ℝ) : ℂ)))
  · intro n b
    simpa only [m, B, NNReal.coe_one, NNReal.coe_zero, zero_mul, zero_div,
      add_zero, one_mul] using hr n b
