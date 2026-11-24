-- Prove2me | solution 1 for Kyprianou.Ch03.momentSmallGaussianMarginalFiniteApproxV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T15:46:01.347036+00:00
-- url     : https://prove2.me/submissions/9537c3ce-e1f7-4cc2-856a-01409acece26

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
import Theorems.Thm_Kyprianou_Ch03_momentSmallJumpCutoffSequenceV1
import Theorems.Thm_Kyprianou_Ch03_momentSmallJumpBandFiniteV1
import Theorems.Thm_Kyprianou_Ch03_momentFiniteBoundedGaussianJumpLawV1
import Theorems.Thm_Kyprianou_Ch03_momentSmallJumpBandRealIntegralBoundV1
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulSmallJumpExponentBandLimitV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple) (t : NNReal) (ht : 0 < t) :
    ∃ q : ℕ → ProbabilityMeasure Real,
      (∀ xi : Real, Tendsto (fun n => charFun (q n : Measure Real) xi) atTop
        (𝓝 (Complex.exp (((t : Real) : Complex) *
          (Complex.I * ((T.drift * xi : Real) : Complex) -
          (((T.gaussianVariance : Real) * xi ^ 2 / 2 : Real) : Complex) +
          ∫ x in Set.Ioo (-1 : Real) 1,
            ProbabilityTheory.levyCompensatedIntegrand xi x ∂T.levyMeasure))))) ∧
      ∀ b : Real, ∃ C : ENNReal, C < ⊤ ∧
        ∀ n, (∫⁻ x, ENNReal.ofReal (Real.exp (b * x)) ∂(q n : Measure Real)) ≤ C := by
  obtain ⟨e, he, hzero⟩ := Kyprianou.Ch03.momentSmallJumpCutoffSequenceV1
  let B (n : ℕ) : Set ℝ := {x | e n ≤ |x| ∧ |x| < 1}
  let nu (n : ℕ) := T.levyMeasure.restrict (B n)
  have hQ (n : ℕ) := by
    letI := Kyprianou.Ch03.momentSmallJumpBandFiniteV1 T (e n) (he n).1
    have hm : MeasurableSet (B n) := by
      dsimp [B]
      exact (measurableSet_le measurable_const continuous_abs.measurable).inter
        (measurableSet_lt continuous_abs.measurable measurable_const)
    have ha : ∀ᵐ x ∂nu n, |x| < 1 :=
      (ae_restrict_mem hm).mono fun x hx => hx.2
    exact Kyprianou.Ch03.momentFiniteBoundedGaussianJumpLawV1 (nu n) ha T.drift T.gaussianVariance t
  choose q hchar hreal using hQ
  refine ⟨q, ?_, ?_⟩
  · intro xi
    let D : ℂ := Complex.I * ((T.drift * xi : ℝ) : ℂ) -
      (((T.gaussianVariance : ℝ) * xi ^ 2 / 2 : ℝ) : ℂ)
    let k : ℂ := ((t : ℝ) : ℂ)
    have hlim := Kyprianou.Ch02.sourceFaithfulSmallJumpExponentBandLimitV1
      T.levyMeasure T.levyMeasure_isLevyMeasure e he hzero t xi
    simp_rw [hchar, nu, B, mul_add, Complex.exp_add]
    exact hlim.const_mul (Complex.exp (k*D))
  · intro b
    let M := T.drift*b + (T.gaussianVariance : ℝ)*b^2/2 +
      ∫ x in Set.Ioo (-1 : ℝ) 1, (Real.exp (b*x)-1-b*x) ∂T.levyMeasure
    refine ⟨ENNReal.ofReal (Real.exp ((t : ℝ)*M)), ENNReal.ofReal_lt_top, fun n => ?_⟩
    rw [← ofReal_integral_eq_lintegral_ofReal (hreal n b).1
      (Eventually.of_forall fun x => (Real.exp_pos (b*x)).le), (hreal n b).2]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ t.coe_nonneg
    exact add_le_add_right (Kyprianou.Ch03.momentSmallJumpBandRealIntegralBoundV1 T (e n) b) _
