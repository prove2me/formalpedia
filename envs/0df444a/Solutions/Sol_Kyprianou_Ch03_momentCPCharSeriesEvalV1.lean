-- Prove2me | solution 1 for Kyprianou.Ch03.momentCPCharSeriesEvalV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T15:03:52.367033+00:00
-- url     : https://prove2.me/submissions/6a1ccc39-ee33-4a5a-97d5-529a0c20b087

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch03_momentFourierCharacterIntegrableV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (mu : Measure Real) [IsFiniteMeasure mu] (xi : Real) :
    (∑' n : ℕ, ((Real.exp (-(mu Set.univ).toReal) : ℝ) : ℂ) *
        ((charFun mu xi) ^ n / (n.factorial : ℂ))) =
      Complex.exp (∫ x, (Complex.exp (Complex.I * (((xi * x : Real) : Complex))) - 1) ∂mu) := by
  let M : ℝ := (mu Set.univ).toReal
  let F (x : ℝ) := Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I)
  have hF : Integrable F mu := Kyprianou.Ch03.momentFourierCharacterIntegrableV1 mu xi
  have hsum := (NormedSpace.expSeries_div_hasSum_exp (charFun mu xi)).mul_left
    ((Real.exp (-M) : ℝ) : ℂ)
  change (∑' n : ℕ, ((Real.exp (-M) : ℝ) : ℂ) *
    ((charFun mu xi) ^ n / (n.factorial : ℂ))) = _
  rw [hsum.tsum_eq]
  have heq : (fun x : ℝ => Complex.exp (Complex.I * (((xi * x : ℝ) : ℂ))) - 1) =
      fun x => F x - 1 := by
    funext x
    dsimp [F]
    push_cast
    congr 2
    ring
  rw [heq, integral_sub hF (integrable_const _)]
  have hchar : (∫ x, F x ∂mu) = charFun mu xi := (charFun_apply_real xi).symm
  rw [hchar]
  simp only [integral_const, Complex.real_smul, mul_one]
  rw [← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  dsimp [M, Measure.real]
  push_cast
  ring
