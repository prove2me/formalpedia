-- Prove2me | solution 1 for Kyprianou.Ch03.momentCPCharSeriesV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T15:46:09.872248+00:00
-- url     : https://prove2.me/submissions/a8d8bd64-daeb-4b2a-98d4-383fe85acb69

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_KSATSingleFlip_Connect_compound_poisson_probability
import Theorems.Thm_Kyprianou_Ch03_momentCPCharPowV1
import Theorems.Thm_Kyprianou_Ch03_momentFourierCharacterIntegrableV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (mu : Measure Real) [IsFiniteMeasure mu] (xi : Real) :
    charFun (KSATSingleFlip.Connect.compoundPoisson mu) xi =
      ∑' n : ℕ, ((Real.exp (-(mu Set.univ).toReal) : ℝ) : ℂ) *
        ((charFun mu xi) ^ n / (n.factorial : ℂ)) := by
  let cp := KSATSingleFlip.Connect.compoundPoisson mu
  let F (x : ℝ) := Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I)
  let M : ℝ := (mu Set.univ).toReal
  letI : IsProbabilityMeasure cp := ⟨KSATSingleFlip.Connect.compound_poisson_probability mu⟩
  have hi : Integrable F cp := Kyprianou.Ch03.momentFourierCharacterIntegrableV1 cp xi
  have he : cp = Measure.sum (fun n : ℕ =>
      ENNReal.ofReal (Real.exp (-M) / (n.factorial : ℝ)) • KSATSingleFlip.Connect.convPow mu n) := by
    unfold cp KSATSingleFlip.Connect.compoundPoisson
    rw [if_neg (measure_ne_top mu _)]
  rw [he] at hi
  change charFun cp xi = _
  rw [charFun_apply_real, he]
  change (∫ x, F x ∂_) = _
  rw [integral_sum_measure hi]
  apply tsum_congr
  intro n
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]
  change (Real.exp (-M) / (n.factorial : ℝ)) • (∫ x, F x ∂KSATSingleFlip.Connect.convPow mu n) = _
  have hh := Kyprianou.Ch03.momentCPCharPowV1 mu xi n
  rw [charFun_apply_real] at hh
  change (∫ x, F x ∂KSATSingleFlip.Connect.convPow mu n) = _ at hh
  rw [hh, Complex.real_smul]
  dsimp [M]
  push_cast
  ring
