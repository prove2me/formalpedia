-- Prove2me | solution 1 for Kyprianou.Ch04.clockSignedInfimumLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:45:41.68239+00:00
-- url     : https://prove2.me/submissions/132035e2-b11f-4d99-a2b0-7e059515e7e0

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_drawdown_infimum_marginal_law
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The signed product-clock drawdown has the same law as the actual running infimum. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (q : ℝ) (hq : 0 < q) :
    IdentDistrib
      (fun z : Ω × ℝ => -(runningSup L z.2.toNNReal z.1 - L.X z.2.toNNReal z.1))
      (fun z : Ω × ℝ => sInf ((fun s : NNReal => L.X s z.1) '' Iic z.2.toNNReal))
      (P.prod (expMeasure q)) (P.prod (expMeasure q)) := by
  let A : Ω × ℝ → ℝ := fun z => runningSup L z.2.toNNReal z.1 - L.X z.2.toNNReal z.1
  let B : Ω × ℝ → ℝ := fun z => -sInf {y : ℝ | ∃ s : NNReal, s ≤ z.2.toNNReal ∧ y = L.X s z.1}
  let Q := P.prod (expMeasure q)
  have hmeas := levy_exponential_real_clock_extrema_drawdown_measurable L
  have hm : Q.map A = Q.map B := by
    simpa only [A,B,Q,L.X_zero,zero_add] using
      avram_ws01e_bt_new_original_clock_drawdown_infimum_marginal_law L q hq
  have hid : IdentDistrib A B Q Q := ⟨hmeas.snd.aemeasurable,hmeas.fst.snd.aemeasurable,hm⟩
  have hs (z : Ω × ℝ) : ((fun s : NNReal => L.X s z.1) '' Iic z.2.toNNReal) =
      {y : ℝ | ∃ s : NNReal, s ≤ z.2.toNNReal ∧ y = L.X s z.1} := by
    ext y
    constructor <;> rintro ⟨s,h,he⟩ <;> exact ⟨s,h,he.symm⟩
  simpa only [A,B,Q,Function.comp_def,neg_neg,hs] using
    (hid.comp (measurable_neg : Measurable (fun x : ℝ => -x)))
