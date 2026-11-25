-- Prove2me | solution 1 for Kyprianou.Ch04.fixedHorizonSignedExtremaLaplaceEquality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:47:58.120986+00:00
-- url     : https://prove2.me/submissions/1b829d1a-018f-4c9c-b499-17a306c9c517

import Mathlib
import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_Kyprianou_Ch04_fixedHorizonSignedDrawdownInfimumLaw
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Fixed-horizon signed extrema have the same exponential moments. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (t : NNReal) (ht : 0 < t)
    (beta : ℝ) :
    (∫ w : Ω, Real.exp (beta *
      (L.X t w - sSup ((fun s : NNReal => L.X s w) '' Iic t))) ∂P) =
    (∫ w : Ω, Real.exp (beta *
      (sInf ((fun s : NNReal => L.X s w) '' Iic t))) ∂P) := by
  let A : Ω → ℝ :=
    fun w => L.X t w - sSup ((fun s : NNReal => L.X s w) '' Iic t)
  let B : Ω → ℝ :=
    fun w => sInf ((fun s : NNReal => L.X s w) '' Iic t)
  have hID : IdentDistrib A B P P :=
    Kyprianou.Ch04.fixedHorizonSignedDrawdownInfimumLaw P F L t ht
  have hMeas : Measurable (fun z : ℝ => Real.exp (beta * z)) := by
    fun_prop
  have hComp := hID.comp hMeas
  simpa only [A, B, Function.comp_def] using hComp.integral_eq
