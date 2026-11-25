-- Prove2me | solution 1 for Newton.memLp_mul_of_memLp_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:10:09.679577+00:00
-- url     : https://prove2.me/submissions/f61d1f8e-5c9c-4f3e-8ba4-7ab2950d7df6

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Theorems.Thm_Newton_holder_inequality

set_option autoImplicit false
open MeasureTheory ENNReal NNReal
open scoped ENNReal BigOperators
open Newton
variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
namespace Newton
theorem _root_.solution
    (p q : ℝ≥0∞)
    (hpq : IsConjugateExponent p q)
    (f : α → ℝ) (g : α → ℝ)
    (hf : MemLp f p μ)
    (hg : MemLp g q μ) :
    Integrable (fun x => f x * g x) μ := by
  obtain ⟨h_int, -⟩ :=
    holder_inequality (μ := μ) (p := p) (q := q) hpq f g hf hg
  refine ⟨hf.aestronglyMeasurable.mul hg.aestronglyMeasurable, ?_⟩
  have h_finite : HasFiniteIntegral (fun x => ‖f x‖ * ‖g x‖) μ :=
    h_int.hasFiniteIntegral
  have h_finite' : HasFiniteIntegral (fun x => f x * g x) μ :=
    h_finite.congr' <|
      (Filter.Eventually.of_forall fun x => by
        simp [Real.norm_eq_abs])
  simpa using h_finite'
end Newton
