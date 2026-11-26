-- Prove2me | solution 1 for Kyprianou.Ch04.lpNormEqOfSquareIntegralEq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:50:59.725054+00:00
-- url     : https://prove2.me/submissions/5ad42439-cee8-4c01-b101-5d179256c9f2

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_Kyprianou_Ch04_lpNormSqIntegral
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false
universe u v

/-- Equality of square integrals implies equality of the L2 norms. -/
theorem solution
    {A : Type u} {Ω : Type v} [MeasurableSpace A] [MeasurableSpace Ω]
    (μ : Measure A) (P : Measure Ω) (f : A → ℝ) (X : Ω → ℝ)
    (hf : MemLp f 2 μ) (hX : MemLp X 2 P)
    (h : (∫ ω, (X ω)^2 ∂P) = ∫ a, (f a)^2 ∂μ) :
    ‖hX.toLp X‖ = ‖hf.toLp f‖ := by
  have hs : ‖hX.toLp X‖ ^ 2 = ‖hf.toLp f‖ ^ 2 := by
    rw [Kyprianou.Ch04.lpNormSqIntegral P X hX,
      Kyprianou.Ch04.lpNormSqIntegral μ f hf, h]
  nlinarith [norm_nonneg (hX.toLp X), norm_nonneg (hf.toLp f)]
