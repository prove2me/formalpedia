-- Prove2me | solution 1 for NumberField.AdelicFourier.integral_fourierChar_trace_mul_prod_eq_prod_integral_fourierChar_trace_single_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/88496f1a-a867-5722-a8e4-e22413548a00

import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_integral_fourierChar_trace_mul_prod_eq_prod_integral_fourierChar_trace_single_mul

set_option autoImplicit false

open MeasureTheory NumberField

theorem solution
    (F : Type) [Field F] [NumberField F] [DecidableEq (InfinitePlace F)]
    [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)]
    (μ : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, SigmaFinite (μ w)]
    (g : (w : InfinitePlace F) → w.Completion → ℂ) (ξ : InfiniteAdeleRing F) :
    ∫ y : InfiniteAdeleRing F,
        (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
            (InfiniteAdeleRing.ringEquiv_mixedSpace F (-(y * ξ)))) : ℂ) * ∏ w, g w (y w) ∂(Measure.pi μ)
      = ∏ w, ∫ z, (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
            (InfiniteAdeleRing.ringEquiv_mixedSpace F (Pi.single w (-(z * ξ w))))) : ℂ) * g w z ∂(μ w) := by

  set χ : InfiniteAdeleRing F → ℂ := fun a =>
    (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F a)) : ℂ)
    with hχ
  have hχ0 : χ 0 = 1 := by
    simp only [hχ, map_zero, AddChar.map_zero_eq_one, Circle.coe_one]
  have hχadd : ∀ a b : InfiniteAdeleRing F, χ (a + b) = χ a * χ b := by
    intro a b
    simp only [hχ, map_add, AddChar.map_add_eq_mul, Circle.coe_mul]
  have hχsum : ∀ (s : Finset (InfinitePlace F)) (f : InfinitePlace F → InfiniteAdeleRing F),
      χ (∑ w ∈ s, f w) = ∏ w ∈ s, χ (f w) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [hχ0]
    | insert w s hw ih => rw [Finset.sum_insert hw, Finset.prod_insert hw, hχadd, ih]
  have key : ∀ y : InfiniteAdeleRing F, χ (-(y * ξ)) = ∏ w, χ (Pi.single w (-(y w * ξ w))) := by
    intro y
    rw [← hχsum]
    congr 1
    conv_lhs => rw [← Finset.univ_sum_single (-(y * ξ))]
    rfl

  have hint : ∀ y : InfiniteAdeleRing F,
      χ (-(y * ξ)) * ∏ w, g w (y w) = ∏ w, (χ (Pi.single w (-(y w * ξ w))) * g w (y w)) := by
    intro y
    rw [key, ← Finset.prod_mul_distrib]
  show ∫ y : InfiniteAdeleRing F, χ (-(y * ξ)) * ∏ w, g w (y w) ∂(Measure.pi μ)
    = ∏ w, ∫ z, χ (Pi.single w (-(z * ξ w))) * g w z ∂(μ w)
  simp_rw [hint]
  exact MeasureTheory.integral_fintype_prod_eq_prod (fun w z => χ (Pi.single w (-(z * ξ w))) * g w z)

end S_NumberField_AdelicFourier_integral_fourierChar_trace_mul_prod_eq_prod_integral_fourierChar_trace_single_mul
end P2MW
export P2MW.S_NumberField_AdelicFourier_integral_fourierChar_trace_mul_prod_eq_prod_integral_fourierChar_trace_single_mul (solution)
