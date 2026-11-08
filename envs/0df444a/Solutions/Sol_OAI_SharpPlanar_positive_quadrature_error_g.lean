-- Prove2me | solution 1 for OAI.SharpPlanar.positive_quadrature_error_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:06:57.69146+00:00
-- url     : https://prove2.me/submissions/ca074a05-da90-4aeb-826a-792c2f712fb3

import Mathlib

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Quadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev



open MeasureTheory Set
open scoped BigOperators

namespace SharpPlanar


lemma positive_quadrature_error_g_oai {ι : Type*} [Fintype ι]
    (a b : ℝ) (hab : a ≤ b) (w t : ι → ℝ) (f p : ℝ → ℂ) (ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, t i ∈ Icc a b)
    (hmass : ∑ i, w i = b-a)
    (hf : ContinuousOn f (Icc a b)) (hp : ContinuousOn p (Icc a b))
    (herr : ∀ x ∈ Icc a b, ‖f x-p x‖ ≤ ε)
    (hexact : (∫ x in a..b, p x) = ∑ i, (w i : ℂ)*p (t i)) :
    ‖(∫ x in a..b, f x)-∑ i, (w i : ℂ)*f (t i)‖ ≤ 2*(b-a)*ε := by
  have hi₁ : IntervalIntegrable f volume a b :=
    (hf.intervalIntegrable_of_Icc hab)
  have hi₂ : IntervalIntegrable p volume a b :=
    (hp.intervalIntegrable_of_Icc hab)
  have he : (∫ x in a..b, f x)-∑ i, (w i : ℂ)*f (t i) =
      (∫ x in a..b, f x-p x) - ∑ i, (w i : ℂ)*(f (t i)-p (t i)) := by
    rw [intervalIntegral.integral_sub hi₁ hi₂, hexact]
    simp only [mul_sub, Finset.sum_sub_distrib]
    abel
  rw [he]
  have hInt : ‖∫ x in a..b, f x-p x‖ ≤ (b-a)*ε := by
    calc
      _ ≤ ∫ x in a..b, ‖f x-p x‖ := intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ x in a..b, ε := intervalIntegral.integral_mono_on hab
        (hi₁.sub hi₂).norm (intervalIntegrable_const) (fun x hx => herr x hx)
      _ = (b-a)*ε := by simp
  have hFin : ‖∑ i, (w i : ℂ)*(f (t i)-p (t i))‖ ≤ (b-a)*ε := by
    calc
      _ ≤ ∑ i, ‖(w i : ℂ)*(f (t i)-p (t i))‖ := norm_sum_le _ _
      _ ≤ ∑ i, w i*ε := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
        exact mul_le_mul_of_nonneg_left (herr _ (ht i)) (hw i)
      _ = (b-a)*ε := by rw [← Finset.sum_mul, hmass]
  exact (norm_sub_le _ _).trans (by nlinarith)

end SharpPlanar


end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpPlanar.positive_quadrature_error_g_oai.{u_1} := @OAI.SharpPlanar.positive_quadrature_error_g_oai.{u_1}
