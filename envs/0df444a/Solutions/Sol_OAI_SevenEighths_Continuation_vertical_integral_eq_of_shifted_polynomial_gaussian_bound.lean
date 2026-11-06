-- Prove2me | solution 1 for OAI.SevenEighths.Continuation.vertical_integral_eq_of_shifted_polynomial_gaussian_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:43.869113+00:00
-- url     : https://prove2.me/submissions/9ab0c22a-8e97-40c3-87fa-278c9138dd71

import Definitions.Def_OAI_NumberTheory_DirichletL_ContinuationPolynomialContour
import Definitions.Def_OAI_NumberTheory_DirichletL_ContinuationShiftedGaussian
import Theorems.Thm_OAI_SevenEighths_Continuation_vertical_integral_eq_of_polynomial_gaussian_bound


set_option autoImplicit false
open OAI
noncomputable section
open MeasureTheory Set Filter Complex
open OAI.SevenEighths OAI.SevenEighths.Continuation
namespace OAI.SevenEighths.Continuation
theorem _root_.solution (F : ℂ→ℂ)
    {a b C : ℝ} (q : ℝ) (n : ℕ) (hab : a≤b)
    (hhol : DifferentiableOn ℂ F {s : ℂ | a≤s.re ∧ s.re≤b})
    (hbound : ∀x∈Icc a b,∀t : ℝ,
      ‖F ((x:ℂ)+t*I)‖≤C*polynomialGaussian n (t+q)) :
    (∫t : ℝ,F ((a:ℂ)+t*I))=∫t : ℝ,F ((b:ℂ)+t*I) := by
  let G : ℂ→ℂ := fun s=>F (s-(q:ℂ)*I)
  have hg : DifferentiableOn ℂ G {s : ℂ | a≤s.re ∧ s.re≤b} := by
    apply hhol.comp (differentiable_id.sub_const ((q:ℂ)*I)).differentiableOn
    intro s hs
    simpa using hs
  have hbnd (x : ℝ) (hx : x∈Icc a b) (t : ℝ) :
      ‖G ((x:ℂ)+t*I)‖≤C*polynomialGaussian n t := by
    have heq : (x:ℂ)+t*I-(q:ℂ)*I=(x:ℂ)+(t-q)*I := by ring
    simpa only [G,heq,sub_add_cancel,Complex.ofReal_sub] using hbound x hx (t-q)
  have hi := vertical_integral_eq_of_polynomial_gaussian_bound G n hab hg hbnd
  have heq (x : ℝ) : (∫t : ℝ,G ((x:ℂ)+t*I))=∫t : ℝ,F ((x:ℂ)+t*I) := by
    have hg' : (fun t : ℝ=>G ((x:ℂ)+t*I))=(fun t : ℝ=>F ((x:ℂ)+(t+(-q))*I)) := by
      funext t
      dsimp [G]
      congr 1
      ring
    rw [hg']
    simpa only [Complex.ofReal_add,Complex.ofReal_neg] using
      (integral_add_right_eq_self (fun t : ℝ=>F ((x:ℂ)+t*I)) (-q) (μ:=volume))
  simpa only [heq] using hi
end OAI.SevenEighths.Continuation
