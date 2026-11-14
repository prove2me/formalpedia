-- Prove2me | solution 1 for KSATSingleFlip.Connect.lemma_2_6_fixed_count
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:34:51.518683+00:00
-- url     : https://prove2.me/submissions/f3d6cb5e-abd3-4d9f-b25a-ba56374f8d56

import Theorems.Thm_RadGauss_RiskBound_mcdiarmid_inequality
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

theorem solution {A : Type} [MeasurableSpace A] (j : ℕ) (hj : 1 ≤ j)
    (μ : Measure A) [IsProbabilityMeasure μ] (F : (Fin j → A) → ℝ)
    (hF : Measurable F) (L u : ℝ) (hL : 1 ≤ L) (hu : 0 < u)
    (hreplace : ∀ (i : Fin j) (x : Fin j → A) (a : A),
      |F x - F (Function.update x i a)| ≤ 2*L) :
    Measure.pi (fun _ : Fin j => μ) {x | F x ≤ (∫ y, F y ∂(Measure.pi (fun _ : Fin j => μ))) - u} ≤
      ENNReal.ofReal (Real.exp (-(u^2)/(2*(j:ℝ)*L^2))) := by
  have hh := RadGauss.RiskBound.mcdiarmid_inequality j (fun _ : Fin j => μ) (fun x => -F x)
    hF.neg (fun _ => 2*L) (by
      intro i x a
      have h := hreplace i x a
      simpa only [neg_sub_neg, abs_sub_comm] using h) u hu
  have hsets : {x | F x ≤ (∫ y, F y ∂(Measure.pi (fun _ : Fin j => μ))) - u} =
      {x | u ≤ -F x - ∫ y, -F y ∂(Measure.pi (fun _ : Fin j => μ))} := by
    ext x
    simp only [Set.mem_setOf_eq, integral_neg]
    constructor <;> intro h <;> linarith
  rw [hsets]
  apply le_trans hh
  have hsum : (∑ _i : Fin j, (2*L)^2) = (j:ℝ)*(2*L)^2 := by simp
  rw [hsum]
  apply le_of_eq
  congr 2
  have hj' : (j:ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have hL' : L ≠ 0 := by linarith
  field_simp
