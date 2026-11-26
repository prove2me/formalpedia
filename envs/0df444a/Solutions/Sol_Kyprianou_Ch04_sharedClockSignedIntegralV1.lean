-- Prove2me | solution 1 for Kyprianou.Ch04.sharedClockSignedIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:15:55.873799+00:00
-- url     : https://prove2.me/submissions/bea82e84-7dda-4c66-8918-3f12e8b582bd

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_sharedClockSignedIntegrabilityV1
import Theorems.Thm_Kyprianou_Ch04_sharedClockNonnegativeIntegral
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

/-- Transfer a signed integrable kernel through a shared expected clock. -/
theorem solution {Ω E A : Type} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace A]
    (P : Measure Ω) (μ : Measure A) (R : Ω → Measure E)
    (q : Ω → E → A) (hq : ∀ w, Measurable (q w))
    (hR : ∀ k : A → ENNReal, Measurable k →
      AEMeasurable (fun w => ∫⁻ z, k (q w z) ∂(R w)) P ∧
      (∫⁻ w, ∫⁻ z, k (q w z) ∂(R w) ∂P) = ∫⁻ a, k a ∂μ)
    (f : A → ℝ) (hf : Measurable f) (hi : Integrable f μ) :
    (∀ᵐ w ∂P, Integrable (fun z => f (q w z)) (R w)) ∧
      Integrable (fun w => ∫ z, f (q w z) ∂(R w)) P ∧
      (∫ w, ∫ z, f (q w z) ∂(R w) ∂P) = ∫ a, f a ∂μ := by
  let aux := Kyprianou.Ch04.sharedClockSignedIntegrabilityV1 P μ R q hq hR
  let p := fun a => max (f a) 0
  let n := fun a => max (-f a) 0
  have hp : Measurable p := hf.max measurable_const
  have hn : Measurable n := hf.neg.max measurable_const
  have hpi : Integrable p μ := hi.pos_part
  have hni : Integrable n μ := hi.neg_part
  have hsplit : f = fun a => p a - n a := by
    funext a
    dsimp [p,n]
    rcases le_total (f a) 0 with h|h <;> simp [max_eq_left,max_eq_right,h] <;> linarith
  have hAE : ∀ᵐ w ∂P, (∫ z, f (q w z) ∂(R w)) =
      (∫ z, p (q w z) ∂(R w)) - ∫ z, n (q w z) ∂(R w) := by
    filter_upwards [(aux p hp hpi).1,(aux n hn hni).1] with w h1 h2
    calc
      _ = ∫ z, p (q w z) - n (q w z) ∂(R w) := by conv_lhs => rw [hsplit]
      _ = _ := integral_sub h1 h2
  refine ⟨(aux f hf hi).1,(aux f hf hi).2,?_⟩
  rw [integral_congr_ae hAE,integral_sub (aux p hp hpi).2 (aux n hn hni).2,
    Kyprianou.Ch04.sharedClockNonnegativeIntegral P μ R q hq hR p hp
      (fun a => le_max_right _ _) hpi,
    Kyprianou.Ch04.sharedClockNonnegativeIntegral P μ R q hq hR n hn
      (fun a => le_max_right _ _) hni]
  conv_rhs => rw [hsplit]
  exact (integral_sub hpi hni).symm
