-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_predictable_martingale_increment_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:26:59.765524+00:00
-- url     : https://prove2.me/submissions/b4f3eafb-8b4c-4278-a66c-46c1e538b66d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb49_predictable_real_condExp_cross_zero
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every bounded predictable coefficient has zero expectation against an
increment of an integrable real martingale. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration NNReal mΩ)
    (E : NNReal → Ω → Real) (hE : Martingale E F P)
    (W : Ω → Real) (s t : NNReal) (hst : s ≤ t)
    (hW : Measurable[F s] W) (C : Real)
    (hWBound : ∀ w, ‖W w‖ ≤ C) :
    (∫ w, W w * (E t w - E s w) ∂P) = 0 := by
  have hm : (F s : MeasurableSpace Ω) ≤ mΩ := F.le s
  have hQ : Integrable (fun w => E t w - E s w) P :=
    (hE.integrable t).sub (hE.integrable s)
  have hWambient : Measurable W := hW.mono hm le_rfl
  have hProd : Integrable (fun w => W w * (E t w - E s w)) P :=
    hQ.bdd_mul hWambient.aestronglyMeasurable
      (Filter.Eventually.of_forall hWBound)
  have hSM : StronglyMeasurable[F s] (E s) := hE.stronglyAdapted s
  have hCEself : P[E s | F s] =ᵐ[P] E s :=
    Filter.EventuallyEq.of_eq
      (condExp_of_stronglyMeasurable hm hSM (hE.integrable s))
  have hC : P[(fun w => E t w - E s w) | F s] =ᵐ[P]
      (fun _ => (0 : Real)) := by
    calc
      P[(fun w => E t w - E s w) | F s] =ᵐ[P]
          (fun w => (P[E t | F s]) w - (P[E s | F s]) w) :=
        condExp_sub (hE.integrable t) (hE.integrable s) (F s)
      _ =ᵐ[P] (fun w => E s w - E s w) :=
        (hE.condExp_ae_eq hst).sub hCEself
      _ =ᵐ[P] (fun _ => (0 : Real)) := by simp
  exact AvramDividend.Classical.avram_gb49_predictable_real_condExp_cross_zero hm W
    (fun w => E t w - E s w) hW hQ hProd hC
