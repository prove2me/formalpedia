-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_martingale_from_grid_event_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:15:27.622886+00:00
-- url     : https://prove2.me/submissions/78c58407-20ed-4cdd-8d64-5321ac67b543

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_dominated_event_zero
import Theorems.Thm_Kyprianou_Ch04_kw47_martingale_of_event_increment_zero
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Conditional-centred approximants transfer their martingale
property to an adapted L1-dominated pathwise limit. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration NNReal mΩ)
    (M : NNReal → Ω → Real)
    (hAdapt : StronglyAdapted F M)
    (hInt : ∀ t, Integrable (M t) P)
    (Q : NNReal → NNReal → Nat → Ω → Real)
    (B : NNReal → NNReal → Ω → Real)
    (hQInt : ∀ a b, a ≤ b → ∀ n, Integrable (Q a b n) P)
    (hBInt : ∀ a b, a ≤ b → Integrable (B a b) P)
    (hBound : ∀ a b, a ≤ b → ∀ n, ∀ᵐ w ∂P,
      ‖Q a b n w‖ ≤ B a b w)
    (hLim : ∀ a b, a ≤ b → ∀ᵐ w ∂P,
      Tendsto (fun n => Q a b n w) atTop
        (nhds (M a w - M b w)))
    (hZero : ∀ a b, a ≤ b → ∀ n, ∀ A : Set Ω,
      MeasurableSet[F a] A →
        (∫ w in A, Q a b n w ∂P) = 0) :
    Martingale M F P := by
  apply Kyprianou.Ch04.kw47_martingale_of_event_increment_zero
    P F M hAdapt hInt
  intro a b hab A hA
  exact Kyprianou.Ch04.kw47_dominated_event_zero P A
    (Q a b) (fun w => M a w - M b w) (B a b)
    (hQInt a b hab) (hBInt a b hab)
    (hBound a b hab) (hLim a b hab)
    (fun n => hZero a b hab n A hA)
