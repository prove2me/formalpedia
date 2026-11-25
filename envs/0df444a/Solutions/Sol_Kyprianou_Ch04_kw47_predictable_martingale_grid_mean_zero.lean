-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_predictable_martingale_grid_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:30:54.843614+00:00
-- url     : https://prove2.me/submissions/2a80fb7e-a484-41d3-a57f-df9746016ff2

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_predictable_martingale_increment_zero
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration NNReal mΩ)
    (E : NNReal → Ω → Real) (hE : Martingale E F P)
    (W : ℕ → Ω → Real) (u : ℕ → NNReal) (hu : Monotone u)
    (hW : ∀ i, Measurable[F (u i)] (W i)) (C : Real)
    (hWBound : ∀ i w, ‖W i w‖ ≤ C) (n : ℕ) :
    (∫ w, ∑ i ∈ Finset.range n,
      W i w * (E (u (i + 1)) w - E (u i) w) ∂P) = 0 := by
  have hTerm (i : ℕ) : Integrable
      (fun w => W i w * (E (u (i + 1)) w - E (u i) w)) P := by
    have hQ := (hE.integrable (u (i + 1))).sub (hE.integrable (u i))
    exact hQ.bdd_mul ((hW i).mono (F.le _) le_rfl).aestronglyMeasurable
      (Filter.Eventually.of_forall (hWBound i))
  have hZero (i : ℕ) :
      (∫ w, W i w * (E (u (i + 1)) w - E (u i) w) ∂P) = 0 :=
    Kyprianou.Ch04.kw47_predictable_martingale_increment_zero P F E hE (W i)
      (u i) (u (i + 1)) (hu (Nat.le_succ i)) (hW i) C (hWBound i)
  rw [integral_finsetSum (Finset.range n) (fun i _ => hTerm i)]
  simp [hZero]
