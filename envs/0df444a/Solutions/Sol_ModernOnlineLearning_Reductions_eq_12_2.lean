-- Prove2me | solution 1 for ModernOnlineLearning.Reductions.eq_12_2
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T17:34:03.446407+00:00
-- url     : https://prove2.me/submissions/371b7c1b-8f6d-45d5-b317-f98b5730d652

import Definitions.Def_ModernOnlineLearning_Reductions_Setting

set_option autoImplicit false
open ModernOnlineLearning.Reductions

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (V W : Set E) (hV : V.Nonempty)
    (hclosed : IsClosed V) (hconv : Convex ℝ V) (hVW : V ⊆ W)
    (loss : ℕ → E → ℝ) (z x : ℕ → E) (g q : ℕ → E →L[ℝ] ℝ)
    (T : ℕ) (hT : 1 ≤ T) (hRun : IsProjectedRun V W loss z x g q T)
    (u : E) (hu : u ∈ V) :
    ModernOnlineLearning.OGD.regret loss x u T ≤ ∑ t ∈ Finset.Icc 1 T, g t (x t - u) ∧
      (∑ t ∈ Finset.Icc 1 T, g t (x t - u)) =
        ∑ t ∈ Finset.Icc 1 T, (g t (z t - u) + g t (x t - z t)) := by
  constructor
  · apply Finset.sum_le_sum
    intro t ht
    have hs := (hRun t ht).2.2.1 u hu
    simp only [map_sub] at hs ⊢
    linarith
  · apply Finset.sum_congr rfl
    intro t ht
    simp only [map_sub]
    ring

