-- Prove2me | solution 1 for LargeDelaySGD.MeanSquare.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:46:09.429008+00:00
-- url     : https://prove2.me/submissions/434ef940-c360-4437-b8af-73f363ea5714

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model
import Theorems.Thm_LargeDelaySGD_MeanSquare_remark_1
import Theorems.Thm_LargeDelaySGD_MeanSquare_lemma_1
import Theorems.Thm_LargeDelaySGD_MeanSquare_lemma_2
import Theorems.Thm_LargeDelaySGD_MeanSquare_lemma_A_4
import Theorems.Thm_LargeDelaySGD_MeanSquare_delay_sum_sublinear
import Theorems.Thm_LargeDelaySGD_MeanSquare_delay_sum_linear
import Theorems.Thm_LargeDelaySGD_MeanSquare_delay_sum_polynomial

open MeasureTheory ProbabilityTheory LargeDelaySGD.MeanSquare

theorem solution {d : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (B : ℝ) (L : NNReal) (hA1 : Assumption1 F μ B L)
    (α : ℕ → ℝ) (s : ℕ → ℕ) (hA2 : Assumption2 α s)
    (hinf : BddBelow (Set.range (objective F μ)))
    (ω : ℕ → Ω → Ξ) (hω : IIDNoise P μ ω) (x₀ : EuclideanSpace ℝ (Fin d))
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : IsDASGD F α s ω x₀ X) :
    Differentiable ℝ (objective F μ) ∧
      (∀ n, Integrable (fun a => ‖gradient (objective F μ) (X n a)‖ ^ 2) P) ∧
      Filter.Tendsto (fun n => ∫ a, ‖gradient (objective F μ) (X n a)‖ ^ 2 ∂P)
        Filter.atTop (nhds 0) := by
  obtain ⟨-, hgrad, -⟩ := remark_1 μ F B L hA1
  obtain ⟨hint, hsum⟩ := lemma_1 μ P F B L hA1 α s hA2 hinf ω hω x₀ X hX
  obtain ⟨-, C, hC, hCb⟩ := lemma_2 μ P F B L hA1 α s hA2 ω hω x₀ X hX
  obtain ⟨hpos, hs, hreg⟩ := hA2
  have hns : ¬ Summable (fun n => α (n + 1)) := by
    rcases hreg with h | h | h | h
    · intro hc
      exact h.2.2 ((summable_nat_add_iff 1).mp hc)
    · exact (delay_sum_sublinear α s hs hpos h).2.1
    · exact (delay_sum_linear α s hs hpos h).2.1
    · exact (delay_sum_polynomial α s hs hpos h).2.1
  refine ⟨fun x => (hgrad x).differentiableAt, hint, ?_⟩
  exact lemma_A_4 (fun n => α (n + 1)) _ (fun n => (hpos _).le)
    (fun n => integral_nonneg (fun a => by positivity)) hns hsum C hC hCb
