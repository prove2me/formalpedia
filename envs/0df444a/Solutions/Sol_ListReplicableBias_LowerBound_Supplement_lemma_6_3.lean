-- Prove2me | solution 1 for ListReplicableBias.LowerBound.Supplement.lemma_6_3
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:02:29.192888+00:00
-- url     : https://prove2.me/submissions/f7d2f225-fbf8-450f-b9fb-e966a0ea475f

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_Geometry
import Definitions.Def_ListReplicableBias_LowerBound_Supplement_Rounding

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open ListReplicableBias.LowerBound ListReplicableBias.LowerBound.Supplement

lemma lrb63_close {ε u x : ℝ} (hε : 0 < ε) (hu0 : 0 ≤ u) (hu1 : u < ε) :
    |roundShift ε u x - x| < ε := by
  unfold roundShift
  have ha1 : (⌊(x + u) / ε⌋ : ℝ) ≤ (x + u) / ε := Int.floor_le _
  have ha2 : (x + u) / ε < (⌊(x + u) / ε⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hε] at ha1
  rw [div_lt_iff₀ hε] at ha2
  rw [abs_lt]; constructor <;> nlinarith

theorem solution (ε u : ℝ) (hu : u ∈ Set.Ico (0 : ℝ) ε) :
    (∀ x : ℝ, |roundShift ε u x - x| < ε) ∧
    (∀ (d : ℕ) (x : Fin d → ℝ), ‖roundVec ε u x - x‖ < ε) := by
  have hε : 0 < ε := lt_of_le_of_lt hu.1 hu.2
  refine ⟨fun x => lrb63_close hε hu.1 hu.2, fun d x => ?_⟩
  rw [pi_norm_lt_iff hε]
  intro i
  rw [Real.norm_eq_abs]
  exact lrb63_close hε hu.1 hu.2
