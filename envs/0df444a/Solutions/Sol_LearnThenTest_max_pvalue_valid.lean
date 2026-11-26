-- Prove2me | solution 1 for LearnThenTest.max_pvalue_valid
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:54:24.986268+00:00
-- url     : https://prove2.me/submissions/d86ea5a2-9761-4d66-a54e-826987c58c4c

import Mathlib
import Definitions.Def_LearnThenTest_Basic

open MeasureTheory ProbabilityTheory Filter
namespace LearnThenTest

theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m : ℕ} (R α : Fin m → ℝ) (p : Fin m → Ω → ℝ)
    (hp : ∀ l, Measurable (p l)) (hvalid : ∀ l, α l < R l → IsValidPValue P (p l))
    (hnull : ∃ l, α l < R l) :
    IsValidPValue P (fun ω => ⨆ l, p l ω) := by
  obtain ⟨l, hl⟩ := hnull
  intro u hu
  refine le_trans (measure_mono ?_) (hvalid l hl u hu)
  intro ω hω
  exact le_trans (le_ciSup (Set.finite_range fun l => p l ω).bddAbove l) hω


end LearnThenTest
