-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45FiniteCofinalStopsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:12:38.388582+00:00
-- url     : https://prove2.me/submissions/4fa3dec7-d74e-473e-a015-715b32b174d7

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_exercise45ClippedExitMonotoneCofinalV1
import Theorems.Thm_Kyprianou_Ch04_exercise45ClippedExitStoppingV1
import Theorems.Thm_Kyprianou_Ch04_exercise45ClippedExitBoundsV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Increasing finite spatial exits bound the physical left state through the exit itself. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal inferInstance)
    (X L : NNReal → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hRC : F.IsRightContinuous)
    (hNull : ∀ (s : NNReal) (N A : Set Ω), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (hAdapt : Adapted F X)
    (hL : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (hL0 : ∀ᵐ w ∂P, L 0 w = X 0 w) :
    ∃ τ : ℕ → Ω → NNReal,
      (∀ n w, τ n w ≤ (n : NNReal)) ∧
      (∀ n, IsStoppingTime F (fun w => (τ n w : WithTop NNReal))) ∧
      (∀ w, Monotone (fun n => τ n w)) ∧
      (∀ᵐ w ∂P, Tendsto (fun n => (τ n w : WithTop NNReal)) atTop (nhds ⊤)) ∧
      (∀ᵐ w ∂P, ∀ n, (∀ t < τ n w, |X t w| ≤ (n : ℝ)) ∧
        (∀ t ≤ τ n w, |L t w| ≤ (n : ℝ))) := by
  let σ (n : ℕ) (w : Ω) : WithTop NNReal :=
    sInf {v | ∃ u : NNReal, v = ↑u ∧ (n : ℝ) < |X u w|}
  let τ (n : ℕ) (w : Ω) : NNReal :=
    (min (σ n w) (n : NNReal)).untopD (n : NNReal)
  obtain ⟨hb,hm,he⟩ := Kyprianou.Ch04.exercise45ClippedExitMonotoneCofinalV1 P F X hX
  refine ⟨τ,hb,?_,hm,he,?_⟩
  · exact Kyprianou.Ch04.exercise45ClippedExitStoppingV1 P F X hX hRC hNull hAdapt
  · exact Kyprianou.Ch04.exercise45ClippedExitBoundsV1 P F X L hX hL hL0
