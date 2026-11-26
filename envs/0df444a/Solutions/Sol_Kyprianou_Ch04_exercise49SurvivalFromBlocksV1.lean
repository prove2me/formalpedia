-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49SurvivalFromBlocksV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:58:11.895215+00:00
-- url     : https://prove2.me/submissions/518fb203-137c-449c-b49e-01065809e3b7

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49AllPathCadlagVersionV1
import Theorems.Thm_Kyprianou_Ch04_exercise49SurvivalFromAllPathBlocksV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Transfer the all-path block construction by indistinguishability. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hSafe : ∃ n : ℕ, 0 < P {ω | ∀ t : NNReal, -(n : ℝ) ≤ X t ω})
    (hBlock : ∃ s : NNReal, 0 < s ∧ ∃ a : ℝ, 0 < a ∧
      0 < P {ω | (∀ t : NNReal, t ≤ s → 0 ≤ X t ω) ∧ a ≤ X s ω}) :
    (P {ω | (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ X t ω < 0}) ≠ ⊤}).toReal < 1 := by
  obtain ⟨Y, hY, hm, hc, he⟩ :=
    Kyprianou.Ch04.exercise49AllPathCadlagVersionV1 P X hX
  obtain ⟨n, hn⟩ := hSafe
  obtain ⟨s, hs, a, ha, hb⟩ := hBlock
  have hSafeY : P {ω | ∀ t : NNReal, -(n : ℝ) ≤ Y t ω} =
      P {ω | ∀ t : NNReal, -(n : ℝ) ≤ X t ω} := by
    apply measure_congr
    filter_upwards [he] with ω h
    change (∀ t : NNReal, -(n : ℝ) ≤ Y t ω) =
      (∀ t : NNReal, -(n : ℝ) ≤ X t ω)
    simp only [h]
  have hBlockY :
      P {ω | (∀ t : NNReal, t ≤ s → 0 ≤ Y t ω) ∧ a ≤ Y s ω} =
      P {ω | (∀ t : NNReal, t ≤ s → 0 ≤ X t ω) ∧ a ≤ X s ω} := by
    apply measure_congr
    filter_upwards [he] with ω h
    change ((∀ t : NNReal, t ≤ s → 0 ≤ Y t ω) ∧ a ≤ Y s ω) =
      ((∀ t : NNReal, t ≤ s → 0 ≤ X t ω) ∧ a ≤ X s ω)
    simp only [h]
  have hRuin :
      P {ω | (sInf {v : WithTop NNReal | ∃ t : NNReal,
        v = ↑t ∧ 0 < t ∧ Y t ω < 0}) ≠ ⊤} =
      P {ω | (sInf {v : WithTop NNReal | ∃ t : NNReal,
        v = ↑t ∧ 0 < t ∧ X t ω < 0}) ≠ ⊤} := by
    apply measure_congr
    filter_upwards [he] with ω h
    change ((sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ Y t ω < 0}) ≠ ⊤) =
      ((sInf {v : WithTop NNReal | ∃ t : NNReal,
        v = ↑t ∧ 0 < t ∧ X t ω < 0}) ≠ ⊤)
    simp only [h]
  rw [← hRuin]
  exact Kyprianou.Ch04.exercise49SurvivalFromAllPathBlocksV1 P Y hY hm hc
    ⟨n, hSafeY ▸ hn⟩ ⟨s, hs, a, ha, hBlockY ▸ hb⟩
