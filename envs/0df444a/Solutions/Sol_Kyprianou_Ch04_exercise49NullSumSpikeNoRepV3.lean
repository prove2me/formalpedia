-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49NullSumSpikeNoRepV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:52:08.857877+00:00
-- url     : https://prove2.me/submissions/160c55a2-c626-43c9-a724-59fc0f4a7c95

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49SpikeTimeV3
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (Y : NNReal → (Ω ⊕ E) → ℝ) (a : E → NNReal)
    (ha : ∀ e, 0 < a e) (hBad : ¬ MeasurableSet {e | a e ≤ 1})
    (hSpike : ∀ t e, Y t (Sum.inr e) = if t = a e then -1 else 0) :
    let τ := fun w : Ω ⊕ E => sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ Y t w < 0}
    ¬ ∃ f : Ω ⊕ E → NNReal, Measurable f ∧
      ∀ w, τ w ≠ ⊤ → τ w = (f w : WithTop NNReal) := by
  dsimp only
  intro ⟨f,hf,hEq⟩
  have he (e : E) : (sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ Y t (Sum.inr e) < 0}) = (a e : WithTop NNReal) := by
    simp only [hSpike]
    exact exercise49SpikeTimeV3 (a e) (ha e)
  have hF : f ∘ Sum.inr = a := by
    funext e
    have ht : (sInf {v : WithTop NNReal |
        ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ Y t (Sum.inr e) < 0}) ≠ ⊤ := by rw [he]; exact WithTop.coe_ne_top
    exact WithTop.coe_injective ((hEq (Sum.inr e) ht).symm.trans (he e))
  have hm : Measurable a := hF ▸ hf.comp measurable_inr
  exact hBad (measurableSet_le hm measurable_const)
