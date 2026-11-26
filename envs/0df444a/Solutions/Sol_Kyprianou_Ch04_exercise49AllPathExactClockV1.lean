-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49AllPathExactClockV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:48:06.823797+00:00
-- url     : https://prove2.me/submissions/7d22b8fd-85d1-4547-9330-6b622df17b14

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49RationalClockEqV3
import Theorems.Thm_Kyprianou_Ch04_exercise49RationalClockMeasurableV3
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- On measurable all-path cadlag Levy versions the strict first-passage clock has a pointwise finite representative. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, IsCadlag (fun t => X t ω)) :
    let τ : Ω → WithTop NNReal := fun ω => sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ X t ω < 0}
    Measurable τ ∧ ∃ f : Ω → NNReal, Measurable f ∧
      ∀ ω, τ ω ≠ ⊤ → τ ω = (f ω : WithTop NNReal) := by
  let τ : Ω → WithTop NNReal := fun ω => sInf {v : WithTop NNReal |
    ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ X t ω < 0}
  have he : τ = fun ω => ⨅ q : ℚ,
      if 0 < (q : ℝ) ∧ X (Real.toNNReal q) ω < 0 then
        (↑(Real.toNNReal q) : WithTop NNReal) else ⊤ := by
    funext ω
    exact Kyprianou.Ch04.exercise49RationalClockEqV3 (fun t => X t ω)
      (by simp [congrFun hX.start_zero ω]) (fun t => (hc ω t).1)
  have hτ : Measurable τ := by
    rw [he]
    exact Kyprianou.Ch04.exercise49RationalClockMeasurableV3 X hm
  refine ⟨hτ, fun ω => (τ ω).untopD 0, (WithTop.measurable_untopD 0).comp hτ, ?_⟩
  intro ω hn
  change τ ω = ↑((τ ω).untopD 0)
  cases hv : τ ω with
  | top => exact (hn hv).elim
  | coe t => rfl
