-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_small_time_increment_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:52:14.469055+00:00
-- url     : https://prove2.me/submissions/4b997886-18ee-47ee-8d57-d7bd865a87f2

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_compact_kernel_bound
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal
import Theorems.Thm_Kyprianou_Ch04_ito43_small_time_dyadic_limit
import Theorems.Thm_Kyprianou_Ch04_ito43_small_time_dyadic_bound
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- A measurable envelope for the short-time oscillation of a cadlag path. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (X : NNReal → Ω → ℝ)
    (hX : Measurable (fun z : NNReal × Ω => X z.1 z.2))
    (hCad : ∀ w, IsCadlag (fun t => X t w)) (T : NNReal) :
    ∃ B : ℕ → Ω → ℝ, (∀ n, Measurable (B n)) ∧
      (∀ w, Tendsto (fun n => B n w) atTop (nhds 0)) ∧
      ∀ (n : ℕ) (w : Ω) (r : NNReal), r ≤ T / (n : NNReal) → |X r w - X 0 w| ≤ B n w := by
  let d : ℕ → ℕ × ℕ → NNReal := fun n k =>
    min (T / (n : NNReal)) ((k.1 : NNReal) / 2 ^ k.2)
  let K : ℕ → (ℕ × ℕ) → Ω → ℝ := fun n k w => |X (d n k) w - X 0 w|
  let B : ℕ → Ω → ℝ := fun n w => ⨆ k, K n k w
  have hx (t : NNReal) : Measurable (X t) :=
    hX.comp (measurable_const.prodMk measurable_id)
  refine ⟨B, fun n => Measurable.iSup fun k => ((hx (d n k)).sub (hx 0)).abs,
    Kyprianou.Ch04.ito43_small_time_dyadic_limit X hX hCad T,
    Kyprianou.Ch04.ito43_small_time_dyadic_bound X hX hCad T⟩
