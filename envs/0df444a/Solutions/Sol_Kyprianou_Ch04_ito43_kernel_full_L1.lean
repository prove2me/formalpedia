-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_kernel_full_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:48:41.452659+00:00
-- url     : https://prove2.me/submissions/3500461f-2177-4263-8ca4-f0b3fca3ceb9

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_kernel_full_L1_meas
import Theorems.Thm_Kyprianou_Ch04_ito43_kernel_full_L1_limit
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Combine measurability and pathwise L1 convergence. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : Measurable (fun z : NNReal × Omega => X z.1 z.2))
    (hCad : ∀ w, IsCadlag (fun t => X t w))
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Ici (0 : ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal) :
    let B : ℕ → Omega → ℝ := fun n w =>
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      (∑ k ∈ Finset.range n,
      (∫ s in Icc ((u k : NNReal) : ℝ) ((u (k+1) : NNReal) : ℝ),
        |g (s,X (Real.toNNReal s) w) - g (s,X (u (k+1)) w)|))
    (∀ n, Measurable (B n)) ∧ ∀ w, Tendsto (fun n => B n w) atTop (nhds 0) := by
  intro B
  exact ⟨Kyprianou.Ch04.ito43_kernel_full_L1_meas P X hX hCad g hg T,
    Kyprianou.Ch04.ito43_kernel_full_L1_limit P X hX hCad g hg T⟩
