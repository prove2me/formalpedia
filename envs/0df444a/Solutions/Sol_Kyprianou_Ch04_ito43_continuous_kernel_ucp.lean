-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_continuous_kernel_ucp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:38:27.852784+00:00
-- url     : https://prove2.me/submissions/e0c2c661-e614-4f53-a49f-16ccb6c9697e

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_levy_joint_version
import Theorems.Thm_Kyprianou_Ch04_ito43_kernel_joint_ucp
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Transfer the jointly measurable cadlag kernel convergence along indistinguishable paths. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : IsLevyProcess X P)
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Ici (0 : ℝ) ×ˢ (univ : Set ℝ))) :
    ∀ (T : NNReal) (e : ℝ), 0 < e →
      Tendsto (fun n : ℕ =>
        (P {w | ∃ t : NNReal, t ≤ T ∧
          let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
          let v : ℕ → NNReal := fun k => min t (u k)
          e ≤ |(∫ s in Icc (0 : ℝ) (t : ℝ), g (s,X (Real.toNNReal s) w)) -
            ∑ k ∈ Finset.range n,
              (∫ s in Icc (v k : ℝ) (v (k+1) : ℝ), g (s,X (v (k+1)) w))|}).toReal)
        atTop (nhds 0) := by
  intro T e he
  obtain ⟨Y,hY,heq,hCad⟩ := Kyprianou.Ch04.ito43_levy_joint_version P X hX
  apply (Kyprianou.Ch04.ito43_kernel_joint_ucp P Y hY hCad g hg T e he).congr
  intro n
  congr 1
  apply measure_congr
  filter_upwards [heq] with w hw
  have hfun : (fun t => Y t w) = (fun t => X t w) := funext hw
  change (∃ t : NNReal, t ≤ T ∧ _) = (∃ t : NNReal, t ≤ T ∧ _)
  simp only [hw]
