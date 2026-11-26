-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_kernel_joint_ucp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:42:38.313025+00:00
-- url     : https://prove2.me/submissions/fe8bc228-48de-4e8f-93dc-6c6526890752
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_kernel_measurable_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_kernel_full_L1
import Theorems.Thm_Kyprianou_Ch04_ito43_kernel_stopped_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_ucp_countable_envelope
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The measurable L1 envelope and one mesh charge imply stopped uniform convergence. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : Measurable (fun z : NNReal × Omega => X z.1 z.2))
    (hCad : ∀ w, IsCadlag (fun t => X t w))
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
  obtain ⟨M,hM,hM0,hMb⟩ := Kyprianou.Ch04.ito43_kernel_measurable_bound P X hX hCad g hg T
  obtain ⟨hL,hlim⟩ := Kyprianou.Ch04.ito43_kernel_full_L1 P X hX hCad g hg T
  let L : ℕ → Omega → ℝ := fun n w =>
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    (∑ k ∈ Finset.range n,
      (∫ s in Icc ((u k : NNReal) : ℝ) ((u (k+1) : NNReal) : ℝ),
        |g (s,X (Real.toNNReal s) w) - g (s,X (u (k+1)) w)|))
  let B : ℕ → Omega → ℝ := fun n w => L (n+1) w + 2 * M w * (T : ℝ) / ((n+1 : ℕ) : ℝ)
  let E : ℕ → NNReal → Omega → ℝ := fun m t w =>
    let n := m+1
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    (∫ s in Icc (0 : ℝ) (t : ℝ), g (s,X (Real.toNNReal s) w)) -
      ∑ k ∈ Finset.range n,
        (∫ s in Icc (v k : ℝ) (v (k+1) : ℝ), g (s,X (v (k+1)) w))
  have hB (n : ℕ) : AEStronglyMeasurable (B n) P := by
    exact ((hL (n+1)).add (((measurable_const.mul hM).mul measurable_const).div measurable_const)).aestronglyMeasurable
  have hBlim : ∀ᵐ w ∂P, Tendsto (fun n => B n w) atTop (nhds 0) := by
    filter_upwards [] with w
    have H : Tendsto (fun k : ℕ => L k w + 2 * M w * (T : ℝ) / (k : ℝ))
        atTop (nhds 0) := by
      simpa only [add_zero] using (hlim w).add
        (tendsto_const_div_atTop_nhds_zero_nat (2 * M w * (T : ℝ)))
    exact (tendsto_add_atTop_iff_nat 1).mpr H
  have hbound : ∀ᵐ w ∂P, ∀ n t, t ≤ T → |E n t w| ≤ |B n w| := by
    filter_upwards [] with w
    intro n t ht
    exact (Kyprianou.Ch04.ito43_kernel_stopped_bound P X hX hCad g hg T M hM0 hMb
      (n+1) (Nat.succ_pos _) t ht w).trans (le_abs_self _)
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact Kyprianou.Ch04.ito43_ucp_countable_envelope P E B T hB hBlim hbound e he
