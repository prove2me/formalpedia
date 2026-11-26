-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_rounded_kernel_meas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:58:33.740878+00:00
-- url     : https://prove2.me/submissions/93875286-3de1-4de8-96a3-b24847726da3

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_ceiling_grid_path_limit
import Theorems.Thm_Kyprianou_Ch04_ito43_ceiling_grid
import Theorems.Thm_Kyprianou_Ch04_ito43_compact_kernel_bound
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : Measurable (fun z : NNReal × Omega => X z.1 z.2))
    (hCad : ∀ w, IsCadlag (fun t => X t w))
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Ici (0 : ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal) (w : Omega) :
    let R : ℕ → ℝ → ℝ := fun n s => (T : ℝ) * (Nat.ceil (s * (n : ℝ) / (T : ℝ)) : ℝ) / (n : ℝ)
    let F : ℝ → ℝ → ℝ := fun s r =>
      |g (s,X (Real.toNNReal s) w) - g (s,X (Real.toNNReal r) w)|
    let μ := volume.restrict (Icc (0 : ℝ) (T : ℝ))
    ∀ n : ℕ, AEStronglyMeasurable (fun s => F s (R n s)) μ := by
  intro R F μ
  have hg0 : Continuous (fun z : ℝ × ℝ => g (max 0 z.1,z.2)) :=
    hg.comp_continuous ((continuous_const.max continuous_fst).prodMk continuous_snd)
      (fun z => ⟨show 0 ≤ max 0 z.1 from le_max_left _ _,mem_univ _⟩)
  have hXm : Measurable (fun s : ℝ => X (Real.toNNReal s) w) :=
    hX.comp (measurable_real_toNNReal.prodMk measurable_const)
  have hR (n : ℕ) : Measurable (R n) := by
    dsimp [R]
    have hc : Measurable (fun k : ℕ => (k : ℝ)) := measurable_of_countable _
    exact (measurable_const.mul (hc.comp ((measurable_id.mul measurable_const).div_const _).nat_ceil)).div_const _
  have hFm (n : ℕ) : AEStronglyMeasurable (fun s => F s (R n s)) μ := by
    have h1 : Measurable (fun s : ℝ => g (max 0 s,X (Real.toNNReal s) w)) :=
      hg0.measurable.comp (measurable_id.prodMk hXm)
    have h2 : Measurable (fun s : ℝ => g (max 0 s,X (Real.toNNReal (R n s)) w)) :=
      hg0.measurable.comp (measurable_id.prodMk (hXm.comp (hR n)))
    apply ((h1.sub h2).abs).aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with s hs
    simp [F,max_eq_right hs.1]
  exact hFm
