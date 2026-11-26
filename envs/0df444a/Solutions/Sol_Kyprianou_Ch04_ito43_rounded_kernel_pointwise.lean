-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_rounded_kernel_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:58:33.819689+00:00
-- url     : https://prove2.me/submissions/1cad8422-646c-43d8-9274-602865c0f129

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
    (hg : ContinuousOn g (Ici (0 : ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal) (w : Omega) (hT' : 0 < (T : ℝ)) :
    let R : ℕ → ℝ → ℝ := fun n s => (T : ℝ) * (Nat.ceil (s * (n : ℝ) / (T : ℝ)) : ℝ) / (n : ℝ)
    let F : ℝ → ℝ → ℝ := fun s r =>
      |g (s,X (Real.toNNReal s) w) - g (s,X (Real.toNNReal r) w)|
    let μ := volume.restrict (Icc (0 : ℝ) (T : ℝ))
    ∀ᵐ s ∂μ, Tendsto (fun n => F s (R n s)) atTop (nhds 0) := by
  intro R F μ
  have hg0 : Continuous (fun z : ℝ × ℝ => g (max 0 z.1,z.2)) :=
    hg.comp_continuous ((continuous_const.max continuous_fst).prodMk continuous_snd)
      (fun z => ⟨show 0 ≤ max 0 z.1 from le_max_left _ _,mem_univ _⟩)
  have hFl : ∀ᵐ s ∂μ, Tendsto (fun n => F s (R n s)) atTop (nhds 0) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with s hs
    have hxrc : ContinuousWithinAt (fun r : ℝ => X (Real.toNNReal r) w) (Ici s) s :=
      (hCad w (Real.toNNReal s)).1.comp continuous_real_toNNReal.continuousWithinAt
        (fun r hr => Real.toNNReal_mono hr)
    have hpath := Kyprianou.Ch04.ito43_ceiling_grid_path_limit
      (fun r => X (Real.toNNReal r) w) (T : ℝ) s hT' hs hxrc
    have hG : Tendsto (fun n => g (s,X (Real.toNNReal (R n s)) w)) atTop
        (nhds (g (s,X (Real.toNNReal s) w))) := by
      have H := (hg0.tendsto (s,X (Real.toNNReal s) w)).comp
        (tendsto_const_nhds.prodMk_nhds hpath)
      change Tendsto (fun n => g (max 0 s,X (Real.toNNReal (R n s)) w)) atTop
        (nhds (g (max 0 s,X (Real.toNNReal s) w))) at H
      simpa only [max_eq_right hs.1] using H
    simpa only [F,sub_self,abs_zero] using
      ((tendsto_const_nhds (x := g (s,X (Real.toNNReal s) w))).sub hG).abs
  exact hFl
