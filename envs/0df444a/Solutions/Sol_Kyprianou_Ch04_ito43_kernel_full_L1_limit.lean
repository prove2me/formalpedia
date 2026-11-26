-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_kernel_full_L1_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:01:04.572223+00:00
-- url     : https://prove2.me/submissions/406382c0-f334-4874-a961-3a9e8cd9d59b

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_full_cell_rounding_integral
import Theorems.Thm_Kyprianou_Ch04_ito43_ceiling_grid_path_limit
import Theorems.Thm_Kyprianou_Ch04_ito43_ceiling_grid
import Theorems.Thm_Kyprianou_Ch04_ito43_compact_kernel_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_rounded_kernel_meas
import Theorems.Thm_Kyprianou_Ch04_ito43_rounded_kernel_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_rounded_kernel_pointwise
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

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
    ∀ w, Tendsto (fun n => B n w) atTop (nhds 0) := by
  intro B w
  by_cases hT : T = 0
  · simpa [B,hT] using (tendsto_const_nhds (x := (0 : ℝ)) : Tendsto (fun _ : ℕ => 0) atTop (nhds 0))
  have hT' : 0 < (T : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hT)
  let R : ℕ → ℝ → ℝ := fun n s => (T : ℝ) * (Nat.ceil (s * (n : ℝ) / (T : ℝ)) : ℝ) / (n : ℝ)
  let F : ℝ → ℝ → ℝ := fun s r =>
    |g (s,X (Real.toNNReal s) w) - g (s,X (Real.toNNReal r) w)|
  let μ := volume.restrict (Icc (0 : ℝ) (T : ℝ))
  obtain ⟨M,hM,hb⟩ := Kyprianou.Ch04.ito43_compact_kernel_bound (fun t => X t w) (hCad w) g hg T
  have hFm := Kyprianou.Ch04.ito43_rounded_kernel_meas P X hX hCad g hg T w
  have hFb := Kyprianou.Ch04.ito43_rounded_kernel_bound P X hX hCad g hg T w hT' M hb
  have hFl := Kyprianou.Ch04.ito43_rounded_kernel_pointwise P X hX hCad g hg T w hT'
  have hD := tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (F := fun n s => F s (R n s)) (f := fun _ => (0 : ℝ)) (fun _ => 2*M)
    (Eventually.of_forall hFm) ((eventually_gt_atTop (0 : ℕ)).mono hFb)
    (integrable_const _) hFl
  simp only [integral_zero] at hD
  apply hD.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hFi : IntegrableOn (fun s => F s (R n s)) (Icc 0 (T : ℝ)) :=
    (integrable_const (2*M)).mono (hFm n) (by
      filter_upwards [hFb n hn] with s hs
      rw [show ‖(2*M : ℝ)‖ = 2*M from Real.norm_of_nonneg (by positivity)]
      exact hs)
  have h := Kyprianou.Ch04.ito43_full_cell_rounding_integral (T : ℝ) hT' n hn F hFi
  have he (k : ℕ) : ((T : ℝ)*(k : ℝ)/(n : ℝ)).toNNReal = T*(k : NNReal)/(n : NNReal) := by
    rw [← NNReal.coe_natCast, ← NNReal.coe_mul, ← NNReal.coe_natCast, ← NNReal.coe_div, Real.toNNReal_coe]
  simpa only [F,R,B,μ,NNReal.coe_mul,NNReal.coe_div,NNReal.coe_natCast,he] using h.symm
