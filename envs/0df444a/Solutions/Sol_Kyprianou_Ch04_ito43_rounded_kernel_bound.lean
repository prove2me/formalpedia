-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_rounded_kernel_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:58:34.067751+00:00
-- url     : https://prove2.me/submissions/040686d6-c8c7-4297-8bf3-e22fcb83f140

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
    (hg : ContinuousOn g (Ici (0 : ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal) (w : Omega) (hT' : 0 < (T : ℝ)) (M : ℝ)
    (hb : ∀ s ∈ Icc (0 : ℝ) (T : ℝ), ∀ r : NNReal, r ≤ T → |g (s,X r w)| ≤ M) :
    let R : ℕ → ℝ → ℝ := fun n s => (T : ℝ) * (Nat.ceil (s * (n : ℝ) / (T : ℝ)) : ℝ) / (n : ℝ)
    let F : ℝ → ℝ → ℝ := fun s r =>
      |g (s,X (Real.toNNReal s) w) - g (s,X (Real.toNNReal r) w)|
    let μ := volume.restrict (Icc (0 : ℝ) (T : ℝ))
    ∀ n : ℕ, 0 < n → ∀ᵐ s ∂μ, ‖F s (R n s)‖ ≤ 2*M := by
  intro R F μ
  have hFb (n : ℕ) (hn : 0 < n) : ∀ᵐ s ∂μ, ‖F s (R n s)‖ ≤ 2*M := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with s hs
    have hround := Kyprianou.Ch04.ito43_ceiling_grid (T : ℝ) s hT' hs n hn
    have h1 := hb s hs (Real.toNNReal s) ((Real.toNNReal_le_iff_le_coe).mpr hs.2)
    have h2 := hb s hs (Real.toNNReal (R n s)) ((Real.toNNReal_le_iff_le_coe).mpr hround.2.1)
    dsimp [F]
    rw [abs_abs]
    have htri := abs_sub_le (g (s,X (Real.toNNReal s) w)) 0 (g (s,X (Real.toNNReal (R n s)) w))
    simp only [sub_zero,zero_sub,abs_neg] at htri
    linarith
  exact hFb
