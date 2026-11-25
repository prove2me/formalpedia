-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42GridDCTIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T16:04:42.725798+00:00
-- url     : https://prove2.me/submissions/1f25e212-39cb-4024-b32b-e69959573670

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_uniform_floor_samples_converge_from_left
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open ProbabilityTheory Set Topology
open scoped Topology
open Kyprianou.Ch04

theorem solution
    (t : NNReal) (ht : 0 < t) (U g : NNReal → ℝ)
    (K : NNReal) (hU : LipschitzWith K U)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ s : NNReal, s ≤ t → ‖g s‖ ≤ C)
    (hpoint : ∀ᵐ s ∂(volume.restrict (Icc 0 (t : ℝ))),
      Tendsto (fun n : ℕ => g (((t : ℝ) *
        (⌊(s / (t : ℝ)) * ((n : ℝ) + 2)⌋₊ : ℝ)) /
        ((n : ℝ) + 2)).toNNReal) atTop (nhds (g s.toNNReal))) :
    let T : ℝ := t
    let V : ℝ → ℝ := fun s => U s.toNNReal
    let D : ℝ → ℝ := deriv V
    let q : ℕ → ℕ → ℝ := fun n i => T * (i : ℝ) / ((n : ℝ) + 2)
    let j : ℕ → ℝ → ℕ := fun n s => ⌊(s / T) * ((n : ℝ) + 2)⌋₊
    let F : ℕ → ℝ → ℝ := fun n s => g (q n (j n s)).toNNReal * D s
    Tendsto (fun n => ∫ s in Icc 0 T, F n s) atTop
      (nhds (∫ s in Icc 0 T, g s.toNNReal * D s)) := by
  classical
  intro T V D q j F
  have hT : 0 < T := ht
  have hLip : LipschitzWith K V := by
    simpa [V, Function.comp_def] using hU.comp Real.lipschitzWith_toNNReal
  have hDmeas : Measurable D := measurable_deriv V
  have hDbd (s : ℝ) : ‖D s‖ ≤ (K : ℝ) := norm_deriv_le_of_lipschitz hLip
  have hsample (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 T) :
      (q n (j n s)).toNNReal ≤ t := by
    have h := (AvramDividend.Classical.avram_bvb_b21_original_uniform_floor_samples_converge_from_left
      T s hT hs.1).1 n
    exact (Real.toNNReal_le_toNNReal (h.trans hs.2)).trans_eq (Real.toNNReal_coe : (t : ℝ).toNNReal = t)
  have hFmeas (n : ℕ) : Measurable (F n) := by
    have hj : Measurable (j n) := by
      dsimp [j]
      exact ((measurable_id.div_const T).mul_const ((n : ℝ) + 2)).nat_floor
    exact ((measurable_of_countable (fun i : ℕ => g (q n i).toNNReal)).comp hj).mul hDmeas
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hconst : Integrable (fun _ : ℝ => C * (K : ℝ)) μ :=
    integrableOn_const (isCompact_Icc.measure_lt_top.ne)
  have hFbd (n : ℕ) : ∀ᵐ s ∂μ, ‖F n s‖ ≤ C * (K : ℝ) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with s hs
    rw [show F n s = g (q n (j n s)).toNNReal * D s from rfl, norm_mul]
    exact mul_le_mul (hg _ (hsample n s hs)) (hDbd s) (norm_nonneg _) hC
  change Tendsto (fun n => ∫ s, F n s ∂μ) atTop
    (nhds (∫ s, g s.toNNReal * D s ∂μ))
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => C * (K : ℝ))
    (fun n => (hFmeas n).aestronglyMeasurable) hconst hFbd
  filter_upwards [hpoint] with s hs
  exact hs.mul tendsto_const_nhds
