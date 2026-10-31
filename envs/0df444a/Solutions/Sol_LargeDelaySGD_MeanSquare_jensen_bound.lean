-- Prove2me | solution 1 for LargeDelaySGD.MeanSquare.jensen_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:52:38.772626+00:00
-- url     : https://prove2.me/submissions/b267a14e-1bbf-43e3-a0c7-8deb818c25e2

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model
import Theorems.Thm_LargeDelaySGD_MeanSquare_remark_1

open MeasureTheory ProbabilityTheory LargeDelaySGD.MeanSquare

theorem solution {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (B : ℝ) (L : NNReal)
    (hA1 : Assumption1 F μ B L) :
    ∀ x, ‖gradient (objective F μ) x‖ ^ 2 ≤ B := by
  intro x
  obtain ⟨-, hgrad, -⟩ := remark_1 μ F B L hA1
  rw [(hgrad x).gradient]
  have hm : MemLp (fun ξ => ‖stochGrad F x ξ‖) 2 μ := (hA1.memLp x).norm
  have hv := variance_nonneg (fun ξ => ‖stochGrad F x ξ‖) μ
  rw [variance_eq_sub hm] at hv
  have h1 : ‖∫ ξ, stochGrad F x ξ ∂μ‖ ≤ ∫ ξ, ‖stochGrad F x ξ‖ ∂μ :=
    norm_integral_le_integral_norm _
  have h2 := hA1.second_moment x
  have h0 : 0 ≤ ‖∫ ξ, stochGrad F x ξ ∂μ‖ := norm_nonneg _
  have h3 : (∫ ξ, (fun ξ => ‖stochGrad F x ξ‖) ξ ∂μ) ^ 2 ≤ ∫ ξ, ‖stochGrad F x ξ‖ ^ 2 ∂μ := by
    simpa [Pi.pow_apply] using hv
  simp only at h3
  nlinarith
