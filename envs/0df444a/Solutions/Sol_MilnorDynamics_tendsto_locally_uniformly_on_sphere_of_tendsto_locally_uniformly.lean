-- Prove2me | solution 1 for MilnorDynamics.tendsto_locally_uniformly_on_sphere_of_tendsto_locally_uniformly
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T21:34:47.289988+00:00
-- url     : https://prove2.me/submissions/ea9cdf40-f549-4736-be47-249a488a038b

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Variant 1: compact-wise Euclidean convergence via the `isCompact`
characterisation, then the chordal bound `sigma <= 2 * dist`. -/
theorem solution (U : Set ℂ) (hU : IsOpen U) (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (hcv : TendstoLocallyUniformlyOn F g atTop U) :
    TendstoLocallyUniformlyOnSphere (fun n z => ((F n z : ℂ) : OnePoint ℂ))
      (fun z => ((g z : ℂ) : OnePoint ℂ)) U := by
  have key : ∀ w c : ℂ, chordalDist (w : OnePoint ℂ) (c : OnePoint ℂ) ≤ 2 * ‖w - c‖ := by
    intro w c
    show 2 * ‖w - c‖ / (Real.sqrt (1 + ‖w‖ ^ 2) * Real.sqrt (1 + ‖c‖ ^ 2)) ≤ 2 * ‖w - c‖
    apply div_le_self (by positivity)
    have h1 : 1 ≤ Real.sqrt (1 + ‖w‖ ^ 2) := Real.one_le_sqrt.mpr (by nlinarith [norm_nonneg w])
    have h2 : 1 ≤ Real.sqrt (1 + ‖c‖ ^ 2) := Real.one_le_sqrt.mpr (by nlinarith [norm_nonneg c])
    exact one_le_mul_of_one_le_of_one_le h1 h2
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU] at hcv
  intro K hKU hK ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hcv K hKU hK)) (ε / 2) hε2] with n hn
  intro x hx
  have hd : ‖F n x - g x‖ < ε / 2 := by
    simpa [dist_comm, dist_eq_norm] using hn x hx
  calc chordalDist ((F n x : ℂ) : OnePoint ℂ) ((g x : ℂ) : OnePoint ℂ)
      ≤ 2 * ‖F n x - g x‖ := key (F n x) (g x)
    _ < ε := by linarith
