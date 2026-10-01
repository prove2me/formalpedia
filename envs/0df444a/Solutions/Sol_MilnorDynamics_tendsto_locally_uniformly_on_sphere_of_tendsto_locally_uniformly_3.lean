-- Prove2me | solution 3 for MilnorDynamics.tendsto_locally_uniformly_on_sphere_of_tendsto_locally_uniformly
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T21:34:55.716983+00:00
-- url     : https://prove2.me/submissions/b688d7e6-eb02-43d5-9809-dd8682886c4c

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Variant 3: the chordal radius bound is derived once with renamed bound
variables and the final step is a direct `le_of_lt` composition, avoiding any
`linarith` call on the goal. -/
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
  have hδ : (0 : ℝ) < ε / 2 := half_pos hε
  have hev : ∀ᶠ n in atTop, ∀ x ∈ K, ‖F n x - g x‖ < ε / 2 :=
    ((Metric.tendstoUniformlyOn_iff.mp (hcv K hKU hK)) (ε / 2) hδ).mono fun n hn x hx =>
      (by simpa [dist_comm, dist_eq_norm] using hn x hx)
  filter_upwards [hev] with n hn x hx
  have hstep : 2 * ‖F n x - g x‖ < 2 * (ε / 2) :=
    mul_lt_mul_of_pos_left (hn x hx) (by norm_num)
  exact lt_of_le_of_lt (key (F n x) (g x)) (by linarith)
