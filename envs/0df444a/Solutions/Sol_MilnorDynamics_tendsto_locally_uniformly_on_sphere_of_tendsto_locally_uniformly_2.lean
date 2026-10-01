-- Prove2me | solution 2 for MilnorDynamics.tendsto_locally_uniformly_on_sphere_of_tendsto_locally_uniformly
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T21:34:51.756617+00:00
-- url     : https://prove2.me/submissions/0c299de2-00d0-4e36-a9cd-defe0760e475

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Variant 2: same transport, but the compact-wise characterisation is applied
as a rewrite lemma to the hypothesis and the eventual statement is consumed with
`Eventually.mono` instead of `filter_upwards`. -/
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
  have hcK : ∀ K, K ⊆ U → IsCompact K → TendstoUniformlyOn F g atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hcv
  intro K hKU hK ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  refine ((Metric.tendstoUniformlyOn_iff.mp (hcK K hKU hK)) (ε / 2) hε2).mono ?_
  intro n hn x hx
  have hd : ‖F n x - g x‖ < ε / 2 := by
    simpa [dist_comm, dist_eq_norm] using hn x hx
  exact lt_of_le_of_lt (key (F n x) (g x)) (by linarith)
