-- Prove2me | solution 1 for HunterPDE.Harmonic.harmonic_directional_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T15:27:24.020325+00:00
-- url     : https://prove2.me/submissions/c3d746e2-1ae8-4a0a-8f88-a53b48c594b1

import Theorems.Thm_HunterPDE_Harmonic_mean_value_property
import Theorems.Thm_HunterPDE_Harmonic_smooth_of_mean_value_property
import Theorems.Thm_HunterPDE_Harmonic_directional_derivative_mean_value
import Mathlib.Analysis.Calculus.ContDiff.Comp

open HunterPDE.Harmonic Filter Topology Laplacian
open scoped ContDiff
set_option autoImplicit false

theorem solution {n : ℕ} (hn : 0 < n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hΩ : IsOpen Ω) (hu : InnerProductSpace.HarmonicOnNhd u Ω)
    (v : EuclideanSpace ℝ (Fin n)) :
    InnerProductSpace.HarmonicOnNhd (fun y => fderiv ℝ u y v) Ω := by
  have hmv : HasMeanValueProperty Ω u :=
    fun y s hs hsub => mean_value_property hn hΩ hu hs hsub
  have hs := smooth_of_mean_value_property hΩ hu.contDiffOn.continuousOn hmv
  have hd : ContDiffOn ℝ ∞ (fun y => fderiv ℝ u y v) Ω :=
    (hs.1.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hdmv : HasMeanValueProperty Ω (fun y => fderiv ℝ u y v) :=
    fun y s hs hsub => directional_derivative_mean_value hn hΩ
      (fun z hz => (hu z hz).1.of_le (by norm_num)) hmv hs hsub v
  have hzero := (smooth_of_mean_value_property hΩ hd.continuousOn hdmv).2
  intro y hy
  refine ⟨((hd y hy).contDiffAt (hΩ.mem_nhds hy)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2), ?_⟩
  filter_upwards [hΩ.mem_nhds hy] with z hz
  exact hzero z hz
