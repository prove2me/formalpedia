-- Prove2me | solution 1 for HunterPDE.Harmonic.smooth_of_mean_value_property
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T11:16:40.73056+00:00
-- url     : https://prove2.me/submissions/250d4c8c-adb1-496f-ad5d-ea04a051bc56

import Theorems.Thm_MeasureTheory_radial_convolution_eq_of_sphere_average
import Theorems.Thm_MeasureTheory_exists_smooth_radial_probability_kernel
import Theorems.Thm_HunterPDE_Harmonic_laplacian_eq_zero_of_C2_mean_value

open MeasureTheory Set Metric Filter Laplacian HunterPDE.Harmonic
open scoped Topology Convolution ContDiff
set_option autoImplicit false

theorem solution {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    (hmv : HasMeanValueProperty Ω u) :
    ContDiffOn ℝ ∞ u Ω ∧ ∀ x ∈ Ω, Δ u x = 0 := by
  classical
  by_cases hn : 0 < n
  · have hs : ContDiffOn ℝ ∞ u Ω := by
      intro x hx
      obtain ⟨R, hR, hsub⟩ := nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hx)
      have hε : 0 < R / 4 := by positivity
      obtain ⟨k, κ, hk, hkc, hkr, hks, hki⟩ :=
        MeasureTheory.exists_smooth_radial_probability_kernel (n := n) hε
      let g := (closedBall x R).indicator u
      have hg : Integrable g :=
        (integrable_indicator_iff measurableSet_closedBall).mpr
          ((hu.mono hsub).integrableOn_compact (isCompact_closedBall x R))
      have hconv : ContDiff ℝ ∞ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) :=
        hkc.contDiff_convolution_left _ hk hg.locallyIntegrable
      have heq : (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) =ᶠ[𝓝 x] u := by
        filter_upwards [ball_mem_nhds x hε] with z hz
        have hzx : dist z x < R / 4 := mem_ball.mp hz
        have hgz : g z = u z := indicator_of_mem
          (show z ∈ closedBall x R from mem_closedBall.mpr (by linarith)) u
        rw [MeasureTheory.radial_convolution_eq_of_sphere_average hn hk.continuous hkc
          hkr hks hki hg.locallyIntegrable z, hgz]
        intro t ht htε
        have hzt : closedBall z t ⊆ Ω := by
          intro y hy
          apply hsub
          apply mem_closedBall.mpr
          calc
            dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
            _ ≤ t + dist z x := by gcongr; exact mem_closedBall.mp hy
            _ ≤ R := by linarith
        have hsg : sphereAverage g z t = sphereAverage u z t := by
          unfold sphereAverage
          apply integral_congr_ae
          apply Eventually.of_forall
          intro w
          have hd : dist (z + t • w.1) z = t := by
            simp [dist_eq_norm, norm_smul, mem_sphere_zero_iff_norm.mp w.2, abs_of_pos ht]
          apply indicator_of_mem
          apply mem_closedBall.mpr
          calc
            dist (z + t • w.1) x ≤ dist (z + t • w.1) z + dist z x := dist_triangle _ _ _
            _ ≤ R := by rw [hd]; linarith
        change sphereAverage g z t = g z
        rw [hsg, hgz]
        exact (hmv z t ht hzt).2.symm
      exact (hconv.contDiffAt.congr_of_eventuallyEq heq.symm).contDiffWithinAt
    exact ⟨hs, HunterPDE.Harmonic.laplacian_eq_zero_of_C2_mean_value hn hΩ
      (contDiffOn_infty.mp hs 2) hmv⟩
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have heq : u = fun _ => u 0 := funext fun y => congrArg u (Subsingleton.elim y 0)
    rw [heq]
    exact ⟨contDiffOn_const, fun x _ => by simp⟩
