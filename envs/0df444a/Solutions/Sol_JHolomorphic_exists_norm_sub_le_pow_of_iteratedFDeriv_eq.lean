-- Prove2me | solution 1 for JHolomorphic.exists_norm_sub_le_pow_of_iteratedFDeriv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T14:39:54.905404+00:00
-- url     : https://prove2.me/submissions/981f21ae-7814-47af-a722-27b63bd1d646

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic



namespace JHolomorphic

open Metric Filter Topology
open scoped ContDiff

/-- Two maps that are `C^∞` on a disc around `0` and whose derivatives of all orders agree at `0`
differ by at most `C ‖z‖ ^ N` near `0`, for every `N`. -/
theorem exists_norm_sub_le_pow_of_iteratedFDeriv_eq_aux {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (r : ℝ) (hr : 0 < r) (u v : ℂ → F)
    (hu : ContDiffOn ℝ ∞ u (ball 0 r)) (hv : ContDiffOn ℝ ∞ v (ball 0 r))
    (hD : ∀ m : ℕ, iteratedFDeriv ℝ m u 0 = iteratedFDeriv ℝ m v 0) :
    ∀ N : ℕ, ∃ C δ : ℝ, 0 < δ ∧ ∀ z ∈ ball (0 : ℂ) δ, ‖u z - v z‖ ≤ C * ‖z‖ ^ N := by
  intro N
  induction N generalizing F with
  | zero =>
    have h0 : u 0 = v 0 := by
      have := congrArg (fun T => T (0 : Fin 0 → ℂ)) (hD 0)
      simpa using this
    have hc : ContinuousAt (fun z => u z - v z) 0 :=
      ((hu.continuousOn.sub hv.continuousOn).continuousAt (ball_mem_nhds 0 hr))
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hc 1 one_pos
    refine ⟨1, δ, hδ, fun z hz => ?_⟩
    have := hδ' (by simpa using hz)
    rw [h0, sub_self, dist_zero_right] at this
    simpa using this.le
  | succ N ih =>
    have h0 : u 0 = v 0 := by
      have := congrArg (fun T => T (0 : Fin 0 → ℂ)) (hD 0)
      simpa using this
    have hu' : ContDiffOn ℝ ∞ (fun y => fderiv ℝ u y) (ball 0 r) :=
      hu.fderiv_of_isOpen isOpen_ball (by simp)
    have hv' : ContDiffOn ℝ ∞ (fun y => fderiv ℝ v y) (ball 0 r) :=
      hv.fderiv_of_isOpen isOpen_ball (by simp)
    have hD' : ∀ m : ℕ, iteratedFDeriv ℝ m (fun y => fderiv ℝ u y) 0 =
        iteratedFDeriv ℝ m (fun y => fderiv ℝ v y) 0 := by
      intro m
      ext p w
      have := congrArg (fun T => T (Fin.snoc p w)) (hD (m + 1))
      simp only [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last] at this
      exact this
    obtain ⟨C, δ, hδ, hC⟩ := ih _ _ hu' hv' hD'
    set C' := max C 0
    refine ⟨C', min δ r, lt_min hδ hr, fun z hz => ?_⟩
    have hzδ : ‖z‖ < min δ r := by simpa using hz
    have hs : closedBall (0 : ℂ) ‖z‖ ⊆ ball 0 (min δ r) := closedBall_subset_ball hzδ
    have hsr : closedBall (0 : ℂ) ‖z‖ ⊆ ball 0 r :=
      hs.trans (ball_subset_ball (min_le_right _ _))
    have hsδ : closedBall (0 : ℂ) ‖z‖ ⊆ ball 0 δ :=
      hs.trans (ball_subset_ball (min_le_left _ _))
    have hdu : ∀ y ∈ closedBall (0 : ℂ) ‖z‖, DifferentiableAt ℝ u y := fun y hy =>
      (hu.differentiableOn (by simp) y (hsr hy)).differentiableAt
        (isOpen_ball.mem_nhds (hsr hy))
    have hdv : ∀ y ∈ closedBall (0 : ℂ) ‖z‖, DifferentiableAt ℝ v y := fun y hy =>
      (hv.differentiableOn (by simp) y (hsr hy)).differentiableAt
        (isOpen_ball.mem_nhds (hsr hy))
    have hbound : ∀ y ∈ closedBall (0 : ℂ) ‖z‖,
        ‖fderiv ℝ (fun x => u x - v x) y‖ ≤ C' * ‖z‖ ^ N := by
      intro y hy
      rw [fderiv_fun_sub (hdu y hy) (hdv y hy)]
      have hy' : ‖y‖ ≤ ‖z‖ := by simpa using hy
      calc _ ≤ C * ‖y‖ ^ N := hC y (hsδ hy)
        _ ≤ C' * ‖y‖ ^ N := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ C' * ‖z‖ ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy' N) (le_max_right _ _)
    have := (convex_closedBall (0 : ℂ) ‖z‖).norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => (hdu y hy).sub (hdv y hy)) hbound (mem_closedBall_self (norm_nonneg z))
      (y := z) (by simp)
    simp only [Pi.sub_apply, h0, sub_self, sub_zero] at this
    calc _ ≤ C' * ‖z‖ ^ N * ‖z‖ := this
      _ = C' * ‖z‖ ^ (N + 1) := by ring

end JHolomorphic

open JHolomorphic

open Metric Filter Topology
open scoped ContDiff

theorem solution {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (r : ℝ) (hr : 0 < r) (u v : ℂ → F)
    (hu : ContDiffOn ℝ ∞ u (ball 0 r)) (hv : ContDiffOn ℝ ∞ v (ball 0 r))
    (hD : ∀ m : ℕ, iteratedFDeriv ℝ m u 0 = iteratedFDeriv ℝ m v 0) :
    ∀ N : ℕ, ∃ C δ : ℝ, 0 < δ ∧ ∀ z ∈ ball (0 : ℂ) δ, ‖u z - v z‖ ≤ C * ‖z‖ ^ N :=
  exists_norm_sub_le_pow_of_iteratedFDeriv_eq_aux r hr u v hu hv hD
