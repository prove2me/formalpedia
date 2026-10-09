-- Prove2me | solution 1 for HunterPDE.Harmonic.laplacian_eq_zero_of_C2_mean_value
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T11:16:00.998982+00:00
-- url     : https://prove2.me/submissions/4ce44ebe-7470-4016-9616-a7425a89fc3e

import Theorems.Thm_HunterPDE_Harmonic_sphereAverage_radial_eq_ball_laplacian
import Theorems.Thm_HunterPDE_Harmonic_hasDerivAt_sphereAverage_radial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open MeasureTheory Set Metric Filter Laplacian HunterPDE.Harmonic
open scoped Topology
set_option autoImplicit false

theorem solution {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hmv : HasMeanValueProperty Ω u) :
    ∀ x ∈ Ω, Δ u x = 0 := by
  have hc : ContinuousOn (Δ u) Ω := by
    intro x hx
    simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
      (EuclideanSpace.basisFun (Fin n) ℝ)]
    apply ContinuousAt.continuousWithinAt
    apply tendsto_finsetSum
    intro i hi
    exact (continuous_eval_const _).continuousAt.comp
      ((hu.contDiffAt (hΩ.mem_nhds hx)).continuousAt_iteratedFDeriv (by norm_num))
  have hav : ∀ x r, 0 < r → closedBall x (2 * r) ⊆ Ω → (⨍ y in ball x r, Δ u y) = 0 := by
    intro x r hr hsub
    have hsubr : closedBall x r ⊆ Ω :=
      (closedBall_subset_closedBall (by linarith : r ≤ 2 * r)).trans hsub
    have heq : sphereAverage u x =ᶠ[𝓝 r] fun _ => u x := by
      filter_upwards [Ioo_mem_nhds hr (by linarith : r < 2 * r)] with t ht
      exact (hmv x t ht.1 ((closedBall_subset_closedBall ht.2.le).trans hsub)).2.symm
    have hz := (hasDerivAt_const r (u x)).congr_of_eventuallyEq heq
    have hd := hasDerivAt_sphereAverage_radial hn hr
      (fun y hy => (hu.contDiffAt (hΩ.mem_nhds (hsubr hy))).of_le (by norm_num))
    have hflux := sphereAverage_radial_eq_ball_laplacian hn hr
      (fun y hy => hu.contDiffAt (hΩ.mem_nhds (hsubr hy)))
    have hzero := hd.unique hz
    rw [hzero] at hflux
    exact (mul_eq_zero.mp hflux.symm).resolve_left (div_ne_zero hr.ne' (Nat.cast_ne_zero.mpr hn.ne'))
  have nonpos : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ), ContinuousOn f Ω →
      (∀ x r, 0 < r → closedBall x (2 * r) ⊆ Ω → (⨍ y in ball x r, f y) = 0) →
      ∀ x ∈ Ω, f x ≤ 0 := by
    intro f hf hfav x hx
    by_contra hnpos
    have hp : 0 < f x := lt_of_not_ge hnpos
    have hnh : {y | f x / 2 < f y} ∩ Ω ∈ 𝓝 x :=
      inter_mem ((hf x hx).continuousAt (hΩ.mem_nhds hx) |>.preimage_mem_nhds
        (Ioi_mem_nhds (by linarith : f x / 2 < f x))) (hΩ.mem_nhds hx)
    obtain ⟨R, hR, hsubR⟩ := nhds_basis_closedBall.mem_iff.mp hnh
    let r := R / 2
    have hr : 0 < r := half_pos hR
    have h2r : 2 * r = R := by dsimp [r]; ring
    have hsub : closedBall x r ⊆ {y | f x / 2 < f y} ∩ Ω :=
      (closedBall_subset_closedBall (by dsimp [r]; linarith)).trans hsubR
    have hΩr : closedBall x r ⊆ Ω := fun y hy => (hsub hy).2
    have hi : IntegrableOn f (closedBall x r) volume :=
      (hf.mono hΩr).integrableOn_compact (isCompact_closedBall x r)
    have hb := hi.mono_set ball_subset_closedBall
    have hineq := setIntegral_ge_of_const_le_real measurableSet_ball
      (measure_ball_lt_top (μ := volume) (x := x) (r := r)).ne
      (fun y hy => (hsub (ball_subset_closedBall hy)).1.le) hb
    have ha := hfav x r hr (by rw [h2r]; exact fun y hy => (hsubR hy).2)
    have hz := congrArg (fun a : ℝ => (volume.real (ball x r)) • a) ha
    rw [measure_smul_setAverage _ (measure_ball_lt_top (μ := volume) (x := x) (r := r)).ne,
      smul_zero] at hz
    rw [hz] at hineq
    have hv : 0 < volume.real (ball x r) := ENNReal.toReal_pos
      (measure_ball_pos volume x hr).ne' (measure_ball_lt_top (μ := volume) (x := x) (r := r)).ne
    have := mul_pos (half_pos hp) hv
    linarith
  intro x hx
  apply le_antisymm (nonpos (Δ u) hc hav x hx)
  have hneg := nonpos (fun y => -(Δ u y)) hc.neg
    (fun y r hr hs => by rw [average_neg, hav y r hr hs, neg_zero]) x hx
  linarith
