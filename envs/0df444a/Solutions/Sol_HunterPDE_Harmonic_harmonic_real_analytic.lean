-- Prove2me | solution 1 for HunterPDE.Harmonic.harmonic_real_analytic
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T16:31:43.993126+00:00
-- url     : https://prove2.me/submissions/464873a6-715c-41c8-a35d-44ca14a605a3

import Theorems.Thm_RealAnalytic_analyticAt_of_multiDeriv_bound
import Theorems.Thm_HunterPDE_Harmonic_harmonic_higher_derivative_estimate
import Theorems.Thm_HunterPDE_Harmonic_mean_value_property
import Theorems.Thm_HunterPDE_Harmonic_smooth_of_mean_value_property
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open HunterPDE.Harmonic Filter Topology Metric
open scoped ContDiff
set_option autoImplicit false

theorem solution {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω)
    (hu : InnerProductSpace.HarmonicOnNhd u Ω) : AnalyticOnNhd ℝ u Ω := by
  classical
  by_cases hn : n = 0
  · subst n
    have heq : u = fun _ => u 0 := funext fun y => congrArg u (Subsingleton.elim y 0)
    rw [heq]
    exact analyticOnNhd_const
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hmv : HasMeanValueProperty Ω u := fun y s hs hsub =>
    mean_value_property hnpos hΩ hu hs hsub
  have hsmooth := (smooth_of_mean_value_property hΩ hu.continuousOn hmv).1
  intro x hx
  obtain ⟨R, hR, hsub⟩ := nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hx)
  obtain ⟨M, hM⟩ := (isCompact_closedBall x R).bddAbove_image
    ((hu.continuousOn.mono hsub).abs)
  have hMb : ∀ y ∈ closedBall x R, |u y| ≤ M := fun y hy =>
    hM (Set.mem_image_of_mem _ hy)
  have hMpos : 0 ≤ M := (abs_nonneg (u x)).trans (hMb x (mem_closedBall_self hR.le))
  have hr : 0 < R / 2 := by positivity
  have hsmall : ball x (R / 2) ⊆ Ω :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hsub
  apply RealAnalytic.analyticAt_of_multiDeriv_bound hr hMpos
    (show 0 < (n : ℝ) * Real.exp 1 / (R / 2) by positivity) (hsmooth.mono hsmall)
  intro y hy α k hk hk1
  have hshift : closedBall y (R / 2) ⊆ closedBall x R := by
    apply closedBall_subset_closedBall'
    have hd : dist y x < R / 2 := hy
    linarith
  have hest := harmonic_higher_derivative_estimate hΩ hu hr (hshift.trans hsub)
    α k hk hk1 (fun z hz => hMb z (hshift hz))
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hepow : Real.exp 1 ^ (k - 1) ≤ Real.exp 1 ^ k :=
    pow_le_pow_right₀ he (Nat.sub_le k 1)
  calc
    |HunterPDE.Shared.multiDeriv u α y| ≤
        ((n : ℝ) ^ k * Real.exp 1 ^ (k - 1) * (k.factorial : ℝ) / (R / 2) ^ k) * M := hest
    _ ≤ ((n : ℝ) ^ k * Real.exp 1 ^ k * (k.factorial : ℝ) / (R / 2) ^ k) * M := by
      gcongr
    _ = M * ((n : ℝ) * Real.exp 1 / (R / 2)) ^ k * (k.factorial : ℝ) := by
      simp only [div_pow, mul_pow]
      ring
