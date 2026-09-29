-- Prove2me | solution 1 for KeatingSnaith.keating_snaith_joint_clt
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T04:55:29.706747+00:00
-- url     : https://prove2.me/submissions/efad306a-41a4-41ea-95e4-4f7f66056565

import Mathlib
import Definitions.Def_keating_snaith_cue

/-! Disproof of 6cf71ae1 `KeatingSnaith.keating_snaith_joint_clt`.

The statement quantifies over all `a c u v : ℝ` with no hypotheses `a ≤ c`, `u ≤ v`. For
`a = u = 1`, `c = v = 0` both sets `Set.Icc 1 0` are empty, so the product of indicators vanishes
and every `cueAverage` in the sequence is `0`. But `gaussianMass 1 0` is the oriented interval
integral `(√(2π))⁻¹ * ∫ x in 1..0, exp (-x²/2)`, which is strictly negative, so the claimed limit
`gaussianMass 1 0 * gaussianMass 1 0` is strictly positive. The constant sequence `0` cannot
converge to it. -/

set_option autoImplicit false

open Finset MeasureTheory Filter Topology
open scoped Real

theorem dpKS_6cf7_gm_neg : KeatingSnaith.gaussianMass 1 0 < 0 := by
  unfold KeatingSnaith.gaussianMass
  have hpos : 0 < ∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2 / 2) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · exact (by fun_prop : Continuous fun x : ℝ => Real.exp (-x ^ 2 / 2)).intervalIntegrable _ _
    · intro x _
      exact Real.exp_pos _
    · norm_num
  rw [intervalIntegral.integral_symm]
  have hs : 0 < (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  nlinarith

theorem dpKS_6cf7_avg_zero (N : ℕ) (g h : (Fin N → ℝ) → ℝ) :
    KeatingSnaith.cueAverage N
      (fun θ => Set.indicator (Set.Icc (1 : ℝ) 0) (fun _ => (1 : ℝ)) (g θ) *
        Set.indicator (Set.Icc (1 : ℝ) 0) (fun _ => (1 : ℝ)) (h θ)) = 0 := by
  have hE : Set.Icc (1 : ℝ) 0 = ∅ := Set.Icc_eq_empty (by norm_num)
  rw [hE]
  simp [KeatingSnaith.cueAverage]

open KeatingSnaith in
theorem solution : ¬ (∀ (a c u v : ℝ),
    Tendsto (fun N : ℕ => cueAverage N (fun θ =>
        Set.indicator (Set.Icc a c) (fun _ => (1 : ℝ)) (logAbsZ N θ / cltScale N) *
          Set.indicator (Set.Icc u v) (fun _ => (1 : ℝ)) (imLogZ N θ / cltScale N)))
      atTop (𝓝 (gaussianMass a c * gaussianMass u v))) := by
  intro H
  have h := H 1 0 1 0
  have hz : (fun N : ℕ => cueAverage N (fun θ =>
      Set.indicator (Set.Icc (1 : ℝ) 0) (fun _ => (1 : ℝ)) (logAbsZ N θ / cltScale N) *
        Set.indicator (Set.Icc (1 : ℝ) 0) (fun _ => (1 : ℝ)) (imLogZ N θ / cltScale N)))
      = fun _ => (0 : ℝ) := by
    funext N
    exact dpKS_6cf7_avg_zero N _ _
  rw [hz] at h
  have h0 := tendsto_nhds_unique tendsto_const_nhds h
  have hp : 0 < gaussianMass 1 0 * gaussianMass 1 0 :=
    mul_pos_of_neg_of_neg dpKS_6cf7_gm_neg dpKS_6cf7_gm_neg
  linarith

