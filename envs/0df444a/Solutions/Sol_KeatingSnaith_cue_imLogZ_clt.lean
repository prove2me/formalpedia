-- Prove2me | solution 1 for KeatingSnaith.cue_imLogZ_clt
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T04:31:35.689591+00:00
-- url     : https://prove2.me/submissions/71969a8a-18ab-4c81-a66d-e0e6f0a1b74f

import Mathlib
import Definitions.Def_keating_snaith_cue

/-! Disproof of cabed0fa `KeatingSnaith.cue_imLogZ_clt`.

The statement quantifies over all `a c : ℝ` with no hypothesis `a ≤ c`. For `a > c` the set
`Set.Icc a c` is empty, so the indicator vanishes and every `cueAverage` in the sequence is `0`.
But `gaussianMass a c` is an oriented interval integral, `(√(2π))⁻¹ * ∫ x in a..c, exp (-x²/2)`,
which is strictly negative when `a > c`. At `a = 1`, `c = 0` the constant sequence `0` would
have to converge to `gaussianMass 1 0 < 0`, which is impossible. -/

set_option autoImplicit false

open Finset MeasureTheory Filter Topology
open scoped Real

theorem dpKS_cabe_gm_neg : KeatingSnaith.gaussianMass 1 0 < 0 := by
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

theorem dpKS_cabe_avg_zero (N : ℕ) (g : (Fin N → ℝ) → ℝ) :
    KeatingSnaith.cueAverage N
      (fun θ => Set.indicator (Set.Icc (1 : ℝ) 0) (fun _ => (1 : ℝ)) (g θ)) = 0 := by
  have hE : Set.Icc (1 : ℝ) 0 = ∅ := Set.Icc_eq_empty (by norm_num)
  rw [hE]
  simp [KeatingSnaith.cueAverage]

open KeatingSnaith in
theorem solution : ¬ (∀ (a c : ℝ),
    Tendsto (fun N : ℕ => cueAverage N (fun θ =>
        Set.indicator (Set.Icc a c) (fun _ => (1 : ℝ)) (imLogZ N θ / cltScale N)))
      atTop (𝓝 (gaussianMass a c))) := by
  intro H
  have h := H 1 0
  have hz : (fun N : ℕ => cueAverage N (fun θ =>
      Set.indicator (Set.Icc (1 : ℝ) 0) (fun _ => (1 : ℝ)) (imLogZ N θ / cltScale N)))
      = fun _ => (0 : ℝ) := by
    funext N
    exact dpKS_cabe_avg_zero N _
  rw [hz] at h
  have h0 := tendsto_nhds_unique tendsto_const_nhds h
  linarith [dpKS_cabe_gm_neg]

