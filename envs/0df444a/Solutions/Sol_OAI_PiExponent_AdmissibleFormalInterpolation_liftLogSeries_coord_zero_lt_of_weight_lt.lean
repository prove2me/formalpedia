-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_coord_zero_lt_of_weight_lt
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:33:06.762878+00:00
-- url     : https://prove2.me/submissions/7e0f3714-15e2-44c3-9f1a-c309f14da5f4

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem solution
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (N : Fin m → ℕ)
    (hv0 : 0 < v0)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (i : Fin m) (α : Fin (m + 1) →₀ ℕ)
    (htail : ∀ j : Fin m, α j.succ = 0)
    (hα : (∑ j, Fin.cases v0 u j * (α j : ℝ)) < u i) :
    α 0 < N i := by
  rw [Fin.sum_univ_succ] at hα
  simp [htail] at hα
  by_contra h
  have hle : (N i : ℝ) ≤ (α 0 : ℝ) := by
    exact_mod_cast (Nat.not_lt.mp h)
  have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt hv0)
  nlinarith [hN i]