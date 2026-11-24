-- Prove2me | solution 1 for Kyprianou.Ch03.levy_future_inc_eq_cumsum_successive
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T22:27:09.0682+00:00
-- url     : https://prove2.me/submissions/40e95a10-e5bd-4639-8ee3-340d0988dbb9

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Finset
open scoped NNReal
set_option autoImplicit false

/-!
Pathwise telescoping along a lag grid for the shifted path `s ↦ X_(τ+s) - X_τ`.
-/

private lemma fin_partial_sum_increments
    {Omega : Type} (Y : NNReal → Omega → ℝ) (hY0 : Y 0 = fun _ => 0)
    {k : ℕ} (e : Fin (k + 1) → NNReal) (he0 : e 0 = 0) (i : Fin (k + 1)) (ω : Omega) :
    Y (e i) ω =
      ∑ j ∈ univ.filter (fun j : Fin k => j.castSucc < i),
        (Y (e j.succ) ω - Y (e j.castSucc) ω) := by
  induction i using Fin.induction with
  | zero =>
    have hfilt : univ.filter (fun j : Fin k => j.castSucc < (0 : Fin (k + 1))) = ∅ := by
      ext j; simp
    rw [hfilt, sum_empty, he0, hY0]
  | succ i' ih =>
    have hfilt :
        univ.filter (fun j : Fin k => j.castSucc < i'.succ) =
          insert i'
            (univ.filter (fun j : Fin k => j.castSucc < i'.castSucc)) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · intro h
        rcases lt_or_eq_of_le (Fin.le_castSucc_iff.mpr h) with hlt | heq
        · exact Or.inr hlt
        · exact Or.inl (Fin.castSucc_injective k heq)
      · rintro (rfl | hlt)
        · exact Fin.castSucc_lt_succ
        · exact hlt.trans Fin.castSucc_lt_succ
    have hnot : i' ∉ univ.filter (fun j : Fin k => j.castSucc < i'.castSucc) := by simp
    rw [hfilt, sum_insert hnot, ← ih]
    ring

theorem solution
    {Omega : Type}
    (X : NNReal → Omega → Real)
    (τ : NNReal)
    (m : ℕ) (lags : Fin (m + 1) → NNReal) (_hlags : Monotone lags)
    (h0 : lags 0 = 0)
    (u : NNReal) (i_u : Fin (m + 1)) (hi_u : lags i_u = u)
    (ω : Omega) :
    X (τ + u) ω - X τ ω =
      ∑ i : Fin m,
        if i.succ ≤ i_u then
          X (τ + lags i.succ) ω - X (τ + lags i.castSucc) ω
        else 0 := by
  let Y : NNReal → Omega → ℝ := fun s ω' => X (τ + s) ω' - X τ ω'
  have hY0 : Y 0 = fun _ => 0 := by funext; simp [Y]
  have hLHS : X (τ + u) ω - X τ ω = Y (lags i_u) ω := by simp [Y, hi_u]
  have htele := fin_partial_sum_increments Y hY0 lags h0 i_u ω
  classical
  have hiff : ∀ i : Fin m, i.succ ≤ i_u ↔ i.castSucc < i_u := fun i =>
    (Fin.castSucc_lt_iff_succ_le (i := i) (j := i_u)).symm
  have hrhs :
      (∑ i : Fin m,
          if i.succ ≤ i_u then
            X (τ + lags i.succ) ω - X (τ + lags i.castSucc) ω
          else 0) =
        ∑ i ∈ univ.filter (fun i : Fin m => i.castSucc < i_u),
          (Y (lags i.succ) ω - Y (lags i.castSucc) ω) := by
    have h1 :
        (∑ i : Fin m,
            if i.succ ≤ i_u then
              X (τ + lags i.succ) ω - X (τ + lags i.castSucc) ω
            else 0) =
          ∑ i ∈ univ.filter (fun i : Fin m => i.succ ≤ i_u),
            (X (τ + lags i.succ) ω - X (τ + lags i.castSucc) ω) :=
      (sum_filter (fun i : Fin m => i.succ ≤ i_u)
        (fun i => X (τ + lags i.succ) ω - X (τ + lags i.castSucc) ω)).symm
    rw [h1]
    refine sum_congr ?_ fun i _ => by simp [Y]
    ext i
    simp only [mem_filter, mem_univ, true_and]
    exact hiff i
  rw [hLHS, hrhs, htele]
