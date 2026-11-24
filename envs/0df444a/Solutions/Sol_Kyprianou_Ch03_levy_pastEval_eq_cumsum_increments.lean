-- Prove2me | solution 1 for Kyprianou.Ch03.levy_pastEval_eq_cumsum_increments
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T22:32:32.669381+00:00
-- url     : https://prove2.me/submissions/b4d68ee3-b8c8-4ea8-a4b9-d64482a2c8c9

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Finset
open scoped NNReal
set_option autoImplicit false

/-! Pathwise telescoping for evaluations on a grid with `e 0 = 0` and `X 0 = 0`. -/

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
    (hX0 : X 0 = fun _ => 0)
    (k : ℕ) (e : Fin (k + 1) → NNReal) (he0 : e 0 = 0)
    (v : NNReal) (i_v : Fin (k + 1)) (hi : e i_v = v)
    (ω : Omega) :
    X v ω =
      ∑ j : Fin k,
        if j.castSucc < i_v then
          X (e j.succ) ω - X (e j.castSucc) ω
        else 0 := by
  classical
  have htele := fin_partial_sum_increments X hX0 e he0 i_v ω
  have hrhs :
      (∑ j : Fin k,
          if j.castSucc < i_v then
            X (e j.succ) ω - X (e j.castSucc) ω
          else 0) =
        ∑ j ∈ univ.filter (fun j : Fin k => j.castSucc < i_v),
          (X (e j.succ) ω - X (e j.castSucc) ω) :=
    (sum_filter (fun j : Fin k => j.castSucc < i_v)
      (fun j => X (e j.succ) ω - X (e j.castSucc) ω)).symm
  rw [← hi, hrhs, htele]
