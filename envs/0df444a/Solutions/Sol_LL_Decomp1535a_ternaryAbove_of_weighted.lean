-- Prove2me | solution 1 for LL_Decomp1535a.ternaryAbove_of_weighted
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:04.28228+00:00
-- url     : https://prove2.me/submissions/21609c15-3cde-4e72-936c-b602ac2ec702

import Mathlib
import Definitions.Def_LL_Decomp1535a_IsTernarySum
import Definitions.Def_LL_Decomp1535a_R3
import Definitions.Def_LL_Decomp1535a_ChenWangWeighted
import Definitions.Def_LL_Decomp1535a_TernaryAbove

open MeasureTheory

noncomputable def GbAAux.R3A (N : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N + 1),
    if p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = N then
      Real.log p * Real.log q * Real.log r else 0

theorem GbAAux.ex_pos {ι : Type*} {s : Finset ι} {f : ι → ℝ} (h : 0 < ∑ i ∈ s, f i) :
    ∃ i ∈ s, 0 < f i := by
  by_contra hc
  exact absurd h (not_lt.2 (Finset.sum_nonpos fun i hi => not_lt.1 fun h' => hc ⟨i, hi, h'⟩))

theorem GbAAux.ternary_of_R3 (N : ℕ) (h : 0 < GbAAux.R3A N) : LL_Decomp1535a.IsTernarySum N := by
  unfold GbAAux.R3A at h
  obtain ⟨p, _, hp⟩ := GbAAux.ex_pos h
  obtain ⟨q, _, hq⟩ := GbAAux.ex_pos hp
  obtain ⟨r, _, hr⟩ := GbAAux.ex_pos hq
  by_cases hc : p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = N
  · exact ⟨p, q, r, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
  · rw [if_neg hc] at hr
    exact absurd hr (lt_irrefl _)

theorem solution {C : ℝ} (h : LL_Decomp1535a.ChenWangWeighted C) :
    LL_Decomp1535a.TernaryAbove C :=
  fun n hn hC => GbAAux.ternary_of_R3 n (h n hn hC)
