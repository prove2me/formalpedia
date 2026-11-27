-- Prove2me | solution 1 for ManipPotential.winner_closures_cover
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:07:30.549308+00:00
-- url     : https://prove2.me/submissions/5e6e20bb-1af1-4d59-8e5e-b530fc2c1672

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_winnerClosure
import Definitions.Def_ManipPotential_cycTotal
import Definitions.Def_ManipPotential_extNorm
import Definitions.Def_ManipPotential_delta
import Theorems.Thm_ManipPotential_corollary_6_7

open ManipPotential

theorem solution {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) :
    Omega m ⊆ ⋃ j, winnerClosure g j ∧
    ∀ (j : Fin m), ∀ P ∈ winnerClosure g j,
      (delta m K : ℝ) * cycTotal P - ((K : ℝ) + 1) * (1 - (delta m K : ℝ)) * extNorm P ≤
        P (ell j) := by
  constructor
  · intro P hP
    rw [Set.mem_iUnion]
    by_contra hno
    push Not at hno
    have hnc : ∀ j, ∃ ε > 0, ∀ b ∈ {P | P ∈ Omega m ∧ ∃ q : Ranking m → ℚ,
        (fun r => (q r : ℝ)) = P ∧ g q = j}, ε ≤ dist P b := by
      intro j
      have h1 : P ∉ closure {P | P ∈ Omega m ∧ ∃ q : Ranking m → ℚ,
          (fun r => (q r : ℝ)) = P ∧ g q = j} := fun hc => hno j ⟨hP, hc⟩
      rw [Metric.mem_closure_iff] at h1
      push Not at h1
      exact h1
    choose ε hεpos hε using hnc
    set ε0 : ℝ := min (Finset.univ.inf' Finset.univ_nonempty ε)
      (Finset.univ.inf' Finset.univ_nonempty P) with hε0def
    have hε0pos : 0 < ε0 := by
      apply lt_min
      · exact (Finset.lt_inf'_iff _).mpr (fun j _ => hεpos j)
      · exact (Finset.lt_inf'_iff _).mpr (fun r _ => hP r)
    have hq : ∀ r : Ranking m, ∃ t : ℚ, P r < t ∧ (t : ℝ) < P r + ε0 / 2 := by
      intro r
      exact exists_rat_btwn (by linarith)
    choose q hq1 hq2 using hq
    have hqΩ : (fun r => (q r : ℝ)) ∈ Omega m := fun r => lt_trans (hP r) (hq1 r)
    have hdist : dist P (fun r => (q r : ℝ)) < ε0 := by
      rw [dist_pi_lt_iff hε0pos]
      intro r
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hq1 r, hq2 r]
    have := hε (g q) (fun r => (q r : ℝ)) ⟨hqΩ, q, rfl, rfl⟩
    have h2 : ε0 ≤ ε (g q) :=
      le_trans (min_le_left _ _) (Finset.inf'_le _ (Finset.mem_univ _))
    linarith
  · intro j P hP
    have hsub : {P | P ∈ Omega m ∧ ∃ q : Ranking m → ℚ, (fun r => (q r : ℝ)) = P ∧ g q = j} ⊆
        {P : Ranking m → ℝ | (delta m K : ℝ) * cycTotal P -
          ((K : ℝ) + 1) * (1 - (delta m K : ℝ)) * extNorm P ≤ P (ell j)} := by
      rintro _ ⟨hΩ, q, rfl, hqj⟩
      have hq0 : 0 ≤ q := by
        intro r
        have := hΩ r
        simp only at this
        exact le_of_lt (by exact_mod_cast this)
      have hX : 0 < cycTotal q := by
        unfold cycTotal
        apply Finset.sum_pos _ Finset.univ_nonempty
        intro i _
        have := hΩ (ell i)
        simp only at this
        exact_mod_cast this
      have h := corollary_6_7 hm K g hg q hq0 hX j hqj
      have hcyc : cycTotal (fun r => (q r : ℝ)) = ((cycTotal q : ℚ) : ℝ) := by
        unfold cycTotal; push_cast; rfl
      have hext : extNorm (fun r => (q r : ℝ)) = ((extNorm q : ℚ) : ℝ) := by
        unfold extNorm; push_cast; rfl
      simp only [Set.mem_setOf_eq]
      rw [hcyc, hext]
      exact_mod_cast h
    have hclosed : IsClosed {P : Ranking m → ℝ | (delta m K : ℝ) * cycTotal P -
          ((K : ℝ) + 1) * (1 - (delta m K : ℝ)) * extNorm P ≤ P (ell j)} := by
      apply isClosed_le _ (continuous_apply _)
      unfold cycTotal extNorm
      fun_prop
    exact closure_minimal hsub hclosed hP.2
