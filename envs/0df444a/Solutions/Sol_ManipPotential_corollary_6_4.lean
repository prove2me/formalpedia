-- Prove2me | solution 1 for ManipPotential.corollary_6_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:01:44.525115+00:00
-- url     : https://prove2.me/submissions/a86f753c-5549-48bd-9d71-90cabc07a3eb

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_cycL
import Definitions.Def_ManipPotential_cycR
import Definitions.Def_ManipPotential_supp
import Theorems.Thm_ManipPotential_lemma_6_3

open ManipPotential

theorem solution {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) (x : Fin m → ℚ) (hx : 0 ≤ x) (hx0 : x ≠ 0) :
    g (cycL x) ∈ supp x ∧ g (cycR x) ∈ supp x := by
  have hL := (lemma_6_3 hm K g hg 0 le_rfl 0 le_rfl).1
  have hR := (lemma_6_3 hm K g hg 0 le_rfl 0 le_rfl).2
  have hpos : 0 < ∑ j, x j := by
    obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
      by_contra h
      push Not at h
      exact hx0 (funext h)
    have hk' : 0 < x k := lt_of_le_of_ne (hx k) (Ne.symm hk)
    exact lt_of_lt_of_le hk' (Finset.single_le_sum (fun i _ => hx i) (Finset.mem_univ k))
  have hsum : ((K : ℚ) + 1) ^ ((supp x).card - 1) * 0 < ∑ j, x j := by simpa using hpos
  constructor
  · have := hL (fun j u hu => ?_) x hx hx0 hsum
    · simpa using this
    · rw [zero_add, hg.1 (ell j) u hu]
      simp [Ranking.top, ell]
  · have := hR (fun j u hu => ?_) x hx hx0 hsum
    · simpa using this
    · rw [zero_add, hg.1 (rr j) u hu]
      simp [Ranking.top, rr]
