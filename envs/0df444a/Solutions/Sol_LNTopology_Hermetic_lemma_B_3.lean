-- Prove2me | solution 1 for LNTopology.Hermetic.lemma_B_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:05:29.753563+00:00
-- url     : https://prove2.me/submissions/bb8be243-d2d9-40a7-a5e0-2159e566050a

import Mathlib
import Definitions.Def_LNTopology_Hermetic_Peel

set_option autoImplicit false
open LNTopology.Hermetic

theorem solution {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (t : ℝ) :
    (∀ v ∈ peel G t, t < ((G.neighborFinset v ∩ peel G t).card : ℝ)) ∧
      ∀ W' : Finset W, (∀ v ∈ W', t < ((G.neighborFinset v ∩ W').card : ℝ)) →
        W' ⊆ peel G t := by
  have hsub : ∀ S : Finset W, peelStep G t S ⊆ S := fun S => Finset.filter_subset _ _
  -- the iterates stabilise within `card W` steps
  have key : ∀ k : ℕ, (peelStep G t)^[k + 1] Finset.univ = (peelStep G t)^[k] Finset.univ ∨
      ((peelStep G t)^[k] Finset.univ).card + k ≤ Fintype.card W := by
    intro k
    induction k with
    | zero => right; simp
    | succ k ih =>
      by_cases hfix : (peelStep G t)^[k + 1] Finset.univ = (peelStep G t)^[k] Finset.univ
      · left
        rw [Function.iterate_succ_apply' (peelStep G t) (k + 1), hfix,
          ← Function.iterate_succ_apply' (peelStep G t) k]
        exact hfix
      · right
        have hlt : ((peelStep G t)^[k + 1] Finset.univ).card <
            ((peelStep G t)^[k] Finset.univ).card := by
          apply Finset.card_lt_card
          refine ⟨?_, ?_⟩
          · rw [Function.iterate_succ_apply']; exact hsub _
          · intro hh; exact hfix (Finset.Subset.antisymm (by rw [Function.iterate_succ_apply']; exact hsub _) hh)
        rcases ih with h | h
        · exact absurd h hfix
        · omega
  have hfixed : peelStep G t (peel G t) = peel G t := by
    unfold peel
    rcases key (Fintype.card W) with h | h
    · rw [← Function.iterate_succ_apply' (peelStep G t)]; exact h
    · have h0 : ((peelStep G t)^[Fintype.card W] Finset.univ) = ∅ := by
        apply Finset.card_eq_zero.1; omega
      rw [h0]
      simp [peelStep]
  refine ⟨?_, ?_⟩
  · intro v hv
    have : v ∈ peelStep G t (peel G t) := by rw [hfixed]; exact hv
    simp only [peelStep, Finset.mem_filter] at this
    exact this.2
  · intro W' hW'
    have : ∀ k : ℕ, W' ⊆ (peelStep G t)^[k] Finset.univ := by
      intro k
      induction k with
      | zero => intro v _; simp
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        intro v hv
        simp only [peelStep, Finset.mem_filter]
        refine ⟨ih hv, lt_of_lt_of_le (hW' v hv) ?_⟩
        exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_left ih)
    exact this _
