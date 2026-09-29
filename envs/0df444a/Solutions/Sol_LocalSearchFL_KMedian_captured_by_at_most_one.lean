-- Prove2me | solution 1 for LocalSearchFL.KMedian.captured_by_at_most_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T23:55:36.466326+00:00
-- url     : https://prove2.me/submissions/c7631a19-ba63-48b0-b5da-4854376e7946

import Mathlib
import Definitions.Def_LocalSearchFL_KMedian_captures

open LocalSearchFL.KMedian

theorem solution {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (o s s' : Fa)
    (hs : captures σS σO s o) (hs' : captures σS σO s' o) : s = s' := by
  by_contra hne
  have hdisj : Disjoint (nbhd σO o ∩ nbhd σS s) (nbhd σO o ∩ nbhd σS s') := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    have h1 : σS j = s := by
      have := Finset.mem_inter.mp hj
      simpa [nbhd] using this.2
    have h2 : σS j = s' := by
      have := Finset.mem_inter.mp hj'
      simpa [nbhd] using this.2
    exact hne (h1 ▸ h2 ▸ rfl)
  have hsub : (nbhd σO o ∩ nbhd σS s) ∪ (nbhd σO o ∩ nbhd σS s') ⊆ nbhd σO o := by
    intro j hj
    rcases Finset.mem_union.mp hj with h | h
    · exact (Finset.mem_inter.mp h).1
    · exact (Finset.mem_inter.mp h).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  unfold captures at hs hs'
  omega
