-- Prove2me | solution 1 for HadwigerConj.colorable_of_isDegenerate
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-01T13:15:12.756825+00:00
-- url     : https://prove2.me/submissions/16d15e44-280d-41ee-8ab5-48010aa1bcf6

import Mathlib
import Definitions.Def_HadwigerConj_Defs

open HadwigerConj

theorem solution {V : Type} [Finite V] (G : SimpleGraph V) (k : ℕ)
    (hG : IsDegenerate G k) : G.Colorable (k + 1) := by
  classical
  have key : ∀ (n : ℕ) (s : Finset V), s.card = n →
      ∃ c : V → Fin (k + 1), ∀ u ∈ s, ∀ w ∈ s, G.Adj u w → c u ≠ c w := by
    intro n
    induction n with
    | zero =>
      intro s _
      exact ⟨fun _ => 0, fun u hu w hw h => by simp_all⟩
    | succ n ih =>
      intro s hs
      have hne : (s : Set V).Nonempty := by
        rw [Finset.coe_nonempty, ← Finset.card_pos]; omega
      obtain ⟨v, hv, hdeg⟩ := hG _ hne
      obtain ⟨c, hc⟩ := ih (s.erase v) (by rw [Finset.card_erase_of_mem hv]; omega)
      -- the set of colours used on neighbours of `v` in `s`
      set N : Finset V := s.filter (fun u => G.Adj v u) with hN
      have hNcard : N.card ≤ k := by
        have : (N : Set V) = G.neighborSet v ∩ (s : Set V) := by
          ext u; simp [hN, and_comm]
        rw [← Set.ncard_coe_finset, this]; exact hdeg
      have himg : (N.image c).card < (Finset.univ : Finset (Fin (k + 1))).card := by
        calc (N.image c).card ≤ N.card := Finset.card_image_le
          _ ≤ k := hNcard
          _ < k + 1 := Nat.lt_succ_self k
          _ = _ := by simp
      obtain ⟨col, -, hcol⟩ := Finset.exists_mem_notMem_of_card_lt_card himg
      refine ⟨Function.update c v col, ?_⟩
      have hfree : ∀ u ∈ s, G.Adj v u → c u ≠ col := by
        intro u hu hadj heq
        exact hcol (Finset.mem_image.mpr ⟨u, by simp [hN, hu, hadj], heq⟩)
      intro u hu w hw hadj
      by_cases huv : u = v
      · subst huv
        have hwv : w ≠ u := fun h => by subst h; exact G.irrefl hadj
        rw [Function.update_self, Function.update_of_ne hwv]
        exact fun h => hfree w hw hadj h.symm
      · by_cases hwv : w = v
        · subst hwv
          rw [Function.update_self, Function.update_of_ne huv]
          exact hfree u hu hadj.symm
        · rw [Function.update_of_ne huv, Function.update_of_ne hwv]
          exact hc u (Finset.mem_erase.mpr ⟨huv, hu⟩) w (Finset.mem_erase.mpr ⟨hwv, hw⟩) hadj
  have := Fintype.ofFinite V
  obtain ⟨c, hc⟩ := key _ Finset.univ rfl
  exact ⟨SimpleGraph.Coloring.mk c (fun {u w} h => hc u (Finset.mem_univ _) w (Finset.mem_univ _) h)⟩
