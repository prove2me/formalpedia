-- Prove2me | solution 1 for KnodelPrimeCordial.primeCordial_transport__p2m_b71a112c_d89d_4dc4_9a88_bb82c5bac86c_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T11:18:05.89624+00:00
-- url     : https://prove2.me/submissions/55231384-33e5-4e4c-8204-e54e982ceb24

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Theorems.Thm_KnodelPrimeCordial_edge_label_counts_transport__p2m_997a75d7_cde0_465d_99c4_3e69bfa4c2a4_a1

theorem solution
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : V ≃ W)
    (hadj : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b))
    (f : V → ℕ)
    (hf : KnodelPrimeCordial.IsPrimeCordialLabeling G f) :
    ∃ g : W → ℕ, KnodelPrimeCordial.IsPrimeCordialLabeling H g := by
  refine ⟨f ∘ e.symm, ?_⟩
  refine ⟨?_, ?_⟩
  · have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr e
    rcases hf.1 with ⟨hmap, hinj, hsurj⟩
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      have hmem := hmap (Set.mem_univ (e.symm w))
      simpa [Function.comp, hcard] using hmem
    · intro x hx y hy hxy
      have hsymm := hinj (Set.mem_univ x) (Set.mem_univ y) hxy
      simpa using congrArg e hsymm
    · intro y hy
      obtain ⟨x, hx, hfx⟩ := hsurj (by simpa [hcard] using hy)
      refine ⟨e x, Set.mem_univ _, ?_⟩
      simpa using hfx
  · have hcounts :=
      KnodelPrimeCordial.edge_label_counts_transport__p2m_997a75d7_cde0_465d_99c4_3e69bfa4c2a4_a1
        G H e hadj f
    rw [← hcounts.1, ← hcounts.2]
    exact hf.2
