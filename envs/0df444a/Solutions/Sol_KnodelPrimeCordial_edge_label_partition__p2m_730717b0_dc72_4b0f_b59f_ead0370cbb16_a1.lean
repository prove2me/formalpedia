-- Prove2me | solution 1 for KnodelPrimeCordial.edge_label_partition__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T09:57:03.233262+00:00
-- url     : https://prove2.me/submissions/241f16b6-a940-4711-98f4-52ec6e4007fd

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (f : V → ℕ)
    (hpos : ∀ e ∈ G.edgeFinset, 0 < KnodelPrimeCordial.edgeGcd f e) :
    (KnodelPrimeCordial.edgesLabelZero G f).card +
      (KnodelPrimeCordial.edgesLabelOne G f).card = G.edgeFinset.card := by
  classical
  let A := KnodelPrimeCordial.edgesLabelZero G f
  let B := KnodelPrimeCordial.edgesLabelOne G f
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e heA heB
    have hA : e ∈ G.edgeFinset ∧ 1 < KnodelPrimeCordial.edgeGcd f e := by
      simpa [A, KnodelPrimeCordial.edgesLabelZero, Finset.mem_filter] using heA
    have hB : e ∈ G.edgeFinset ∧ KnodelPrimeCordial.edgeGcd f e = 1 := by
      simpa [B, KnodelPrimeCordial.edgesLabelOne, Finset.mem_filter] using heB
    omega
  have hcover : A ∪ B = G.edgeFinset := by
    ext e
    simp only [Finset.mem_union, A, B, KnodelPrimeCordial.edgesLabelZero,
      KnodelPrimeCordial.edgesLabelOne, Finset.mem_filter]
    constructor
    · rintro (⟨he, _⟩ | ⟨he, _⟩)
      · exact he
      · exact he
    · intro he
      by_cases heq : KnodelPrimeCordial.edgeGcd f e = 1
      · exact Or.inr ⟨he, heq⟩
      · left
        exact ⟨he, by have := hpos e he; omega⟩
  calc
    (KnodelPrimeCordial.edgesLabelZero G f).card +
        (KnodelPrimeCordial.edgesLabelOne G f).card = (A ∪ B).card := by
          simpa [A, B] using (Finset.card_union_of_disjoint hdisj).symm
    _ = G.edgeFinset.card := by rw [hcover]
