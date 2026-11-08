-- Prove2me | solution 1 for ImpatientMatching.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:57:01.547093+00:00
-- url     : https://prove2.me/submissions/004e3bae-33c4-4970-8c61-98d8e61191e1

import Definitions.Def_ImpatientMatching_Source

open NSWApxHard.Reduction

open ImpatientMatching in
theorem solution (H : GraphInput) (P : Finset (Fin H.N)) : ImpatientMatching.tau H ≤ ImpatientMatching.Phi H P := by
  unfold ImpatientMatching.tau ImpatientMatching.Phi ImpatientMatching.uncovered
  set U : Set (Sym2 (Fin H.N)) := {e | e ∈ H.G.edgeSet ∧ ∀ v ∈ e, v ∉ P} with hU
  have hUfin : U.Finite := Set.toFinite U
  set S : Set (Fin H.N) := (fun e : Sym2 (Fin H.N) => e.out.1) '' U with hS
  have hcov : H.G.IsVertexCover ((↑P : Set (Fin H.N)) ∪ S) := by
    intro v w hvw
    by_cases hv : v ∈ P
    · exact Or.inl (Set.mem_union_left _ (Finset.mem_coe.2 hv))
    by_cases hw : w ∈ P
    · exact Or.inr (Set.mem_union_left _ (Finset.mem_coe.2 hw))
    have he : s(v, w) ∈ U := by
      refine ⟨hvw, ?_⟩
      intro u hu
      rw [Sym2.mem_iff] at hu
      rcases hu with rfl | rfl <;> assumption
    have hm := Sym2.out_fst_mem s(v, w)
    rw [Sym2.mem_iff] at hm
    rcases hm with h | h
    · exact Or.inl (Set.mem_union_right _ ⟨_, he, h⟩)
    · exact Or.inr (Set.mem_union_right _ ⟨_, he, h⟩)
  have h1 := hcov.vertexCoverNum_le
  have h2 : ((↑P : Set (Fin H.N)) ∪ S).encard ≤ ((P.card + U.ncard : ℕ) : ℕ∞) := by
    calc ((↑P : Set (Fin H.N)) ∪ S).encard ≤ (↑P : Set (Fin H.N)).encard + S.encard :=
          Set.encard_union_le _ _
      _ ≤ (P.card : ℕ∞) + U.encard := by
          rw [Set.encard_coe_eq_coe_finsetCard]
          exact add_le_add le_rfl (Set.encard_image_le _ _)
      _ = ((P.card + U.ncard : ℕ) : ℕ∞) := by
          rw [← hUfin.cast_ncard_eq]
          push_cast
          rfl
  exact ENat.toNat_le_of_le_natCast (h1.trans h2)
