-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Bipartite.exists_matching_saturating_left_of_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:59:52.019214+00:00
-- url     : https://prove2.me/submissions/692ebe10-329f-4f2c-9264-abb37b5aa588

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/MatchingExchange.lean:L43-L113
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Bipartite.exists_matching_saturating_left_of_card_lt. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_PruningDefinitions
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Matching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_AugmentedGraph

-- ---- from OAI.Combinatorics.SecondNeighborhood.MatchingExchange ----
namespace OAI

namespace SeymourSecondNeighborhood.Bipartite

variable {L R : Type*} {E : L → R → Prop}

private theorem exchange_matching_subset {M N : Finset (L × R)}
    (hM : IsMatching E M) (hNM : N ⊆ M) : IsMatching E N := by
  exact ⟨fun e he => hM.1 e (hNM he),
    fun _ he _ hf h => hM.2.1 (hNM he) (hNM hf) h,
    fun _ he _ hf h => hM.2.2 (hNM he) (hNM hf) h⟩

private theorem exchange_matching_insert [DecidableEq L] [DecidableEq R]
    {M : Finset (L × R)} (hM : IsMatching E M) {a : L} {b : R}
    (hab : E a b) (ha : ∀ e ∈ M, e.1 ≠ a) (hb : ∀ e ∈ M, e.2 ≠ b) :
    IsMatching E (insert (a, b) M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hab
    · exact hM.1 e he
  · intro e he f hf hef
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · rfl
      · exact False.elim (ha f hf hef.symm)
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact False.elim (ha e he hef)
      · exact hM.2.1 he hf hef
  · intro e he f hf hef
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · rfl
      · exact False.elim (hb f hf hef.symm)
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact False.elim (hb e he hef)
      · exact hM.2.2 he hf hef

theorem exists_matching_saturating_left_of_card_lt [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    {M N : Finset (L × R)} (hM : IsMatching E M) (hN : IsMatching E N)
    (hcard : M.card < N.card) :
    ∃ Q : Finset (L × R), IsMatching E Q ∧ Q.card = N.card ∧
      M.image Prod.fst ⊆ Q.image Prod.fst := by
  classical
  let family : Finset (Finset (L × R)) :=
    Finset.univ.filter (fun Q => IsMatching E Q ∧ Q.card = N.card)
  have hNfamily : N ∈ family := by simp [family, hN]
  obtain ⟨Q, hQfamily, hQmax⟩ :=
    family.exists_max_image (fun Q => (Q ∩ M).card) ⟨N, hNfamily⟩
  have hQ : IsMatching E Q ∧ Q.card = N.card :=
    (Finset.mem_filter.mp hQfamily).2
  refine ⟨Q, hQ.1, hQ.2, ?_⟩
  intro a ha
  by_contra haQ
  obtain ⟨m, hmM, rfl⟩ := Finset.mem_image.mp ha
  have hfree : ∀ e ∈ Q, e.1 ≠ m.1 := by
    intro e he heq
    exact haQ (Finset.mem_image.mpr ⟨e, he, heq⟩)
  have hmQ : m ∉ Q := fun hm => hfree m hm rfl
  have hexternal : ∃ e ∈ Q, e ∉ M := by
    by_contra h
    have hQM : Q ⊆ M := by
      intro e he
      by_contra heM
      exact h ⟨e, he, heM⟩
    have := Finset.card_le_card hQM
    omega
  have hremove : ∃ e ∈ Q, e ∉ M ∧ ∀ f ∈ Q, f.2 = m.2 → f = e := by
    by_cases hright : ∃ e ∈ Q, e.2 = m.2
    · obtain ⟨e, heQ, he⟩ := hright
      have heM : e ∉ M := by
        intro heM
        have hem : e = m := hM.2.2 heM hmM he
        exact hmQ (hem ▸ heQ)
      exact ⟨e, heQ, heM, fun f hf hfm => hQ.1.2.2 hf heQ (hfm.trans he.symm)⟩
    · obtain ⟨e, heQ, heM⟩ := hexternal
      exact ⟨e, heQ, heM, fun f hf hfm => False.elim (hright ⟨f, hf, hfm⟩)⟩
  obtain ⟨e, heQ, heM, he_unique⟩ := hremove
  let Q' := insert m (Q.erase e)
  have hQ'match : IsMatching E Q' := by
    apply exchange_matching_insert
      (exchange_matching_subset hQ.1 (Finset.erase_subset e Q)) (hM.1 m hmM)
    · intro f hf
      exact hfree f (Finset.mem_of_mem_erase hf)
    · intro f hf hfm
      exact (Finset.mem_erase.mp hf).1 (he_unique f (Finset.mem_of_mem_erase hf) hfm)
  have hmQerase : m ∉ Q.erase e := fun hm => hmQ (Finset.mem_of_mem_erase hm)
  have hQ'card : Q'.card = N.card := by
    dsimp [Q']
    rw [Finset.card_insert_of_notMem hmQerase, Finset.card_erase_of_mem heQ]
    have : 0 < Q.card := Finset.card_pos.mpr ⟨e, heQ⟩
    omega
  have hQ'family : Q' ∈ family := by simp [family, hQ'match, hQ'card]
  have hinter : Q' ∩ M = insert m (Q ∩ M) := by
    ext f
    simp only [Q', Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨rfl | ⟨hne, hfQ⟩, hfM⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hfQ, hfM⟩
    · rintro (rfl | ⟨hfQ, hfM⟩)
      · exact ⟨Or.inl rfl, hmM⟩
      · exact ⟨Or.inr ⟨fun hfe => heM (hfe ▸ hfM), hfQ⟩, hfM⟩
  have hmInter : m ∉ Q ∩ M := fun hm => hmQ (Finset.mem_inter.mp hm).1
  have hstrict : (Q ∩ M).card < (Q' ∩ M).card := by
    rw [hinter, Finset.card_insert_of_notMem hmInter]
    omega
  exact (not_lt_of_ge (hQmax Q' hQ'family)) hstrict

end SeymourSecondNeighborhood.Bipartite

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Bipartite


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Bipartite.exists_matching_saturating_left_of_card_lt := @_root_.OAI.SeymourSecondNeighborhood.Bipartite.exists_matching_saturating_left_of_card_lt
