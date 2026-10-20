-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Bipartite.minimum_cover_left_hall
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:05:59.048255+00:00
-- url     : https://prove2.me/submissions/35fc2af6-05b8-4840-ab27-fe6a74993905

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/MatchingCover.lean:L28-L73
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Bipartite.minimum_cover_left_hall. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatchingAugmented
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankMatching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRank

-- ---- from OAI.Combinatorics.SecondNeighborhood.MatchingCover ----
namespace OAI

namespace SeymourSecondNeighborhood.Bipartite

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
variable {E : L → R → Prop}

private theorem minimum_cover_left_hall {A : Finset L} {B : Finset R}
    (hC : IsVertexCover E A B)
    (hmin : ∀ A' B', IsVertexCover E A' B' →
      A.card + B.card ≤ A'.card + B'.card) :
    ∃ f : A → R, Function.Injective f ∧ ∀ a : A, E (a : L) (f a) ∧ f a ∉ B := by
  classical
  let t : A → Finset R := fun a => Finset.univ.filter (fun r => E a r ∧ r ∉ B)
  have hhall : ∀ s : Finset A, s.card ≤ (s.biUnion t).card := by
    intro s
    let S : Finset L := s.image (fun a : A => (a : L))
    let T : Finset R := s.biUnion t
    have hSA : S ⊆ A := by
      intro l hl
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hl
      exact a.property
    have hScard : S.card = s.card :=
      Finset.card_image_of_injective s Subtype.val_injective
    have hdisjoint : Disjoint B T := by
      apply Finset.disjoint_left.mpr
      intro r hrB hrT
      obtain ⟨a, _, hra⟩ := Finset.mem_biUnion.mp hrT
      exact (Finset.mem_filter.mp hra).2.2 hrB
    have hreplace : IsVertexCover E (A \ S) (B ∪ T) := by
      intro l r hlr
      by_cases hlS : l ∈ S
      · by_cases hrB : r ∈ B
        · exact Or.inr (Finset.mem_union_left _ hrB)
        · right
          apply Finset.mem_union_right
          obtain ⟨a, has, hal⟩ := Finset.mem_image.mp hlS
          apply Finset.mem_biUnion.mpr
          refine ⟨a, has, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hrB⟩⟩
          rw [hal]
          exact hlr
      · rcases hC l r hlr with hlA | hrB
        · exact Or.inl (Finset.mem_sdiff.mpr ⟨hlA, hlS⟩)
        · exact Or.inr (Finset.mem_union_left _ hrB)
    have hbound := hmin (A \ S) (B ∪ T) hreplace
    rw [Finset.card_union_of_disjoint hdisjoint] at hbound
    have hsplit := Finset.card_sdiff_add_card_eq_card hSA
    rw [hScard] at hsplit
    change s.card ≤ T.card
    omega
  obtain ⟨f, hfinj, hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hhall
  exact ⟨f, hfinj, fun a => (Finset.mem_filter.mp (hf a)).2⟩

end SeymourSecondNeighborhood.Bipartite

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Bipartite


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Bipartite.minimum_cover_left_hall := @_root_.OAI.SeymourSecondNeighborhood.Bipartite.minimum_cover_left_hall
