-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Bipartite.exists_vertexCover_card_eq_of_isMaximumMatching
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:08:24.186334+00:00
-- url     : https://prove2.me/submissions/6bd43bf5-f6f1-483e-87d2-4701ea451841

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/MatchingCover.lean:L181-L222
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Bipartite.exists_vertexCover_card_eq_of_isMaximumMatching. The node keeps its source
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
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Bipartite_matching_card_le_cover_card
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Bipartite_minimum_cover_has_equal_matching

-- ---- from OAI.Combinatorics.SecondNeighborhood.MatchingCover ----
namespace OAI

namespace SeymourSecondNeighborhood.Bipartite

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
variable {E : L → R → Prop}

omit [DecidableEq L] [DecidableEq R] in
private theorem exists_minimum_vertexCover (E : L → R → Prop) :
    ∃ A : Finset L, ∃ B : Finset R, IsVertexCover E A B ∧
      ∀ A' B', IsVertexCover E A' B' → A.card + B.card ≤ A'.card + B'.card := by
  classical
  let covers : Finset (Finset L × Finset R) :=
    Finset.univ.filter (fun p => IsVertexCover E p.1 p.2)
  have hnonempty : covers.Nonempty := by
    refine ⟨(Finset.univ, ∅), ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun l _ _ => Or.inl (Finset.mem_univ l)⟩
  obtain ⟨p, hp, hleast⟩ :=
    covers.exists_min_image (fun p => p.1.card + p.2.card) hnonempty
  refine ⟨p.1, p.2, (Finset.mem_filter.mp hp).2, ?_⟩
  intro A' B' hC
  exact hleast (A', B') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC⟩)

theorem exists_vertexCover_card_eq_of_isMaximumMatching {M : Finset (L × R)}
    (hM : IsMaximumMatching E M) :
    ∃ A : Finset L, ∃ B : Finset R,
      IsVertexCover E A B ∧ A.card + B.card = M.card ∧
      (∀ l ∈ A, ∃ r, E l r) ∧ (∀ r ∈ B, ∃ l, E l r) := by
  classical
  obtain ⟨A, B, hC, hmin⟩ := exists_minimum_vertexCover E
  obtain ⟨N, hN, hNcard⟩ := minimum_cover_has_equal_matching hC hmin
  have hupper : A.card + B.card ≤ M.card := by
    rw [← hNcard]
    exact hM.2 N hN
  have hcard : A.card + B.card = M.card :=
    Nat.le_antisymm hupper (matching_card_le_cover_card hM.1 hC)
  refine ⟨A, B, hC, hcard, ?_, ?_⟩
  · intro l hl
    by_contra h
    have hreplace : IsVertexCover E (A.erase l) B := by
      intro x r hxr
      rcases hC x r hxr with hx | hr
      · left
        refine Finset.mem_erase.mpr ⟨?_, hx⟩
        intro hxl
        subst x
        exact h ⟨r, hxr⟩
      · exact Or.inr hr
    have hbound := hmin (A.erase l) B hreplace
    have herase := Finset.card_erase_add_one hl
    omega
  · intro r hr
    by_contra h
    have hreplace : IsVertexCover E A (B.erase r) := by
      intro l y hly
      rcases hC l y hly with hl | hy
      · exact Or.inl hl
      · right
        refine Finset.mem_erase.mpr ⟨?_, hy⟩
        intro hyr
        subst y
        exact h ⟨l, hly⟩
    have hbound := hmin A (B.erase r) hreplace
    have herase := Finset.card_erase_add_one hr
    omega

end SeymourSecondNeighborhood.Bipartite

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Bipartite


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Bipartite.exists_vertexCover_card_eq_of_isMaximumMatching := @_root_.OAI.SeymourSecondNeighborhood.Bipartite.exists_vertexCover_card_eq_of_isMaximumMatching
