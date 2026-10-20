-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Bipartite.exists_maximum_matching_min_cost
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:50:08.269488+00:00
-- url     : https://prove2.me/submissions/4f228b66-8f5c-44b4-ad99-4439c57905a2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/Matching.lean:L133-L151
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Bipartite.exists_maximum_matching_min_cost. The node keeps its source
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

-- ---- from OAI.Combinatorics.SecondNeighborhood.Matching ----
namespace OAI

namespace SeymourSecondNeighborhood.Bipartite

variable {L R : Type*}

section DecidableEq

variable [DecidableEq L] [DecidableEq R]

end DecidableEq

section Finite

variable [Fintype L] [Fintype R]

theorem exists_maximum_matching (E : L → R → Prop) :
    ∃ M, IsMaximumMatching E M := by
  classical
  let candidates : Finset (Finset (L × R)) := Finset.univ.filter (IsMatching E)
  have hne : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates]
  obtain ⟨M, hM, hmax⟩ := candidates.exists_max_image Finset.card hne
  refine ⟨M, (Finset.mem_filter.mp hM).2, ?_⟩
  intro N hN
  exact hmax N (by simp [candidates, hN])

theorem exists_maximum_matching_min_cost (E : L → R → Prop)
    (cost : Finset (L × R) → ℕ) :
    ∃ M, IsMaximumMatching E M ∧
      ∀ N, IsMatching E N → N.card = M.card → cost M ≤ cost N := by
  classical
  obtain ⟨M₀, hM₀, hmax₀⟩ := exists_maximum_matching E
  let candidates : Finset (Finset (L × R)) :=
    Finset.univ.filter fun N => IsMatching E N ∧ N.card = M₀.card
  have hne : candidates.Nonempty := by
    refine ⟨M₀, ?_⟩
    simp [candidates, hM₀]
  obtain ⟨M, hM, hmin⟩ := candidates.exists_min_image cost hne
  have hM' : IsMatching E M ∧ M.card = M₀.card := (Finset.mem_filter.mp hM).2
  refine ⟨M, ⟨hM'.1, ?_⟩, ?_⟩
  · intro N hN
    rw [hM'.2]
    exact hmax₀ N hN
  · intro N hN hcard
    exact hmin N (by simp [candidates, hN, hcard, hM'.2])

end Finite

end SeymourSecondNeighborhood.Bipartite

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Bipartite


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Bipartite.exists_maximum_matching_min_cost := @_root_.OAI.SeymourSecondNeighborhood.Bipartite.exists_maximum_matching_min_cost
