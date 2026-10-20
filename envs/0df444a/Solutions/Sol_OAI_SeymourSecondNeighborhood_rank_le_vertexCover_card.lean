-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.rank_le_vertexCover_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:05:18.930101+00:00
-- url     : https://prove2.me/submissions/9acaf70b-e9bd-4593-8591-a58775bc8218

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/GenericRankSupport.lean:L22-L56
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.rank_le_vertexCover_card. The node keeps its source
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

-- ---- from OAI.Combinatorics.SecondNeighborhood.GenericRankSupport ----
namespace OAI

namespace SeymourSecondNeighborhood

variable {I J K : Type*} [Fintype I] [Fintype J] [Field K]

omit [Fintype I] in
private theorem matrix_rank_add_le (B C : Matrix I J K) :
    (B + C).rank ≤ B.rank + C.rank := by
  have hadd : (B + C).mulVecLin = B.mulVecLin + C.mulVecLin :=
    LinearMap.ext fun x => Matrix.add_mulVec B C x
  change Module.finrank K (LinearMap.range (B + C).mulVecLin) ≤
    Module.finrank K (LinearMap.range B.mulVecLin) +
      Module.finrank K (LinearMap.range C.mulVecLin)
  rw [hadd]
  exact (Submodule.finrank_mono
    (LinearMap.range_add_le B.mulVecLin C.mulVecLin)).trans
      (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem rank_le_vertexCover_card (A : Matrix I J K) (s : Finset I) (t : Finset J)
    (hcover : ∀ i j, A i j ≠ 0 → i ∈ s ∨ j ∈ t) :
    A.rank ≤ s.card + t.card := by
  classical
  let B : Matrix I J K := fun i j => if i ∈ s then A i j else 0
  let C : Matrix I J K := fun i j => if i ∈ s then 0 else A i j
  have hsum : A = B + C := by
    ext i j
    change A i j = B i j + C i j
    by_cases hi : i ∈ s <;> simp [B, C, hi]
  have hB : B.rank ≤ s.card := by
    apply Matrix.rank_le_card_of_support_subset B s
    rw [Function.support_subset_iff']
    intro i hi
    change i ∉ s at hi
    funext j
    change (if i ∈ s then A i j else 0) = 0
    simp [hi]
  have hC : C.transpose.rank ≤ t.card := by
    apply Matrix.rank_le_card_of_support_subset C.transpose t
    rw [Function.support_subset_iff']
    intro j hj
    change j ∉ t at hj
    funext i
    change (if i ∈ s then 0 else A i j) = 0
    by_cases hi : i ∈ s
    · simp [hi]
    · have hA : A i j = 0 := by
        by_contra h
        exact (hcover i j h).elim hi hj
      simp [hi, hA]
  calc
    A.rank = (B + C).rank := congrArg Matrix.rank hsum
    _ ≤ B.rank + C.rank := matrix_rank_add_le B C
    _ ≤ s.card + t.card := add_le_add hB (by simpa only [Matrix.rank_transpose] using hC)

end SeymourSecondNeighborhood

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.rank_le_vertexCover_card := @_root_.OAI.SeymourSecondNeighborhood.rank_le_vertexCover_card
