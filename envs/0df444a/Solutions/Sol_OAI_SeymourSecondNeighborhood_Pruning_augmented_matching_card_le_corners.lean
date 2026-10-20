-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Pruning.augmented_matching_card_le_corners
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:22:18.241811+00:00
-- url     : https://prove2.me/submissions/6cf8e3d6-bc63-426c-8ad5-a1606238f72a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/AugmentedRankBound.lean:L12-L49
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Pruning.augmented_matching_card_le_corners. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMaps
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelRestriction
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MaxSupportKernel
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelConflict
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankCoefficients
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMapsPolynomial
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankGlobalMinors
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelBasisLifts
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_augmented_matching_card
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_originalEdges_isMatching
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_original_add_auxiliary_card_le_corners

-- ---- from OAI.Combinatorics.SecondNeighborhood.AugmentedGraph ----
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Bipartite

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {r : V → V → Prop} {R C : Finset (V × V)}

theorem original_alpha_left_ne
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M)
    {e : ↥R × ↥C} (he : e ∈ originalEdges M)
    {a : ↥(Z r R C) × ↥R} (ha : a ∈ alphaEdges M) : e.1 ≠ a.2 := by
  intro h
  have heq := hM.2.1 (mem_originalEdges.mp he) (mem_alphaEdges.mp ha)
    (congrArg Sum.inl h)
  have hright := congrArg Prod.snd heq
  cases hright

theorem original_beta_right_ne
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M)
    {e : ↥R × ↥C} (he : e ∈ originalEdges M)
    {b : ↥(Z r R C) × ↥C} (hb : b ∈ betaEdges M) : e.2 ≠ b.2 := by
  intro h
  have heq := hM.2.2 (mem_originalEdges.mp he) (mem_betaEdges.mp hb)
    (congrArg Sum.inl h)
  have hleft := congrArg Prod.fst heq
  cases hleft

end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.AugmentedRankBound ----
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Bipartite

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem augmented_matching_card_le_corners
    (r : X → X → Prop) (R C : Finset (X × X))
    (M : Finset (LeftVertex r R C × RightVertex r R C))
    (hM : IsMatching (AugmentedEdge r R C) M)
    (hα : IsMaximumMatching (AlphaRelation r R C) (alphaEdges M))
    (hβ : IsMaximumMatching (BetaRelation r R C) (betaEdges M)) :
    M.card ≤ (Z r R C).card + (H r R C).card := by
  classical
  have hαrelation : matrixLSupport r R C = AlphaRelation r R C := by
    funext z a
    exact propext (matrixLSupport_iff_leftCovers r R C z a)
  have hβrelation : matrixNTransposeSupport r R C = BetaRelation r R C := by
    funext z b
    exact propext (matrixNTransposeSupport_iff_rightCovers r R C z b)
  have hα' : IsMaximumMatching (matrixLSupport r R C) (alphaEdges M) := by
    rw [hαrelation]
    exact hα
  have hβ' : IsMaximumMatching (matrixNTransposeSupport r R C) (betaEdges M) := by
    rw [hβrelation]
    exact hβ
  have hOriginal := originalEdges_isMatching hM
  have hleft : Function.Injective (fun e : ↥(originalEdges M) => e.val.1) := by
    intro e f hef
    apply Subtype.ext
    exact hOriginal.2.1 e.property f.property hef
  have hright : Function.Injective (fun e : ↥(originalEdges M) => e.val.2) := by
    intro e f hef
    apply Subtype.ext
    exact hOriginal.2.2 e.property f.property hef
  have hbound := original_add_auxiliary_card_le_corners
    r R C (alphaEdges M) (betaEdges M) hα' hβ'
    (fun e : ↥(originalEdges M) => e.val.1)
    (fun e : ↥(originalEdges M) => e.val.2) hleft hright
    (fun e f => original_alpha_left_ne hM e.property f.property)
    (fun e f => original_beta_right_ne hM e.property f.property)
    (fun e => hOriginal.1 e.val e.property)
  rw [augmented_matching_card hM]
  simpa only [Fintype.card_coe] using hbound

end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
open Bipartite


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Pruning.augmented_matching_card_le_corners := @_root_.OAI.SeymourSecondNeighborhood.Pruning.augmented_matching_card_le_corners
