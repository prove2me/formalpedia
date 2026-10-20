-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Pruning.augmented_matching_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:59:07.346968+00:00
-- url     : https://prove2.me/submissions/12c61513-4552-4a9e-827a-ef755c16eead

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/AugmentedGraph.lean:L249-L287
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Pruning.augmented_matching_card. The node keeps its source
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

-- ---- from OAI.Combinatorics.SecondNeighborhood.AugmentedGraph ----
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Bipartite

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {r : V → V → Prop} {R C : Finset (V × V)}

theorem originalLift_injective :
    Function.Injective (originalLift (r := r) (R := R) (C := C)) := by
  intro e f h
  exact Prod.ext (Sum.inl.inj (congrArg Prod.fst h))
    (Sum.inl.inj (congrArg Prod.snd h))

theorem alphaLift_injective :
    Function.Injective (alphaLift (r := r) (R := R) (C := C)) := by
  intro e f h
  exact Prod.ext (Sum.inr.inj (congrArg Prod.snd h))
    (Sum.inl.inj (congrArg Prod.fst h))

theorem betaLift_injective :
    Function.Injective (betaLift (r := r) (R := R) (C := C)) := by
  intro e f h
  exact Prod.ext (Sum.inr.inj (congrArg Prod.fst h))
    (Sum.inl.inj (congrArg Prod.snd h))

theorem augmented_matching_eq_three_images
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M) :
    M = (originalEdges M).image originalLift ∪
      (alphaEdges M).image alphaLift ∪ (betaEdges M).image betaLift := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨l, b⟩ := e
    cases l with
    | inl a =>
      cases b with
      | inl b =>
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨(a, b), mem_originalEdges.mpr he, rfl⟩))
      | inr z =>
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨(z, a), mem_alphaEdges.mpr he, rfl⟩))
    | inr z =>
      cases b with
      | inl b =>
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨(z, b), mem_betaEdges.mpr he, rfl⟩)
      | inr w => exact False.elim (hM.1 _ he)
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · rcases Finset.mem_union.mp he with he | he
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
        exact mem_originalEdges.mp ha
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
        exact mem_alphaEdges.mp ha
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      exact mem_betaEdges.mp ha

theorem augmented_matching_card
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M) :
    M.card = (originalEdges M).card + (alphaEdges M).card + (betaEdges M).card := by
  classical
  have hOA : Disjoint ((originalEdges M).image originalLift)
      ((alphaEdges M).image alphaLift) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨o, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨a, _, h⟩ := Finset.mem_image.mp hf
    have hright := congrArg Prod.snd h
    cases hright
  have hOB : Disjoint ((originalEdges M).image originalLift)
      ((betaEdges M).image betaLift) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨o, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, _, h⟩ := Finset.mem_image.mp hf
    have hleft := congrArg Prod.fst h
    cases hleft
  have hAB : Disjoint ((alphaEdges M).image alphaLift)
      ((betaEdges M).image betaLift) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, _, h⟩ := Finset.mem_image.mp hf
    have hleft := congrArg Prod.fst h
    cases hleft
  calc
    M.card = (((originalEdges M).image originalLift ∪
        (alphaEdges M).image alphaLift) ∪ (betaEdges M).image betaLift).card :=
      congrArg Finset.card (augmented_matching_eq_three_images hM)
    _ = _ := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hOB, hAB⟩),
        Finset.card_union_of_disjoint hOA,
        Finset.card_image_of_injective _ originalLift_injective,
        Finset.card_image_of_injective _ alphaLift_injective,
        Finset.card_image_of_injective _ betaLift_injective]

end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
open Bipartite


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Pruning.augmented_matching_card := @_root_.OAI.SeymourSecondNeighborhood.Pruning.augmented_matching_card
