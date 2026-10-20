-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Pruning.alphaEdges_image
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:55:43.735291+00:00
-- url     : https://prove2.me/submissions/53dc44f9-e783-4836-81e8-42c4594b0fcb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/AugmentedGraph.lean:L171-L192
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Pruning.alphaEdges_image. The node keeps its source
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

theorem alphaEdges_image
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M) :
    (alphaEdges M).image alphaLift = M.filter (fun e => e.2.isRight) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨⟨z, a⟩, ha, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_filter.mpr ⟨mem_alphaEdges.mp ha, rfl⟩
  · intro he
    obtain ⟨he, hright⟩ := Finset.mem_filter.mp he
    obtain ⟨l, b⟩ := e
    cases l with
    | inl a =>
      cases b with
      | inl b => simp at hright
      | inr z => exact Finset.mem_image.mpr ⟨(z, a), mem_alphaEdges.mpr he, rfl⟩
    | inr z =>
      cases b with
      | inl b => simp at hright
      | inr w => exact False.elim (hM.1 _ he)

end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
open Bipartite


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Pruning.alphaEdges_image := @_root_.OAI.SeymourSecondNeighborhood.Pruning.alphaEdges_image
