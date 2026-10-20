-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Pruning.betaEdges_isMatching
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:54:52.608956+00:00
-- url     : https://prove2.me/submissions/8b666ed6-08a9-445a-8616-ff9c0baec36a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/AugmentedGraph.lean:L133-L147
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Pruning.betaEdges_isMatching. The node keeps its source
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

theorem betaLift_injective :
    Function.Injective (betaLift (r := r) (R := R) (C := C)) := by
  intro e f h
  exact Prod.ext (Sum.inr.inj (congrArg Prod.fst h))
    (Sum.inl.inj (congrArg Prod.snd h))

theorem betaEdges_isMatching
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M) :
    IsMatching (BetaRelation r R C) (betaEdges M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    exact hM.1 (betaLift e) (mem_betaEdges.mp he)
  · intro e he f hf h
    apply betaLift_injective
    exact hM.2.1 (mem_betaEdges.mp he) (mem_betaEdges.mp hf)
      (congrArg Sum.inr h)
  · intro e he f hf h
    apply betaLift_injective
    exact hM.2.2 (mem_betaEdges.mp he) (mem_betaEdges.mp hf)
      (congrArg Sum.inl h)

end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
open Bipartite


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Pruning.betaEdges_isMatching := @_root_.OAI.SeymourSecondNeighborhood.Pruning.betaEdges_isMatching
