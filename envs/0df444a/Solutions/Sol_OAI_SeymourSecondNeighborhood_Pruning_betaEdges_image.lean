-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Pruning.betaEdges_image
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:58:23.080047+00:00
-- url     : https://prove2.me/submissions/c31e475c-d63f-46e9-99d2-21a2c7f73077

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/AugmentedGraph.lean:L194-L212
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Pruning.betaEdges_image. The node keeps its source
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

theorem betaEdges_image
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M) :
    (betaEdges M).image betaLift = M.filter (fun e => e.1.isRight) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨⟨z, b⟩, hb, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_filter.mpr ⟨mem_betaEdges.mp hb, rfl⟩
  · intro he
    obtain ⟨he, hleft⟩ := Finset.mem_filter.mp he
    obtain ⟨l, b⟩ := e
    cases l with
    | inl a => simp at hleft
    | inr z =>
      cases b with
      | inl b => exact Finset.mem_image.mpr ⟨(z, b), mem_betaEdges.mpr he, rfl⟩
      | inr w => exact False.elim (hM.1 _ he)

end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
open Bipartite


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Pruning.betaEdges_image := @_root_.OAI.SeymourSecondNeighborhood.Pruning.betaEdges_image
