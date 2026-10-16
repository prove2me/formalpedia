-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.expectedCopies_formula
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:19:42.739324+00:00
-- url     : https://prove2.me/submissions/8adcd7d6-5175-4ce4-974a-199fdd063351

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/GraphExpectedCopies.lean:L106-L137
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.expectedCopies_formula. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphExpectedCopies
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulliProbability_subset

-- ---- from OAI.Combinatorics.GraphThreshold.GraphExpectedCopies ----
namespace OAI

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

universe u

variable {n : ℕ} {V : Type u}

theorem copyCount_eq_complete_card (G : SimpleGraph (Fin n)) (F : SimpleGraph V) :
    G.copyCount F = Nat.card
      {K : (⊤ : SimpleGraph (Fin n)).Subgraph //
        Nonempty (F ≃g K.coe) ∧ K.spanningCoe ≤ G} := by
  classical
  calc
    G.copyCount F = Fintype.card {K : G.Subgraph // Nonempty (F ≃g K.coe)} := by
      rw [SimpleGraph.copyCount, Fintype.card_subtype]
      apply congrArg Finset.card
      ext K
      simp
    _ = Fintype.card {K : (⊤ : SimpleGraph (Fin n)).Subgraph //
        Nonempty (F ≃g K.coe) ∧ K.spanningCoe ≤ G} :=
      Fintype.card_congr (completeCopyEquiv G F)
    _ = _ := Nat.card_eq_fintype_card.symm

theorem copyCount_eq_sum_complete (G : SimpleGraph (Fin n)) (F : SimpleGraph V) :
    (G.copyCount F : ℝ) =
      ∑ K : (⊤ : SimpleGraph (Fin n)).Subgraph,
        if Nonempty (F ≃g K.coe) then (if K.spanningCoe ≤ G then (1 : ℝ) else 0)
        else 0 := by
  classical
  rw [copyCount_eq_complete_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones]
  simp only [Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro K _
  by_cases hF : Nonempty (F ≃g K.coe) <;> simp [hF]

/-- Adding ambient isolated vertices does not change the edge count. -/
theorem edgeCount_spanningCoe {G : SimpleGraph (Fin n)} (K : G.Subgraph) :
    edgeCount K.spanningCoe = edgeCount K.coe := by
  unfold edgeCount
  rw [SimpleGraph.Subgraph.edgeSet_spanningCoe, ← K.image_coe_edgeSet_coe]
  exact Nat.card_congr
    (Equiv.Set.image (Sym2.map (Subtype.val : K.verts → Fin n)) K.coe.edgeSet
      (Sym2.map.injective Subtype.val_injective)).symm

theorem subgraph_survival_probability (p : ℝ)
    (K : (⊤ : SimpleGraph (Fin n)).Subgraph) :
    bernoulliProbability p (fun W : Finset (Edge n) =>
      K.spanningCoe ≤ graphOfEdges W) = p ^ edgeCount K.coe := by
  have h : ∀ W : Finset (Edge n),
      K.spanningCoe ≤ graphOfEdges W ↔ graphEdges K.spanningCoe ⊆ W := by
    intro W
    calc
      K.spanningCoe ≤ graphOfEdges W ↔
          graphOfEdges (graphEdges K.spanningCoe) ≤ graphOfEdges W := by
        rw [graphOfEdges_graphEdges]
      _ ↔ graphEdges K.spanningCoe ⊆ W := graphOfEdges_le_iff
  simp_rw [h]
  rw [bernoulliProbability_subset, card_graphEdges, edgeCount_spanningCoe]

/-- The exact expected number of unlabelled, non-induced copies. The counted
objects include their vertex sets, so the identity retains isolated vertices. -/
theorem expectedCopies_formula (n : ℕ) (p : ℝ) (F : SimpleGraph V) :
    expectedCopies n p F =
      ((⊤ : SimpleGraph (Fin n)).copyCount F : ℝ) * p ^ edgeCount F := by
  classical
  calc
    expectedCopies n p F =
        ∑ K : (⊤ : SimpleGraph (Fin n)).Subgraph,
          if Nonempty (F ≃g K.coe) then p ^ edgeCount F else 0 := by
      unfold expectedCopies bernoulliExpectation
      simp_rw [copyCount_eq_sum_complete, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro K _
      by_cases hK : Nonempty (F ≃g K.coe)
      · simp only [hK, ite_true]
        have hsurv := subgraph_survival_probability p K
        have hedge : edgeCount K.coe = edgeCount F :=
          (Nat.card_congr hK.some.mapEdgeSet).symm
        rw [hedge] at hsurv
        rw [← hsurv]
        unfold bernoulliProbability
        apply Finset.sum_congr rfl
        intro W _
        by_cases hW : K.spanningCoe ≤ graphOfEdges W <;> simp [hW]
      · simp [hK]
    _ = ((⊤ : SimpleGraph (Fin n)).copyCount F : ℝ) * p ^ edgeCount F := by
      rw [copyCount_eq_sum_complete, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro K _
      by_cases hK : Nonempty (F ≃g K.coe) <;> simp [hK]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
attribute [local instance] Classical.propDecidable


theorem solution.{u} : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.expectedCopies_formula.{u} := @_root_.OAI.LeanBlast.SecondKahnKalai.expectedCopies_formula.{u}
