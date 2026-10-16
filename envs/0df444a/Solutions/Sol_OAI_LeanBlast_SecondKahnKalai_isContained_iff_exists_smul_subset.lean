-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.isContained_iff_exists_smul_subset
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:17:08.970204+00:00
-- url     : https://prove2.me/submissions/26a4c67d-a92e-45c1-969b-7ea423b26805

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/GraphContainment.lean:L26-L49
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.isContained_iff_exists_smul_subset. The node keeps its source
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

-- ---- from OAI.Combinatorics.GraphThreshold.GraphContainment ----
namespace OAI

noncomputable section

open scoped Pointwise

namespace LeanBlast.SecondKahnKalai

variable {n : ℕ} {V : Type*}

theorem mapped_copy_le {U W : Type*} {H : SimpleGraph U} {G : SimpleGraph W}
    (c : H.Copy G) : H.map c.toEmbedding ≤ G := by
  intro a b hab
  obtain ⟨v, w, hvw, rfl, rfl⟩ := (SimpleGraph.map_adj c.toEmbedding H a b).mp hab
  exact c.toHom.map_adj hvw

/-- Containment of a graph is equivalent to containing a permuted copy of its
edges. The embedding carries *all* vertices, so isolated vertices are retained. -/
theorem isContained_iff_exists_smul_subset (f : V ↪ Fin n) (H : SimpleGraph V)
    (W : Finset (Edge n)) :
    H.IsContained (graphOfEdges W) ↔
      ∃ σ : Equiv.Perm (Fin n), σ • graphEdges (H.map f) ⊆ W := by
  constructor
  · rintro ⟨c⟩
    obtain ⟨σ, hσ⟩ := exists_perm_comp_embedding f c.toEmbedding
    refine ⟨σ, graphOfEdges_le_iff.mp ?_⟩
    rw [graphOfEdges_smul, graphOfEdges_graphEdges, SimpleGraph.map_map]
    have heq : (fun v => σ.toEmbedding (f v)) = c.toEmbedding := by
      funext v
      exact hσ v
    change H.map (fun v => σ.toEmbedding (f v)) ≤ graphOfEdges W
    rw [heq]
    exact mapped_copy_le c
  · rintro ⟨σ, hσ⟩
    have hf : H.IsContained (H.map f) :=
      ⟨(SimpleGraph.Embedding.map f H).toCopy⟩
    have hperm : (H.map f).IsContained (graphOfEdges (σ • graphEdges (H.map f))) := by
      rw [graphOfEdges_smul, graphOfEdges_graphEdges]
      exact ⟨(SimpleGraph.Iso.map σ _).toCopy⟩
    exact hf.trans (hperm.trans (SimpleGraph.IsContained.of_le (graphOfEdges_mono hσ)))

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped Pointwise


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.isContained_iff_exists_smul_subset := @_root_.OAI.LeanBlast.SecondKahnKalai.isContained_iff_exists_smul_subset
