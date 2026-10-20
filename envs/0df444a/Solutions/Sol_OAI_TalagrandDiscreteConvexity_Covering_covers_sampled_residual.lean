-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.covers_sampled_residual
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:32:58.108995+00:00
-- url     : https://prove2.me/submissions/2b12bb45-4a91-4126-b895-5fc927c6901d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringSampledFamilies.lean:L104-L127
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.covers_sampled_residual. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_TalagrandDiscreteConvexity
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Model
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Basic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_DyadicBins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteFibers
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringBasic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringSampledFamilies
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_exists_regular_tuple

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoveringSampledFamilies ----
namespace OAI

/-!
# Deterministic covers from a pair-sampling outcome

Every sampling outcome gives a cover.  The cost bounds count generators
with multiplicity, indexed by ordered pairs or injective ordered tuples.
No independence or probability estimate is needed for these pointwise
statements.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- Every pair-sampling outcome covers each set containing sufficiently
many original edges.  This includes `m = 0` and empty edge families. -/
theorem covers_sampled_residual [Fintype V] (H C0 : Family V) (m : ℕ)
    (sample : Sample (regularFamily H C0)) :
    Covers (C0 ∪ sampledFamily (regularFamily H C0) sample ∪
      residualFamily (regularFamily H C0) m sample) (denseFamily H m) := by
  classical
  intro S hS
  by_cases h0 : ∃ I ∈ C0, I ⊆ S
  · obtain ⟨I, hI, hIS⟩ := h0
    exact ⟨I, Finset.mem_union_left _ (Finset.mem_union_left _ hI), hIS⟩
  · obtain ⟨f, hf⟩ := exists_regular_tuple (mem_denseFamily.mp hS) h0
    by_cases havoid : Disjoint sample (tuplePairs f)
    · refine ⟨tupleUnion f,
        Finset.mem_union_right _ (mem_residualFamily.mpr ⟨f, havoid, rfl⟩), ?_⟩
      intro v hv
      obtain ⟨i, hi⟩ := mem_tupleUnion.mp hv
      exact hf i hi
    · obtain ⟨p, hp, hpf⟩ := Finset.not_disjoint_iff.mp havoid
      obtain ⟨i, j, rfl⟩ := mem_tuplePairs.mp hpf
      refine ⟨pairUnion (f.val i, f.val j), ?_, ?_⟩
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (mem_sampledFamily.mpr ⟨_, hp, rfl⟩))
      · exact Finset.union_subset (hf i) (hf j)

end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.covers_sampled_residual := @_root_.OAI.TalagrandDiscreteConvexity.Covering.covers_sampled_residual
