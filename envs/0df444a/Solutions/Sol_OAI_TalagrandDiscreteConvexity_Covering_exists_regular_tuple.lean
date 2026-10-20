-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.exists_regular_tuple
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:32:10.597985+00:00
-- url     : https://prove2.me/submissions/b5ab0aa1-c9c5-4523-be3e-0e15a25d7767

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringSampledFamilies.lean:L77-L102
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.exists_regular_tuple. The node keeps its source
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

/-- A large contained-edge family can be enumerated injectively inside
the regular edges, provided the set avoids the initial generators. -/
theorem exists_regular_tuple {H C0 : Family V} {m : ℕ} {S : Finset V}
    (hm : m ≤ (H.filter (fun e => e ⊆ S)).card)
    (h0 : ¬∃ I ∈ C0, I ⊆ S) :
    ∃ f : EdgeTuple (regularFamily H C0) m, ∀ i, (f.val i).val ⊆ S := by
  classical
  let K := H.filter (fun e => e ⊆ S)
  have hKregular : K ⊆ regularFamily H C0 := by
    intro e he
    obtain ⟨heH, heS⟩ := Finset.mem_filter.mp he
    refine mem_regularFamily.mpr ⟨heH, ?_⟩
    intro I hI hIe
    exact h0 ⟨I, hI, Finset.Subset.trans hIe heS⟩
  have hcard : Fintype.card (Fin m) ≤ Fintype.card ↥K := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using hm
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard
  let f : EdgeTuple (regularFamily H C0) m :=
    ⟨fun i => ⟨(g i).val, hKregular (g i).property⟩, by
      intro i j hij
      apply g.injective
      apply Subtype.ext
      exact congrArg (Subtype.val : ↥(regularFamily H C0) → Finset V) hij⟩
  refine ⟨f, ?_⟩
  intro i
  exact (Finset.mem_filter.mp (g i).property).2

end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.exists_regular_tuple := @_root_.OAI.TalagrandDiscreteConvexity.Covering.exists_regular_tuple
