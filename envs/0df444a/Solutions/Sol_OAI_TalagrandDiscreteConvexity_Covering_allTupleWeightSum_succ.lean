-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.allTupleWeightSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:35:55.074997+00:00
-- url     : https://prove2.me/submissions/11392ef8-91d2-419b-bc40-684e7560bc49

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringResidualTuples.lean:L94-L115
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.allTupleWeightSum_succ. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteProbability
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bernoulli
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringResidualTuples

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoveringResidualTuples ----
namespace OAI

/-!
# The total weight of residual tuples

We bound the sum over injective edge tuples by the sum over all edge tuples.
Splitting an unrestricted tuple into its first edge and its tail gives an
exact weighted recurrence. The per-union extension bound then controls every
step. No nonemptiness assumption on the edge family is needed.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

noncomputable section

/-- Splitting a tuple separates its old union from the newly chosen edge. -/
theorem allTupleUnion_cons {H : Family V} {t : ℕ}
    (e : ↥H) (f : Fin t → ↥H) :
    allTupleUnion (Fin.cons e f) = allTupleUnion f ∪ e.val := by
  ext v
  simp [allTupleUnion, Fin.exists_fin_succ, or_comm]

/-- Union weight factors exactly into the prefix weight and its extension cost. -/
theorem allTupleWeight_cons {H : Family V} {t : ℕ} (rho : ℝ)
    (e : ↥H) (f : Fin t → ↥H) :
    rho ^ (allTupleUnion (Fin.cons e f)).card =
      rho ^ (allTupleUnion f).card * rho ^ (e.val \ allTupleUnion f).card := by
  rw [allTupleUnion_cons, Finset.union_comm,
    ← Finset.card_sdiff_add_card, pow_add, mul_comm]

/-- Exact recurrence for the unrestricted sum, obtained by reindexing with `Fin.cons`. -/
theorem allTupleWeightSum_succ (H : Family V) (rho : ℝ) (t : ℕ) :
    allTupleWeightSum H rho (t + 1) =
      ∑ f : Fin t → ↥H, rho ^ (allTupleUnion f).card *
        (∑ e ∈ H, rho ^ (e \ allTupleUnion f).card) := by
  classical
  calc
    allTupleWeightSum H rho (t + 1) =
        ∑ p : ↥H × (Fin t → ↥H),
          rho ^ (allTupleUnion (Fin.cons p.1 p.2)).card := by
      exact ((Fin.consEquiv (fun _ : Fin (t + 1) => ↥H)).sum_comp
        (fun f => rho ^ (allTupleUnion f).card)).symm
    _ = ∑ f : Fin t → ↥H, ∑ e : ↥H,
        rho ^ (allTupleUnion (Fin.cons e f)).card :=
      Fintype.sum_prod_type_right _
    _ = ∑ f : Fin t → ↥H, rho ^ (allTupleUnion f).card *
        (∑ e ∈ H, rho ^ (e \ allTupleUnion f).card) := by
      apply Finset.sum_congr rfl
      intro f _
      simp_rw [allTupleWeight_cons]
      rw [← Finset.mul_sum, Finset.sum_coe_sort H
        (fun e : Finset V => rho ^ (e \ allTupleUnion f).card)]

end

end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.allTupleWeightSum_succ := @_root_.OAI.TalagrandDiscreteConvexity.Covering.allTupleWeightSum_succ
