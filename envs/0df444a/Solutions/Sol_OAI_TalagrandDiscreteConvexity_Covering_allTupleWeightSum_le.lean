-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.allTupleWeightSum_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:38:20.063102+00:00
-- url     : https://prove2.me/submissions/39302435-f5c0-4243-814f-2e2f2c7ff96c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringResidualTuples.lean:L161-L185
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.allTupleWeightSum_le. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_allTupleWeightSum_succ_le

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

/-- Iteration of the actual recurrence bounds every unrestricted sum up to `m`. -/
theorem allTupleWeightSum_le (H : Family V) {rho T : ℝ} {r m : ℕ}
    (hrho : 0 ≤ rho) (hT : 0 ≤ T)
    (uniform : ∀ e ∈ H, (e : Finset V).card = r)
    (extension : ∀ B : Finset V,
      (∑ e ∈ H, rho ^ (e \ B).card) ≤ T * (1 + (B.card : ℝ)) ^ r)
    (t : ℕ) (ht : t ≤ m) :
    allTupleWeightSum H rho t ≤ (T * (1 + ((r * m : ℕ) : ℝ)) ^ r) ^ t := by
  have hfactor : 0 ≤ T * (1 + ((r * m : ℕ) : ℝ)) ^ r :=
    mul_nonneg hT (pow_nonneg (add_nonneg zero_le_one (Nat.cast_nonneg _)) r)
  revert ht
  induction t with
  | zero => intro ht; simp
  | succ t ih =>
      intro ht
      have htm : t ≤ m := Nat.le_of_succ_le ht
      calc
        allTupleWeightSum H rho (t + 1) ≤
            (T * (1 + ((r * m : ℕ) : ℝ)) ^ r) * allTupleWeightSum H rho t :=
          allTupleWeightSum_succ_le H hrho hT uniform extension htm
        _ ≤ (T * (1 + ((r * m : ℕ) : ℝ)) ^ r) *
            (T * (1 + ((r * m : ℕ) : ℝ)) ^ r) ^ t :=
          mul_le_mul_of_nonneg_left (ih htm) hfactor
        _ = (T * (1 + ((r * m : ℕ) : ℝ)) ^ r) ^ (t + 1) := by
          rw [pow_succ, mul_comm]

end

end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.allTupleWeightSum_le := @_root_.OAI.TalagrandDiscreteConvexity.Covering.allTupleWeightSum_le
