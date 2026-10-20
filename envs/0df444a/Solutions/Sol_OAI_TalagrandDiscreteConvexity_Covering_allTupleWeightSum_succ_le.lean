-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.allTupleWeightSum_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:37:37.168282+00:00
-- url     : https://prove2.me/submissions/191ad2b9-028c-47e8-99c4-5a0460d3ad76

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringResidualTuples.lean:L134-L159
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.allTupleWeightSum_succ_le. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_allTupleWeightSum_succ

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

/-- An unrestricted `t`-tuple of `r`-element edges uses at most `r * t` vertices. -/
theorem allTupleUnion_card_le {H : Family V} {r t : ℕ}
    (uniform : ∀ e ∈ H, (e : Finset V).card = r) (f : Fin t → ↥H) :
    (allTupleUnion f).card ≤ r * t := by
  classical
  calc
    (allTupleUnion f).card ≤ ∑ i : Fin t, (f i).val.card :=
      Finset.card_biUnion_le
    _ = ∑ _i : Fin t, r :=
      Finset.sum_congr rfl (fun i _ => uniform (f i).val (f i).property)
    _ = r * t := by simp [Nat.mul_comm]

/-- The extension estimate yields the unrestricted recurrence up to a fixed length. -/
theorem allTupleWeightSum_succ_le (H : Family V) {rho T : ℝ} {r m t : ℕ}
    (hrho : 0 ≤ rho) (hT : 0 ≤ T)
    (uniform : ∀ e ∈ H, (e : Finset V).card = r)
    (extension : ∀ B : Finset V,
      (∑ e ∈ H, rho ^ (e \ B).card) ≤ T * (1 + (B.card : ℝ)) ^ r)
    (ht : t ≤ m) :
    allTupleWeightSum H rho (t + 1) ≤
      (T * (1 + ((r * m : ℕ) : ℝ)) ^ r) * allTupleWeightSum H rho t := by
  classical
  rw [allTupleWeightSum_succ, allTupleWeightSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro f _
  have hcard : (allTupleUnion f).card ≤ r * m :=
    (allTupleUnion_card_le uniform f).trans (Nat.mul_le_mul_left r ht)
  have hcast : ((allTupleUnion f).card : ℝ) ≤ ((r * m : ℕ) : ℝ) :=
    Nat.cast_le.mpr hcard
  have hpower : (1 + ((allTupleUnion f).card : ℝ)) ^ r ≤
      (1 + ((r * m : ℕ) : ℝ)) ^ r :=
    pow_le_pow_left₀ (add_nonneg zero_le_one (Nat.cast_nonneg _))
      (add_le_add (le_refl (1 : ℝ)) hcast) r
  have hext : (∑ e ∈ H, rho ^ (e \ allTupleUnion f).card) ≤
      T * (1 + ((r * m : ℕ) : ℝ)) ^ r :=
    (extension (allTupleUnion f)).trans (mul_le_mul_of_nonneg_left hpower hT)
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hext (pow_nonneg hrho (allTupleUnion f).card)

end

end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.allTupleWeightSum_succ_le := @_root_.OAI.TalagrandDiscreteConvexity.Covering.allTupleWeightSum_succ_le
