-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.exponent_budget_nat
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:41:56.583644+00:00
-- url     : https://prove2.me/submissions/d6284a19-2139-42da-bb86-114af2c55213

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringNumericalBounds.lean:L73-L100
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.exponent_budget_nat. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringNumericalBounds

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoveringNumericalBounds ----
namespace OAI

namespace TalagrandDiscreteConvexity.Covering.NumericalBounds

/-- The quadratic polynomial exponent is dominated by the sampling budget. -/
theorem exponent_budget_nat (r h : ℕ) (hrh : r ≤ h) (hh : 64 ≤ h) :
    A r h + 1 ≤ 2 ^ (4 * h) := by
  have hh1 : 1 ≤ h := by omega
  have hrh' : r * h ≤ h * h := Nat.mul_le_mul_right h hrh
  have hh' : h ≤ h * h := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left h hh1
  have hquadratic : A r h + 1 ≤ 18 * h ^ 2 := by
    unfold A
    nlinarith
  have hpow : h ≤ 2 ^ h := Nat.le_of_lt Nat.lt_two_pow_self
  have hsquare : h ^ 2 ≤ 2 ^ (2 * h) := by
    calc
      h ^ 2 ≤ (2 ^ h) ^ 2 := Nat.pow_le_pow_left hpow 2
      _ = 2 ^ (2 * h) := by rw [← pow_mul, Nat.mul_comm h 2]
  have h18 : 18 ≤ 2 ^ (2 * h) := by
    calc
      18 ≤ (2 : ℕ) ^ 5 := by norm_num
      _ ≤ 2 ^ (2 * h) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
  calc
    A r h + 1 ≤ 18 * h ^ 2 := hquadratic
    _ ≤ 18 * 2 ^ (2 * h) := Nat.mul_le_mul_left 18 hsquare
    _ ≤ 2 ^ (2 * h) * 2 ^ (2 * h) := Nat.mul_le_mul_right _ h18
    _ = 2 ^ (4 * h) := by
      rw [← pow_add]
      congr 1
      omega

end TalagrandDiscreteConvexity.Covering.NumericalBounds

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.exponent_budget_nat := @_root_.OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.exponent_budget_nat
