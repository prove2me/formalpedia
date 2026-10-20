-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.dyadic_residual_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:42:39.841189+00:00
-- url     : https://prove2.me/submissions/6e4f6501-5a23-4490-a64d-23262a44f435

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringNumericalBounds.lean:L115-L150
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.dyadic_residual_bound. The node keeps its source
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

/-- A dyadic growth factor is dominated by independent avoidance when each
block has one additional unit of exponential sampling budget. -/
theorem dyadic_residual_bound (a n : ℕ) (prob : ℝ)
    (hprob : prob ≤ 1)
    (hbudget : (a : ℝ) + 1 ≤ prob * (n : ℝ)) :
    ((2 : ℝ) ^ a) ^ n * (1 - prob) ^ (n * n) ≤ ((2 : ℝ) ^ n)⁻¹ := by
  have hnonneg : 0 ≤ 1 - prob := sub_nonneg.mpr hprob
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ a ≤ Real.exp (a : ℝ) := by
    calc
      (2 : ℝ) ^ a ≤ (Real.exp 1) ^ a :=
        pow_le_pow_left₀ (by norm_num) htwo a
      _ = Real.exp (a : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
  have hexponent : (a : ℝ) + (n : ℝ) * (-prob) ≤ -1 := by
    calc
      (a : ℝ) + (n : ℝ) * (-prob) = (a : ℝ) - prob * (n : ℝ) := by ring
      _ ≤ -1 := by linarith
  have hhalf : Real.exp (-1 : ℝ) ≤ (2 : ℝ)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos 1) (by norm_num)).mpr htwo
  have hbase : (2 : ℝ) ^ a * (1 - prob) ^ n ≤ (2 : ℝ)⁻¹ := by
    calc
      (2 : ℝ) ^ a * (1 - prob) ^ n ≤
          Real.exp (a : ℝ) * (Real.exp (-prob)) ^ n :=
        mul_le_mul hpow
          (pow_le_pow_left₀ hnonneg (Real.one_sub_le_exp_neg prob) n)
          (pow_nonneg hnonneg n) (Real.exp_nonneg _)
      _ = Real.exp ((a : ℝ) + (n : ℝ) * (-prob)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr hexponent
      _ ≤ (2 : ℝ)⁻¹ := hhalf
  simpa only [mul_pow, ← pow_mul, inv_pow] using
    pow_le_pow_left₀
      (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) a)
        (pow_nonneg hnonneg n)) hbase n

end TalagrandDiscreteConvexity.Covering.NumericalBounds

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.dyadic_residual_bound := @_root_.OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.dyadic_residual_bound
