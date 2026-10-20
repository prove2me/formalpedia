-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.residual_cost_le_inv_pow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:43:27.550446+00:00
-- url     : https://prove2.me/submissions/77589527-0564-44ea-80e8-8c8f2de4c686

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringNumericalBounds.lean:L152-L168
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.residual_cost_le_inv_pow. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_NumericalBounds_dyadic_residual_bound
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_NumericalBounds_exponent_budget_nat
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_NumericalBounds_extension_factor_le_pow

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoveringNumericalBounds ----
namespace OAI

namespace TalagrandDiscreteConvexity.Covering.NumericalBounds

theorem T_pos (h : ℕ) : 0 < T h := by
  unfold T
  positivity

theorem T_nonneg (h : ℕ) : 0 ≤ T h := (T_pos h).le

/-- The chosen pair probability times the tuple length is exactly the
weighted-degree threshold. -/
theorem p_mul_m (h : ℕ) : p h * (m h : ℝ) = T h := by
  simp only [p, m, T, Nat.cast_pow, Nat.cast_ofNat]
  rw [show 12 * h = 8 * h + 4 * h by omega, pow_add, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), one_mul]

theorem exponent_budget (r h : ℕ) (hrh : r ≤ h) (hh : 64 ≤ h) :
    (A r h : ℝ) + 1 ≤ p h * (m h : ℝ) := by
  rw [p_mul_m]
  unfold T
  exact_mod_cast exponent_budget_nat r h hrh hh

/-- The actual residual tuple-growth factor times its exact avoidance
probability is at most the reciprocal dyadic tuple-length power. -/
theorem residual_cost_le_inv_pow (r h : ℕ) (hrh : r ≤ h) (hh : 64 ≤ h) :
    (T h * (1 + (r : ℝ) * (m h : ℝ)) ^ r) ^ m h *
        (1 - p h) ^ (m h * m h) ≤ ((2 : ℝ) ^ m h)⁻¹ := by
  have hfactor : 0 ≤ T h * (1 + (r : ℝ) * (m h : ℝ)) ^ r :=
    mul_nonneg (T_nonneg h) (pow_nonneg (by positivity) r)
  calc
    (T h * (1 + (r : ℝ) * (m h : ℝ)) ^ r) ^ m h *
        (1 - p h) ^ (m h * m h) ≤
        ((2 : ℝ) ^ A r h) ^ m h * (1 - p h) ^ (m h * m h) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hfactor (extension_factor_le_pow r h hrh) (m h))
        (pow_nonneg (sub_nonneg.mpr (p_le_one h)) _)
    _ ≤ ((2 : ℝ) ^ m h)⁻¹ :=
      dyadic_residual_bound (A r h) (m h) (p h) (p_le_one h)
        (exponent_budget r h hrh hh)

end TalagrandDiscreteConvexity.Covering.NumericalBounds

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.residual_cost_le_inv_pow := @_root_.OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.residual_cost_le_inv_pow
