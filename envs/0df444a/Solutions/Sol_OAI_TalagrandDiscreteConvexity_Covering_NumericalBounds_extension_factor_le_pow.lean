-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.extension_factor_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:41:12.899184+00:00
-- url     : https://prove2.me/submissions/3fb1d90c-6163-42c5-b959-ef6bd14928ca

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringNumericalBounds.lean:L57-L71
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.extension_factor_le_pow. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_NumericalBounds_extension_base_le_pow

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoveringNumericalBounds ----
namespace OAI

namespace TalagrandDiscreteConvexity.Covering.NumericalBounds

theorem T_pos (h : ℕ) : 0 < T h := by
  unfold T
  positivity

theorem T_nonneg (h : ℕ) : 0 ≤ T h := (T_pos h).le

/-- The extension factor from the weighted-degree estimate is at most
the stated natural power of two. -/
theorem extension_factor_le_pow (r h : ℕ) (hrh : r ≤ h) :
    T h * (1 + (r : ℝ) * (m h : ℝ)) ^ r ≤ (2 : ℝ) ^ A r h := by
  have hbase : 1 + (r : ℝ) * (m h : ℝ) ≤ (2 : ℝ) ^ (13 * h) := by
    exact_mod_cast extension_base_le_pow r h hrh
  calc
    T h * (1 + (r : ℝ) * (m h : ℝ)) ^ r ≤
        T h * ((2 : ℝ) ^ (13 * h)) ^ r :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase r) (T_nonneg h)
    _ = (2 : ℝ) ^ A r h := by
      rw [T, ← pow_mul, ← pow_add]
      congr 1
      unfold A
      ring

end TalagrandDiscreteConvexity.Covering.NumericalBounds

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.extension_factor_le_pow := @_root_.OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.extension_factor_le_pow
