-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.outright_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:23:24.479194+00:00
-- url     : https://prove2.me/submissions/8dce985c-f65c-4d86-9bc6-e67dbec9e192

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/BinNumerics.lean:L122-L140
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.outright_weight_le. The node keeps its source
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

-- ---- from OAI.Combinatorics.DiscreteConvexity.BinNumerics ----
namespace OAI

namespace TalagrandDiscreteConvexity

open scoped BigOperators

/-- Large weights can be bought outright at a total factor of at most `1/64`. -/
theorem outright_weight_le {r : ℕ} {q w : ℝ} (hr : 1 ≤ r) (hq : 0 ≤ q)
    (hw : (1 / 2 : ℝ) ^ (64 * r) ≤ w) :
    (q / (2 : ℝ) ^ 70) ^ r ≤ (1 / 64 : ℝ) * q ^ r * w := by
  have hsmall : (1 / 2 : ℝ) ^ (6 * r) ≤ (1 / 64 : ℝ) := by
    have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (show 6 ≤ 6 * r by omega)
    norm_num at h ⊢
    exact h
  have hqpow : 0 ≤ q ^ r := pow_nonneg hq _
  calc
    (q / (2 : ℝ) ^ 70) ^ r = q ^ r * (1 / 2 : ℝ) ^ (70 * r) := by
      simp only [div_eq_mul_inv, mul_pow, one_mul, pow_mul, inv_pow]
    _ = q ^ r * ((1 / 2 : ℝ) ^ (6 * r) * (1 / 2 : ℝ) ^ (64 * r)) := by
      rw [← pow_add, show 6 * r + 64 * r = 70 * r by omega]
    _ ≤ q ^ r * ((1 / 64 : ℝ) * w) := by
      apply mul_le_mul_of_nonneg_left _ hqpow
      exact mul_le_mul hsmall hw (by positivity) (by norm_num)
    _ = (1 / 64 : ℝ) * q ^ r * w := by ring

end TalagrandDiscreteConvexity

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.outright_weight_le := @_root_.OAI.TalagrandDiscreteConvexity.outright_weight_le
