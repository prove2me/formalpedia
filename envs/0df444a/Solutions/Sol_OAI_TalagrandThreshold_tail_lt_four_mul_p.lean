-- Prove2me | solution 1 for OAI.TalagrandThreshold.tail_lt_four_mul_p
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:28:00.14611+00:00
-- url     : https://prove2.me/submissions/c09b3a12-676b-42ff-ba94-50223f5b2b16

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/ScaleBounds.lean:L124-L138
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.tail_lt_four_mul_p. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_TalagrandExpectationThreshold
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Model
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Basic
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMasses
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityFinite
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityProduct
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingExpectation
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityColors
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ScaleBounds

-- ---- from OAI.Combinatorics.ExpectationThreshold.ScaleBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# The largest admissible scale

The cutoff is constructed as the first index whose next scale fails.
Its existence follows from the Archimedean property and the elementary
lower bound `scaleSum s ≥ s`. No finite search bound or computed large
power is used.
-/

namespace TalagrandThreshold

open scoped BigOperators

theorem scaleSum_succ (s : ℕ) :
    scaleSum (s + 1) = scaleSum s + (256 : ℝ) ^ (s + 1) := by
  simp only [scaleSum, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

/-- The finite geometric sum is at most twice its largest power. -/
theorem scaleSum_le_two_pow (s : ℕ) : scaleSum s ≤ 2 * (256 : ℝ) ^ s := by
  induction s with
  | zero => simp [scaleSum_zero]
  | succ s ih =>
      rw [scaleSum_succ, pow_succ (256 : ℝ) s]
      have hpow : 0 ≤ (256 : ℝ) ^ s := by positivity
      nlinarith

/-- Failure at the next scale controls the residual color contribution. -/
theorem tail_lt_four_mul_p {p : ℝ} {s : ℕ} (hp : 0 < p)
    (hnext : 1 / 2 < p * scaleSum (s + 1)) :
    1 / (512 : ℝ) ^ (s + 1) < 4 * p := by
  have hsum : p * scaleSum (s + 1) ≤ p * (2 * (256 : ℝ) ^ (s + 1)) :=
    mul_le_mul_of_nonneg_left (scaleSum_le_two_pow (s + 1)) hp.le
  have hDpos : 0 < (256 : ℝ) ^ (s + 1) := by positivity
  have hDB : (256 : ℝ) ^ (s + 1) ≤ (512 : ℝ) ^ (s + 1) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  calc
    1 / (512 : ℝ) ^ (s + 1) ≤ 1 / (256 : ℝ) ^ (s + 1) :=
      one_div_le_one_div_of_le hDpos hDB
    _ < 4 * p := by
      apply (div_lt_iff₀ hDpos).mpr
      nlinarith

end TalagrandThreshold

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.tail_lt_four_mul_p := @_root_.OAI.TalagrandThreshold.tail_lt_four_mul_p
