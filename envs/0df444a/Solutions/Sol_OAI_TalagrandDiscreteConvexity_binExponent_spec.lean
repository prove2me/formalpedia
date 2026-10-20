-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.binExponent_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:20:54.465984+00:00
-- url     : https://prove2.me/submissions/c9f99b68-57e8-4c8d-840d-b67dd0dfad26

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/DyadicBins.lean:L29-L46
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.binExponent_spec. The node keeps its source
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

-- ---- from OAI.Combinatorics.DiscreteConvexity.DyadicBins ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

/-!
# Dyadic bins for positive weights

The exponent of a weight is determined by the first power of `1 / 2`
strictly below it.  In particular, a weight equal to a dyadic endpoint
belongs to the bin whose upper endpoint it equals.
-/

namespace TalagrandDiscreteConvexity

/-- Every positive weight at most one lies in its specified dyadic bin. -/
theorem binExponent_spec {w : ℝ} (hwpos : 0 < w) (hwle : w ≤ 1) :
    (1 / 2 : ℝ) ^ (binExponent w + 1) < w ∧
      w ≤ (1 / 2 : ℝ) ^ binExponent w := by
  classical
  let ex : ∃ h : ℕ, (1 / 2 : ℝ) ^ h < w :=
    exists_pow_lt_of_lt_one hwpos (by norm_num : (1 / 2 : ℝ) < 1)
  have hcross : (1 / 2 : ℝ) ^ Nat.find ex < w := Nat.find_spec ex
  have hne : Nat.find ex ≠ 0 := by
    intro hz
    have : (1 : ℝ) < w := by simpa only [hz, pow_zero] using hcross
    exact (not_lt_of_ge hwle) this
  have hexp : binExponent w = Nat.find ex - 1 := by
    simp only [binExponent, dite_eq_left hwpos]
  rw [hexp]
  constructor
  · simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hne)] using hcross
  · exact le_of_not_gt (Nat.find_min ex (Nat.sub_one_lt hne))

end TalagrandDiscreteConvexity

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.binExponent_spec := @_root_.OAI.TalagrandDiscreteConvexity.binExponent_spec
