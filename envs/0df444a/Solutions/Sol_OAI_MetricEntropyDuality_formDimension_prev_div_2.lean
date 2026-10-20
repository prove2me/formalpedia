-- Prove2me | solution 2 for OAI.MetricEntropyDuality.formDimension_prev_div
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:36:55.691012+00:00
-- url     : https://prove2.me/submissions/748b6b0d-5230-4c43-b3c1-f8bc234bb50c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/DimensionRatio.lean:L31-L47
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.formDimension_prev_div. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Definitions.Def_MetricEntropyDuality
import Definitions.Def_OAI_Analysis_MetricEntropy_FormDimension
import Definitions.Def_OAI_Analysis_MetricEntropy_Parameters

-- ---- from OAI.Analysis.MetricEntropy.FormDimension ----
namespace OAI

universe uK

/-!
# Dimension of symmetric-form coefficients

The coefficients of a symmetric `j`-linear form on an `r`-dimensional space
are indexed by multisets of `j` basis vectors. Their number gives the
dimension of the coefficient space and hence its cardinality over a finite field.
-/

namespace MetricEntropyDuality

/-- Positive ambient dimension gives a nonempty coefficient index set. -/
theorem formDimension_pos {r j : ℕ} (hr : 0 < r) : 0 < formDimension r j := by
  exact Nat.choose_pos (Nat.le_sub_one_of_lt (Nat.lt_add_of_pos_left hr))

end MetricEntropyDuality

end OAI

-- ---- from OAI.Analysis.MetricEntropy.DimensionRatio ----
namespace OAI

/-!
# Exact dimension ratio and rank lower bound

These are identities for the canonical symmetric-form coefficient count.
The ratio is used in the entropy estimate; the lower bound ensures that
the constructed ambient dimensions diverge as the rank increases.
-/

namespace MetricEntropyDuality

/-- The multiplicative recurrence avoids any natural-number division. -/
theorem formDimension_mul_degree {r h : ℕ} (hr : 0 < r) (hh : 0 < h) :
    formDimension r h * h = formDimension r (h - 1) * (r + h - 1) := by
  cases h with
  | zero => omega
  | succ k =>
      have hk : r + k - 1 + 1 = r + k := by omega
      have hrec := Nat.add_one_mul_choose_eq (r + k - 1) k
      rw [hk] at hrec
      simpa only [formDimension, Nat.add_succ, Nat.succ_sub_one, Nat.mul_comm] using
        hrec.symm

/-- The exact ratio of the previous-degree and current-degree dimensions. -/
theorem formDimension_prev_div {r h : ℕ} (hr : 0 < r) (hh : 0 < h) :
    (formDimension r (h - 1) : ℝ) / (formDimension r h : ℝ) =
      (h : ℝ) / ((r : ℝ) + h - 1) := by
  have hD : 0 < (formDimension r h : ℝ) :=
    Nat.cast_pos.mpr (formDimension_pos hr)
  have hrR : 0 < (r : ℝ) := Nat.cast_pos.mpr hr
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast Nat.succ_le_of_lt hh
  have hden : 0 < (r : ℝ) + h - 1 := by linarith
  have hcast : ((r + h - 1 : ℕ) : ℝ) = (r : ℝ) + h - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r + h), Nat.cast_add, Nat.cast_one]
  have hrec : ((formDimension r h * h : ℕ) : ℝ) =
      ((formDimension r (h - 1) * (r + h - 1) : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) (formDimension_mul_degree hr hh)
  rw [Nat.cast_mul, Nat.cast_mul, hcast] at hrec
  apply (div_eq_div_iff hD.ne' hden.ne').mpr
  exact hrec.symm.trans (mul_comm _ _)

end MetricEntropyDuality

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality


theorem solution : type_of% @_root_.OAI.MetricEntropyDuality.formDimension_prev_div := @_root_.OAI.MetricEntropyDuality.formDimension_prev_div
