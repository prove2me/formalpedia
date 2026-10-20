-- Prove2me | solution 2 for OAI.MetricEntropyDuality.form_entropy_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:39:09.309755+00:00
-- url     : https://prove2.me/submissions/e4ecb330-4a16-4881-9f1b-55cccf188551

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/EntropyBounds.lean:L75-L94
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.form_entropy_ratio_le. The node keeps its source
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
import Theorems.Thm_OAI_MetricEntropyDuality_formDimension_prev_div

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

-- ---- from OAI.Analysis.MetricEntropy.EntropyBounds ----
namespace OAI

universe uα

/-!
# From finite compression counts to entropy bounds

The counting premise is the literal finite encoding bound. Its logarithmic
conversion and the exact symmetric-form dimension ratio give the scalar
entropy comparison used after the matrix-to-body construction.
-/

noncomputable section

namespace MetricEntropyDuality

/-- The algebraic ratio calculation before substituting symmetric dimensions. -/
theorem log_square_ratio_le_of_log_bound {Q p D E h s C : ℝ}
    (hp : 1 < p) (hD : 0 < D)
    (hQ : Real.log Q ≤ h * s * E * Real.log p + C) :
    Real.log (Q ^ 2) / (D * Real.log p) ≤
      2 * h * s * (E / D) + 2 * C / (D * Real.log p) := by
  have hlogp : 0 < Real.log p := Real.log_pos hp
  have hden : 0 < D * Real.log p := mul_pos hD hlogp
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  calc
    2 * Real.log Q / (D * Real.log p) ≤
        (2 * (h * s * E * Real.log p + C)) / (D * Real.log p) :=
      div_le_div_of_nonneg_right (by linarith) hden.le
    _ = 2 * h * s * (E / D) + 2 * C / (D * Real.log p) := by
      field_simp [hD.ne', hlogp.ne']

/-- The exact binomial ratio converts label entropy into the rank term. -/
theorem form_entropy_ratio_le {r h s p Q : ℕ} {C : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hp : 1 < p)
    (hQ : Real.log (Q : ℝ) ≤ (h : ℝ) * (s : ℝ) *
      Real.log ((p : ℝ) ^ formDimension r (h - 1)) + C) :
    Real.log ((Q : ℝ) ^ 2) / Real.log ((p : ℝ) ^ formDimension r h) ≤
      2 * (h : ℝ) ^ 2 * (s : ℝ) / ((r : ℝ) + h - 1) +
        2 * C / ((formDimension r h : ℝ) * Real.log (p : ℝ)) := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have hD : (0 : ℝ) < formDimension r h := by exact_mod_cast formDimension_pos hr
  have hQ' : Real.log (Q : ℝ) ≤ (h : ℝ) * (s : ℝ) *
      (formDimension r (h - 1) : ℝ) * Real.log (p : ℝ) + C := by
    rw [Real.log_pow] at hQ
    convert hQ using 1; ring
  have hbound := log_square_ratio_le_of_log_bound hp' hD hQ'
  rw [formDimension_prev_div hr hh] at hbound
  have hlogm : Real.log ((p : ℝ) ^ formDimension r h) =
      (formDimension r h : ℝ) * Real.log (p : ℝ) := Real.log_pow _ _
  rw [hlogm]
  convert hbound using 1; ring

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality


theorem solution : type_of% @_root_.OAI.MetricEntropyDuality.form_entropy_ratio_le := @_root_.OAI.MetricEntropyDuality.form_entropy_ratio_le
