-- Prove2me | solution 2 for OAI.MetricEntropyDuality.entropy_ratio_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:40:04.294814+00:00
-- url     : https://prove2.me/submissions/ad0b5e01-7538-4001-887a-8dc3052f4db9

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/EntropyComparison.lean:L74-L92
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.entropy_ratio_bounds. The node keeps its source
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

-- ---- from OAI.Analysis.MetricEntropy.EntropyComparison ----
namespace OAI

/-!
# Real scalar entropy comparisons

The encoding term is controlled by choosing the field size after all other
parameters. The final lemmas transfer bounds for the finite approximation list
to bounds for covering numbers. Their hypotheses are scalar inequalities, so
natural cardinalities can be inserted by casting.
-/

namespace MetricEntropyDuality

/-- The entropy ratio is nonnegative when both covering counts have the usual
positive lower bounds. -/
theorem entropy_ratio_nonneg {N dual : ℝ} (hN : 1 < N) (hdual : 1 ≤ dual) :
    0 ≤ Real.log dual / Real.log N :=
  div_nonneg (Real.log_nonneg hdual) (Real.log_pos hN).le

/-- Increasing the denominator and decreasing the nonnegative numerator
preserves the upper entropy-ratio bound. -/
theorem entropy_ratio_bounds {N m dual Q : ℝ}
    (hm : 1 < m) (hNm : m ≤ N) (hdual : 1 ≤ dual) (hdualQ : dual ≤ Q ^ 2) :
    0 ≤ Real.log dual / Real.log N ∧
      Real.log dual / Real.log N ≤ Real.log (Q ^ 2) / Real.log m := by
  have hN : 1 < N := hm.trans_le hNm
  have hlogm : 0 < Real.log m := Real.log_pos hm
  have hlogNm : Real.log m ≤ Real.log N :=
    Real.log_le_log (by linarith only [hm]) hNm
  have hlogdual : 0 ≤ Real.log dual := Real.log_nonneg hdual
  have hlogdualQ : Real.log dual ≤ Real.log (Q ^ 2) :=
    Real.log_le_log (by linarith only [hdual]) hdualQ
  refine ⟨entropy_ratio_nonneg hN hdual, ?_⟩
  calc
    Real.log dual / Real.log N ≤ Real.log dual / Real.log m :=
      div_le_div_of_nonneg_left hlogdual hlogm hlogNm
    _ ≤ Real.log (Q ^ 2) / Real.log m :=
      div_le_div_of_nonneg_right hlogdualQ hlogm.le

end MetricEntropyDuality

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality


theorem solution : type_of% @_root_.OAI.MetricEntropyDuality.entropy_ratio_bounds := @_root_.OAI.MetricEntropyDuality.entropy_ratio_bounds
