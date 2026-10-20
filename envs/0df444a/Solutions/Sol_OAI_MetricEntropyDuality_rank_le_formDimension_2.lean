-- Prove2me | solution 2 for OAI.MetricEntropyDuality.rank_le_formDimension
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:37:38.723403+00:00
-- url     : https://prove2.me/submissions/cbd4df62-ceaa-4eeb-93be-b399f74bbbd2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/DimensionRatio.lean:L49-L64
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.rank_le_formDimension. The node keeps its source
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

-- ---- from OAI.Analysis.MetricEntropy.DimensionRatio ----
namespace OAI

/-!
# Exact dimension ratio and rank lower bound

These are identities for the canonical symmetric-form coefficient count.
The ratio is used in the entropy estimate; the lower bound ensures that
the constructed ambient dimensions diverge as the rank increases.
-/

namespace MetricEntropyDuality

/-- Every positive degree has at least as many coefficients as the rank. -/
theorem rank_le_formDimension {r h : ℕ} (hr : 0 < r) (hh : 0 < h) :
    r ≤ formDimension r h := by
  have hpred : r - 1 + 1 = r := Nat.sub_add_cancel hr
  have hchoose : r.choose (r - 1) = r := by
    simpa only [hpred] using Nat.choose_succ_self_right (r - 1)
  have htop : r ≤ r + h - 1 := by omega
  have hdegree : h ≤ r + h - 1 := by omega
  have hsub : r + h - 1 - h = r - 1 := by omega
  calc
    r = r.choose (r - 1) := hchoose.symm
    _ ≤ (r + h - 1).choose (r - 1) := Nat.choose_le_choose _ htop
    _ = formDimension r h := by
      unfold formDimension
      rw [← hsub]
      exact Nat.choose_symm hdegree

end MetricEntropyDuality

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality


theorem solution : type_of% @_root_.OAI.MetricEntropyDuality.rank_le_formDimension := @_root_.OAI.MetricEntropyDuality.rank_le_formDimension
