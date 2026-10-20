-- Prove2me | solution 2 for OAI.MetricEntropyDuality.log_count_le_encodingCost
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:38:31.013427+00:00
-- url     : https://prove2.me/submissions/d05b1251-f537-4005-9b73-dc8a2dc6ec63

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/EntropyBounds.lean:L24-L46
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.log_count_le_encodingCost. The node keeps its source
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

/-- Taking logarithms of the literal finite encoding count. -/
theorem log_count_le_encodingCost {h u q Q : ℕ} {θ : ℝ}
    (hu : 0 < u) (hq : 0 < q) (hθ : 0 < θ) (hQ : 0 < Q)
    (hcount : (Q : ℝ) ≤ (u : ℝ) * (q : ℝ) ^ (h * pivotSlots θ) *
      (1 + (pivotSlots θ : ℝ) * (2 : ℝ) ^ u / θ) ^
        (h * pivotSlots θ * 2 ^ u)) :
    Real.log (Q : ℝ) ≤ (h : ℝ) * (pivotSlots θ : ℝ) * Real.log (q : ℝ) +
      encodingCost h θ u := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hbase : 0 < 1 + (pivotSlots θ : ℝ) * (2 : ℝ) ^ u / θ := by positivity
  calc
    Real.log (Q : ℝ) ≤ Real.log ((u : ℝ) * (q : ℝ) ^ (h * pivotSlots θ) *
        (1 + (pivotSlots θ : ℝ) * (2 : ℝ) ^ u / θ) ^
          (h * pivotSlots θ * 2 ^ u)) := Real.log_le_log hQ0 hcount
    _ = (h : ℝ) * (pivotSlots θ : ℝ) * Real.log (q : ℝ) +
        encodingCost h θ u := by
      rw [Real.log_mul (by positivity) (pow_ne_zero _ hbase.ne'),
        Real.log_mul hu0.ne' (pow_ne_zero _ hq0.ne'), Real.log_pow, Real.log_pow]
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      unfold encodingCost
      ring

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality


theorem solution : type_of% @_root_.OAI.MetricEntropyDuality.log_count_le_encodingCost := @_root_.OAI.MetricEntropyDuality.log_count_le_encodingCost
