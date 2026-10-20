-- Prove2me | solution 2 for OAI.MetricEntropyDuality.GreedyPivots.mem_covered_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:09:45.548984+00:00
-- url     : https://prove2.me/submissions/edfb6fe4-55a2-423a-b38b-7abc97f56748

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/GreedyPivots.lean:L141-L156
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.GreedyPivots.mem_covered_iff. The node keeps its source
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
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricIndex
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricForms
import Definitions.Def_OAI_Analysis_MetricEntropy_Basic
import Definitions.Def_OAI_Analysis_MetricEntropy_EntropyPair
import Definitions.Def_OAI_Analysis_MetricEntropy_SupportPolar
import Definitions.Def_OAI_Analysis_MetricEntropy_PolarCover
import Definitions.Def_OAI_Analysis_MetricEntropy_CoordinateTransport
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionTuples
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteProductCounting
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionSampling
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricMultiplicity
import Definitions.Def_OAI_Analysis_MetricEntropy_FormPolynomials
import Definitions.Def_OAI_Analysis_MetricEntropy_PolynomialZeroBound
import Definitions.Def_OAI_Analysis_MetricEntropy_FormContraction
import Definitions.Def_OAI_Analysis_MetricEntropy_PartitionGraph
import Definitions.Def_OAI_Analysis_MetricEntropy_FieldGraphSeparation
import Definitions.Def_OAI_Analysis_MetricEntropy_LogProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_GraphProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteFieldRows
import Definitions.Def_OAI_Analysis_MetricEntropy_GreedyPivots

-- ---- from OAI.Analysis.MetricEntropy.GreedyPivots ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uX uY

/-!
# A bounded greedy family of pivots

At each step, choose a set whose mass outside the current union exceeds the
threshold if such a set exists. Otherwise choose a fixed padding center.
Padding still enlarges the union, so it cannot increase any residual mass.
If the residual bound failed after `s` steps, all preceding steps would have
made a strict gain greater than the threshold, contradicting total mass at
most one and `1 ≤ s * θ`.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators

namespace GreedyPivots

variable {X : Type uX} {Y : Type uY}

variable [Nonempty X] [DecidableEq Y]

theorem covered_succ (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) (n : ℕ) :
    covered μ I θ (n + 1) =
      covered μ I θ n ∪ I (choosePivot μ I θ (covered μ I θ n)) := rfl

/-- The recursive union consists exactly of the sets of its selected slots. -/
theorem mem_covered_iff (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) (n : ℕ) (y : Y) :
    y ∈ covered μ I θ n ↔
      ∃ k < n, y ∈ I (choosePivot μ I θ (covered μ I θ k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [covered_succ, Finset.mem_union, ih]
      constructor
      · rintro (⟨k, hk, hy⟩ | hy)
        · exact ⟨k, Nat.lt_succ_of_lt hk, hy⟩
        · exact ⟨n, Nat.lt_succ_self n, hy⟩
      · rintro ⟨k, hk, hy⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
        · exact Or.inl ⟨k, hlt, hy⟩
        · exact Or.inr hy

end GreedyPivots

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.GreedyPivots
open scoped BigOperators


theorem solution.{uX,uY} : type_of% @_root_.OAI.MetricEntropyDuality.GreedyPivots.mem_covered_iff.{uX,uY} := @_root_.OAI.MetricEntropyDuality.GreedyPivots.mem_covered_iff.{uX,uY}
