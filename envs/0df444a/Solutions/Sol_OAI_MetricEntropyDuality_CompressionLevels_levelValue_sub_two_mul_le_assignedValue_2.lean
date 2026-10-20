-- Prove2me | solution 2 for OAI.MetricEntropyDuality.CompressionLevels.levelValue_sub_two_mul_le_assignedValue
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:15:08.673561+00:00
-- url     : https://prove2.me/submissions/ec5bfb41-fd87-4e9c-a265-324955074d9f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/CompressionLevels.lean:L123-L151
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.CompressionLevels.levelValue_sub_two_mul_le_assignedValue. The node keeps its source
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
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionLevels
import Theorems.Thm_OAI_MetricEntropyDuality_CompressionLevels_ballIndicator_le_assignedIndicator_add

-- ---- from OAI.Analysis.MetricEntropy.CompressionLevels ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uX uY uK uι uLabel

/-!
# Graph-ball comparison at one compression level

Columns omitted by the common index and retained columns left uncovered
each contribute at most `θ`. Assigned columns are compared using the actual
partition graph and replacement pivots with the same selected label.
Graph distances remain extended distances throughout.
-/

noncomputable section

namespace MetricEntropyDuality.CompressionLevels

open scoped BigOperators Classical

variable {X : Type uX} {Y : Type uY} {K : Type uK} {ι : Type uι} {Label : ι → Type uLabel}

section Weighted

variable [Fintype Y]

/-- The lower comparison loses only omitted mass and uncovered retained mass. -/
theorem levelValue_sub_two_mul_le_assignedValue
    (L : (i : ι) → X → Label i) (v : Y → X) (T : Y → Finset ι)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (i : ι) (j : ℕ)
    (centers rep : K → X) (assignment : Y → Option K)
    (hassign : ∀ y k, assignment y = some k →
      i ∈ T y ∧ PartitionGraph.near L (T y) j (centers k) (v y))
    (hrep : ∀ k, L i (rep k) = L i (centers k)) {θ : ℝ}
    (homit : (∑ y ∈ Finset.univ.filter (fun y => i ∉ T y), μ y) ≤ θ)
    (hrem : ∀ x, (∑ y ∈ Finset.univ.filter (fun y =>
      i ∈ T y ∧ PartitionGraph.near L (T y) j x (v y) ∧
        assignment y = none), μ y) ≤ θ) (x : X) :
    levelValue L v T μ j x - 2 * θ ≤ assignedValue L T rep assignment μ j x := by
  have hsum : levelValue L v T μ j x ≤ assignedValue L T rep assignment μ j x +
      (∑ y ∈ Finset.univ.filter (fun y => i ∉ T y), μ y) +
      (∑ y ∈ Finset.univ.filter (fun y =>
        i ∈ T y ∧ PartitionGraph.near L (T y) j x (v y) ∧
          assignment y = none), μ y) := by
    calc
      _ ≤ ∑ y, μ y * (assignedIndicator L T rep assignment j x y +
          (if i ∉ T y then 1 else 0) +
          (if i ∈ T y ∧ PartitionGraph.near L (T y) j x (v y) ∧
            assignment y = none then 1 else 0)) := by
        exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
          (ballIndicator_le_assignedIndicator_add L v T i j centers rep assignment
            hassign hrep x y) (hμ y)
      _ = _ := by
        simp [assignedValue, mul_add, Finset.sum_add_distrib, Finset.sum_filter, mul_ite]
  linarith [hrem x]

end Weighted

end MetricEntropyDuality.CompressionLevels

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.CompressionLevels
open scoped BigOperators Classical


theorem solution.{uX,uY,uK,uι,uLabel} : type_of% @_root_.OAI.MetricEntropyDuality.CompressionLevels.levelValue_sub_two_mul_le_assignedValue.{uX,uY,uK,uι,uLabel} := @_root_.OAI.MetricEntropyDuality.CompressionLevels.levelValue_sub_two_mul_le_assignedValue.{uX,uY,uK,uι,uLabel}
