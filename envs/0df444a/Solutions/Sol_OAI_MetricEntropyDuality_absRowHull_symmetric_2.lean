-- Prove2me | solution 2 for OAI.MetricEntropyDuality.absRowHull_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:42:13.304367+00:00
-- url     : https://prove2.me/submissions/36b5faa2-87a4-4159-be9e-5721a60485b4

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/ConvexBody.lean:L71-L87
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.absRowHull_symmetric. The node keeps its source
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

-- ---- from OAI.Analysis.MetricEntropy.ConvexBody ----
namespace OAI

universe uι uX uY

/-!
# The concrete symmetric convex bodies

The absolute row hull is the convex hull of the actual finite set of rows and
their negatives. Adding a positive multiple of the coordinate cube gives full
ambient interior, without any spanning hypothesis on the rows.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped Pointwise

section Cube

variable {ι : Type uι} [Fintype ι]

end Cube

section RowHull

variable {X : Type uX} {Y : Type uY} (g : Y → X → ℝ)

theorem convex_absRowHull : Convex ℝ (absRowHull g) :=
  convex_convexHull ℝ _

theorem absRowHull_symmetric (z : RealSpace Y) :
    z ∈ absRowHull g ↔ -z ∈ absRowHull g := by
  have hneg : absRowHull g ⊆ -absRowHull g := by
    apply convexHull_min _ (convex_absRowHull g).neg
    rintro w (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · apply Set.mem_neg.mpr
      exact subset_convexHull ℝ _ (Or.inr ⟨x, rfl⟩)
    · apply Set.mem_neg.mpr
      simpa only [absRowHull, neg_neg] using
        (subset_convexHull ℝ
          (Set.range (row g) ∪ Set.range (fun x => -row g x))
          (Or.inl ⟨x, rfl⟩))
  constructor
  · intro hz
    exact Set.mem_neg.mp (hneg hz)
  · intro hz
    simpa only [neg_neg] using Set.mem_neg.mp (hneg hz)

end RowHull

section MatrixBody

variable {X : Type uX} {Y : Type uY} [Fintype Y] (g : Y → X → ℝ) (t : ℝ)

end MatrixBody

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality
open scoped Pointwise


theorem solution.{uX,uY} : type_of% @_root_.OAI.MetricEntropyDuality.absRowHull_symmetric.{uX,uY} := @_root_.OAI.MetricEntropyDuality.absRowHull_symmetric.{uX,uY}
