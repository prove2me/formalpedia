-- Prove2me | solution 2 for OAI.MetricEntropyDuality.totalDegree_tuplePolynomial_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:54:40.525979+00:00
-- url     : https://prove2.me/submissions/05c10d78-cbb7-4994-b1ea-a8db06589bd9

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/FormPolynomials.lean:L89-L104
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.totalDegree_tuplePolynomial_le. The node keeps its source
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

-- ---- from OAI.Analysis.MetricEntropy.FormPolynomials ----
namespace OAI

universe uK

/-!
# Actual polynomials of symmetric forms

The definitions sum over ordered basis tuples, exactly as the multilinear
form evaluation does. The diagonal coefficient of a basis multiset is its
ordered-tuple fiber cardinality times the value of the form. This coefficient
is nonzero in characteristic greater than the degree. Renaming every vector
block to the same coordinate proves nonvanishing for every index tuple,
including tuples with repeated indices.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators
open MvPolynomial

theorem totalDegree_tuplePolynomial_le {K : Type uK} [CommSemiring K] [Nontrivial K]
    {r h u : ℕ} (F : SymmetricForm K r h) (a : Fin h → Fin u) :
    (tuplePolynomial F a).totalDegree ≤ h := by
  unfold tuplePolynomial
  apply totalDegree_finsetSum_le
  intro b _
  calc
    (C (F (tupleSym b)) * ∏ j : Fin h, X (a j, b j)).totalDegree ≤
        (C (F (tupleSym b)) : MvPolynomial (Fin u × Fin r) K).totalDegree +
          (∏ j : Fin h, (X (a j, b j) : MvPolynomial (Fin u × Fin r) K)).totalDegree :=
      totalDegree_mul _ _
    _ = (∏ j : Fin h, (X (a j, b j) : MvPolynomial (Fin u × Fin r) K)).totalDegree := by
      simp
    _ ≤ ∑ j : Fin h, (X (a j, b j) : MvPolynomial (Fin u × Fin r) K).totalDegree :=
      totalDegree_finsetProd _ _
    _ = h := by simp

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality
open scoped BigOperators
open MvPolynomial


theorem solution.{uK} : type_of% @_root_.OAI.MetricEntropyDuality.totalDegree_tuplePolynomial_le.{uK} := @_root_.OAI.MetricEntropyDuality.totalDegree_tuplePolynomial_le.{uK}
