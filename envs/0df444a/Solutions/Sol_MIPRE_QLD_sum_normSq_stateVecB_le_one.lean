-- Prove2me | solution 1 for MIPRE.QLD.sum_normSq_stateVecB_le_one
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:37:28.308138+00:00
-- url     : https://prove2.me/submissions/f96a479e-8143-457f-8b4a-279cca924e44

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/Positivity.lean
-/
/-
# Operator-order toolbox

Generic order-theoretic facts about the C⋆-algebra `H →L[ℂ] H` of bounded
operators on a complex Hilbert space, used throughout the formalization of
M. de la Salle, *Orthogonalization of Positive Operator Valued Measures*
(arXiv:2103.14126v2).

Nothing in this file refers to POVMs, von Neumann algebras or the paper's
statements: it collects the elementary Loewner-order manipulations that the
assembly step (`PLAN.md` §1, step **F3**) and the reduction steps use over and
over:

* products of commuting positive operators (`mul_nonneg_of_commute`);
* the two operator inequalities the paper uses for `0 ≤ y ≤ 1`, namely
  `y² ≤ y` (`sq_le_self_of_le_one`) and `(1 - y)² ≤ 1 - y²`
  (`one_sub_sq_le_one_sub_sq'`);
* compressions by a projection commuting with a positive operator
  (`IsStarProjection.mul_le_of_commute`, `IsStarProjection.mul_nonneg_of_commute`);
* the continuous-functional-calculus square root: positivity, the bound
  `√y ≤ 1` for `y ≤ 1`, and the fact that it inherits every commutant
  (`Commute.sqrt`);
* positive linear functionals `φ` on `H →L[ℂ] H`, i.e. `ℂ`-linear maps with
  `0 ≤ φ (x* x)` for the `ComplexOrder` order on `ℂ`: they are monotone
  (`re_le_re_of_le`), real on positives (`im_eq_zero_of_nonneg`), and
  positive on positives (`nonneg_of_nonneg`).

The order on `H →L[ℂ] H` is the Loewner order
(`ContinuousLinearMap.le_def : f ≤ g ↔ (g - f).IsPositive`), for which Mathlib
provides a `StarOrderedRing` structure and the continuous functional calculus.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Consistency.lean (solution of MIPRE.QLD.sum_normSq_stateVecB_le_one);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Center
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.Algebra.Ring.Subsemiring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Star
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.SetLike.Basic
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Pairwise
import Mathlib.Order.Basic
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Positivity
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_PhiNorm
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_IsometryData
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Assembly
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_JointDiag
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_Blocks
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_Main
import Definitions.Def_MIPRE_Background_QLD_Ortho
import Definitions.Def_MIPRE_Background_QLD_Consistency
import Theorems.Thm_MIPRE_POVM_sum_val
import Theorems.Thm_MIPRE_norm_stateVecB
import Theorems.Thm_MIPRE_quadForm_eq
import Theorems.Thm_MIPRE_swapVec_dotProduct

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem stateSqNorm_nonneg (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) : 0 ≤ stateSqNorm ψ M :=
  sq_nonneg _
end
end MIPRE

namespace Orthogonalization
section
open scoped ComplexOrder
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {x y : H →L[ℂ] H}
/-- The product of two **commuting** positive operators is positive.
(Without the commutation hypothesis this is false.) This is Mathlib's
`Commute.mul_nonneg`, restated with the hypotheses in the order in which the
proof uses them. -/
theorem mul_nonneg_of_commute (hx : 0 ≤ x) (hy : 0 ≤ y) (h : Commute x y) : 0 ≤ x * y :=
  h.mul_nonneg hx hy
end
end Orthogonalization

namespace Orthogonalization
section
open scoped ComplexOrder
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {x y : H →L[ℂ] H}
/-- If `0 ≤ x ≤ 1` then `x² ≤ x`: indeed `x - x² = x (1 - x)` is a product of
commuting positive operators. -/
theorem sq_le_self_of_le_one (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x * x ≤ x := by
  have hc : Commute x (1 - x) := (Commute.one_right x).sub_right (Commute.refl x)
  have h : 0 ≤ x * (1 - x) := mul_nonneg_of_commute hx0 (sub_nonneg.mpr hx1) hc
  have he : x * (1 - x) = x - x * x := by noncomm_ring
  rw [he] at h
  exact sub_nonneg.mp h
end
end Orthogonalization

namespace Orthogonalization
section
open scoped ComplexOrder
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
/-- The real part of a positive functional is monotone for the Loewner order. -/
theorem re_le_re_of_le (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) {x y : H →L[ℂ] H}
    (hxy : x ≤ y) : (φ x).re ≤ (φ y).re := by
  have h := nonneg_of_nonneg hφ (sub_nonneg.mpr hxy)
  rw [map_sub] at h
  have := (Complex.nonneg_iff.mp h).1
  simpa using this
end
end Orthogonalization

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem ofCLM_mul (x y : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    ofCLM (x * y) = ofCLM x * ofCLM y := map_mul _ _ _
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem ofCLM_one : ofCLM (1 : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) = 1 := map_one _
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem ofCLM_star (x : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    ofCLM (star x) = (ofCLM x)ᴴ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm.map_star' x
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem toCLM_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix dA dA ℂ) :
    toCLM (∑ i ∈ s, f i) = ∑ i ∈ s, toCLM (f i) := map_sum _ _ _
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem toCLM_one : toCLM (1 : Matrix dA dA ℂ) = 1 := map_one _
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- A positive semidefinite matrix is a positive operator: `toEuclideanCLM` is a star-algebra
equivalence of C*-algebras, so it preserves the order. -/
theorem toCLM_nonneg {M : Matrix dA dA ℂ} (hM : (0 : Matrix dA dA ℂ) ≤ M) :
    0 ≤ toCLM M :=
  map_nonneg _ hM
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- The reduced state is normalized exactly when `ψ` is a unit vector. -/
theorem redState_one {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    redState ψ 1 = 1 := by
  rw [redState_apply, ofCLM_one, Matrix.one_kronecker_one, Matrix.one_mulVec, hψ]
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **The reduced state on a square is the state-dependent squared norm.** -/
theorem redState_star_mul_self (ψ : dA × dB → ℂ)
    (x : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    redState ψ (star x * x) = (stateSqNorm ψ (ofCLM x) : ℂ) := by
  rw [redState_apply, ofCLM_mul, ofCLM_star, quadForm_eq]
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- Hence the reduced state is positive. -/
theorem redState_nonneg (ψ : dA × dB → ℂ)
    (x : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    0 ≤ redState ψ (star x * x) := by
  rw [redState_star_mul_self]
  exact Complex.zero_le_real.mpr (stateSqNorm_nonneg ψ _)
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **The reduced state on the square of a self-adjoint operator**, which is the form the
vendored theorem's near-projectivity hypothesis takes. -/
theorem redState_mul_self (ψ : dA × dB → ℂ) {M : Matrix dA dA ℂ} (hM : Mᴴ = M) :
    redState ψ (toCLM M * toCLM M) = (stateSqNorm ψ M : ℂ) := by
  have hMM : M * M = Mᴴ * M := by rw [hM]
  rw [redState_apply, ofCLM_mul, ofCLM_toCLM, hMM]
  exact quadForm_eq ψ M
end
end MIPRE.QLD

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [DecidableEq A] in
theorem _root_.solution {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (R : POVM A dB) :
    ∑ a, ‖stateVecB ψ (((R.mats a).val))‖ ^ 2 ≤ 1 := by
  classical
  set φ := redState (swapVec ψ) with hφ
  have hφ1 : φ 1 = 1 := redState_one (by rw [swapVec_dotProduct]; exact hψ)
  have ha0 : ∀ a, 0 ≤ toCLM ((R.mats a).val) := fun a =>
    toCLM_nonneg (Subtype.coe_le_coe.mpr (R.nonneg a))
  have ha1 : ∑ a, toCLM ((R.mats a).val) = 1 := by
    rw [← toCLM_sum, POVM.sum_val, toCLM_one]
  have hle : ∑ a, toCLM ((R.mats a).val) * toCLM ((R.mats a).val) ≤ 1 := by
    refine le_trans (Finset.sum_le_sum fun a _ => ?_) (le_of_eq ha1)
    refine Orthogonalization.sq_le_self_of_le_one (ha0 a) ?_
    rw [← ha1]
    exact Finset.single_le_sum (fun j _ => ha0 j) (Finset.mem_univ a)
  have hterm : ∀ a, ‖stateVecB ψ (((R.mats a).val))‖ ^ 2
      = (φ (toCLM ((R.mats a).val) * toCLM ((R.mats a).val))).re := by
    intro a
    rw [norm_stateVecB, hφ,
      redState_mul_self (swapVec ψ) ((R.mats a).2 : ((R.mats a).val)ᴴ = ((R.mats a).val)),
      Complex.ofReal_re]
    rfl
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hterm a,
    ← Complex.re_sum, ← map_sum]
  refine le_trans (Orthogonalization.re_le_re_of_le (redState_nonneg (swapVec ψ)) hle) ?_
  rw [hφ1, Complex.one_re]
end MIPRE.QLD
