-- Prove2me | solution 1 for MIPRE.QLD.sum_snorm_sq_ordComb_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:34:29.507989+00:00
-- url     : https://prove2.me/submissions/1f58565d-803a-4047-927f-ab96589bf4fb

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Products.lean (solution of MIPRE.QLD.sum_snorm_sq_ordComb_le);
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
import Mathlib.Algebra.Module.Basic
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
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
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
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
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
import Mathlib.Algebra.Star.Module
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
import Mathlib.Analysis.CStarAlgebra.Matrix
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
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
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
import Mathlib.Data.Fin.Tuple.Basic
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
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Star
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
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
import Mathlib.Order.Fin.Basic
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
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring
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
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_POVMMix_B
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Definitions.Def_MIPRE_Background_LIDT_Coefficients_B
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
import Definitions.Def_MIPRE_Foundations_StrategyDilation
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Value
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Background_QLD_Win
import Definitions.Def_MIPRE_Background_QLD_Anticomm
import Definitions.Def_MIPRE_Background_QLD_WinMS
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Positivity
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_PhiNorm
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_IsometryData
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Assembly
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_JointDiag
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_Blocks
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_Main
import Definitions.Def_MIPRE_Background_QLD_Ortho
import Definitions.Def_MIPRE_Background_QLD_Consistency
import Definitions.Def_MIPRE_Background_QLD_Commutation
import Definitions.Def_MIPRE_Background_QLD_Expanded
import Definitions.Def_MIPRE_Background_QLD_Swap
import Definitions.Def_MIPRE_Background_QLD_Combined
import Definitions.Def_MIPRE_Background_QLD_Lines
import Definitions.Def_MIPRE_Foundations_Blocks
import Definitions.Def_MIPRE_Background_QLD_Padded
import Definitions.Def_MIPRE_Background_QLD_Product
import Definitions.Def_MIPRE_Background_QLD_Combine
import Definitions.Def_MIPRE_Background_QLD_Legalize
import Definitions.Def_MIPRE_Background_QLD_PaddedLines
import Definitions.Def_MIPRE_Background_QLD_PaddedStrategy
import Definitions.Def_MIPRE_Background_QLD_Dummy
import Definitions.Def_MIPRE_Background_QLD_Products
import Theorems.Thm_MIPRE_QLD_sum_avg_fibre_sand_sub_ord_le
import Theorems.Thm_MIPRE_QLD_sum_uniform_pad4
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_bornProb_nonneg
import Theorems.Thm_MIPRE_sum_snorm_sq_aOp_mul_bOp_le
import Theorems.Thm_MIPRE_sum_uniform_eq_one

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
/-- The sesquilinear form of two matrices applied to the same vector, moved onto one side:
`⟨A v, B v⟩ = ⟨v, A† B v⟩`. -/
theorem star_mulVec_dotProduct {M : Type*} [Fintype M] (A B : Matrix M N ℂ) (v : N → ℂ) :
    star (A *ᵥ v) ⬝ᵥ (B *ᵥ v) = star v ⬝ᵥ ((Aᴴ * B) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
theorem norm_evec_sq (v : N → ℂ) : ‖evec v‖ ^ 2 = (star v ⬝ᵥ v).re := by
  classical
  rw [evec, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star v i * v i = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
    norm_cast
  rw [h, Complex.ofReal_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
theorem norm_evec_mulVec_sq {M : Type*} [Fintype M] (A : Matrix M N ℂ) (v : N → ℂ) :
    ‖evec (A *ᵥ v)‖ ^ 2 = (star v ⬝ᵥ ((Aᴴ * A) *ᵥ v)).re := by
  rw [norm_evec_sq, star_mulVec_dotProduct]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem snorm_nonneg (M : Matrix N N ℂ) : 0 ≤ snorm v M := norm_nonneg _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem snorm_add_le (M M' : Matrix N N ℂ) : snorm v (M + M') ≤ snorm v M + snorm v M' := by
  rw [snorm, snorm, snorm, Matrix.add_mulVec, evec_add]
  exact norm_add_le _ _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem qform_add (M M' : Matrix N N ℂ) : qform v (M + M') = qform v M + qform v M' := by
  rw [qform, qform, qform, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem qform_sub (M M' : Matrix N N ℂ) : qform v (M - M') = qform v M - qform v M' := by
  rw [qform, qform, qform, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem qform_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix N N ℂ) :
    qform v (∑ i ∈ s, f i) = ∑ i ∈ s, qform v (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [qform]
  | insert i s hi ih => rw [Finset.sum_insert hi, qform_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
/-- **The squared state norm is the quadratic form of `M† M`.** -/
theorem snorm_sq_eq_qform (M : Matrix N N ℂ) : snorm v M ^ 2 = qform v (Mᴴ * M) := by
  rw [snorm, norm_evec_mulVec_sq, qform]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_add (X Y : Matrix HB HB ℂ) :
    bOp (X + Y) = (bOp X : Matrix (HA × HB) _ ℂ) + bOp Y := Matrix.kronecker_add _ _ _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_smul (c : ℂ) (X : Matrix HB HB ℂ) :
    bOp (c • X) = c • (bOp X : Matrix (HA × HB) _ ℂ) := Matrix.kronecker_smul _ _ _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_sub (X Y : Matrix HB HB ℂ) :
    bOp (X - Y) = (bOp X : Matrix (HA × HB) _ ℂ) - bOp Y := by
  have h : X - Y = X + (-1 : ℂ) • Y := by module
  rw [h, bOp_add, bOp_smul]
  module
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem aOp_mul_bOp_eq (U : Matrix dA dA ℂ) (V : Matrix dB dB ℂ) :
    (aOp U : Matrix (dA × dB) _ ℂ) * bOp V = U ⊗ₖ V := by
  rw [aOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bornProb_eq_qform (ψ : dA × dB → ℂ) (U : Matrix dA dA ℂ) (V : Matrix dB dB ℂ) :
    bornProb ψ U V = qform ψ ((aOp U : Matrix (dA × dB) _ ℂ) * bOp V) := by
  rw [aOp_mul_bOp_eq, bornProb, qform]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem aOp_bOp_mul_aOp_bOp (U U' : Matrix dA dA ℂ) (V V' : Matrix dB dB ℂ) :
    ((aOp U : Matrix (dA × dB) _ ℂ) * bOp V) * ((aOp U' : Matrix (dA × dB) _ ℂ) * bOp V')
      = (aOp (U * U') : Matrix (dA × dB) _ ℂ) * bOp (V * V') := by
  rw [aOp_mul_bOp_eq, aOp_mul_bOp_eq, aOp_mul_bOp_eq, ← Matrix.mul_kronecker_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem aOp_bOp_conjTranspose (U : Matrix dA dA ℂ) (V : Matrix dB dB ℂ) :
    ((aOp U : Matrix (dA × dB) _ ℂ) * bOp V)ᴴ
      = (aOp (Uᴴ) : Matrix (dA × dB) _ ℂ) * bOp (Vᴴ) := by
  rw [aOp_mul_bOp_eq, aOp_mul_bOp_eq, Matrix.conjTranspose_kronecker]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bornProb_sub_right (ψ : dA × dB → ℂ) (X : Matrix dA dA ℂ) (M N : Matrix dB dB ℂ) :
    bornProb ψ X (M - N) = bornProb ψ X M - bornProb ψ X N := by
  rw [bornProb_eq_qform, bornProb_eq_qform, bornProb_eq_qform, bOp_sub, Matrix.mul_sub, qform_sub]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bornProb_sum_left {ι : Type*} (ψ : dA × dB → ℂ) (s : Finset ι)
    (A : ι → Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    bornProb ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, bornProb ψ (A i) B := by
  rw [bornProb_eq_qform, aOp_sum, Finset.sum_mul, qform_sum]
  exact Finset.sum_congr rfl fun i _ => (bornProb_eq_qform ψ (A i) B).symm
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {X Y A B C : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq C] {ψ : dA × dB → ℂ} {x : X} {y : Y}
theorem bornProb_one_one {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    bornProb ψ (1 : Matrix dA dA ℂ) (1 : Matrix dB dB ℂ) = 1 := by
  rw [bornProb, Matrix.one_kronecker_one, Matrix.one_mulVec, hψ, Complex.one_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- The Born probability is monotone in Bob's operator when Alice's is positive. -/
theorem bornProb_mono_right (ψ : dA × dB → ℂ) {X : Matrix dA dA ℂ} (hX : X.PosSemidef)
    {Y Y' : Matrix dB dB ℂ} (h : Y ≤ Y') : bornProb ψ X Y ≤ bornProb ψ X Y' := by
  have h0 := bornProb_nonneg ψ hX (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h))
  rw [bornProb_sub_right] at h0
  linarith
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- The elements of a projective measurement are positive. -/
theorem ProjectiveMeasurement.posSemidef_M {X A : Type*} [Fintype A]
    (G : ProjectiveMeasurement X A (Matrix dA dA ℂ)) (x : X) (a : A) : (G.M x a).PosSemidef := by
  have : G.M x a = (G.M x a)ᴴ * G.M x a := by
    rw [← Matrix.star_eq_conjTranspose, G.selfAdjoint, G.projective]
  rw [this]
  exact Matrix.posSemidef_conjTranspose_mul_self _
end
end MIPRE

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MvPolynomial
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ} {RA RB : Type*} [Fintype RA]
  [DecidableEq RA] [Fintype RB] [DecidableEq RB]
/-- The total weight of a projective measurement's outcomes is one. -/
theorem sum_bornProb_M_one {Φ : RA × RB → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1) {A : Type*} [Fintype A]
    (G : ProjectiveMeasurement Unit A (Matrix RA RA ℂ)) :
    ∑ g, bornProb Φ (G.M () g) (1 : Matrix RB RB ℂ) = 1 := by
  rw [← bornProb_sum_left, G.normalized, bornProb_one_one hΦ]
end
end MIPRE.QLD

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N] [DecidableEq N]
/-- `Q² ≤ Q` for `0 ≤ Q ≤ 1`. -/
theorem mul_self_le_self_of_le_one {Q : Matrix N N ℂ} (h0 : (0 : Matrix N N ℂ) ≤ Q)
    (h1 : Q ≤ 1) : Q * Q ≤ Q := by
  have hc : Commute Q (1 - Q) := by
    show Q * (1 - Q) = (1 - Q) * Q
    noncomm_ring
  have h := hc.mul_nonneg h0 (sub_nonneg.mpr h1)
  have heq : Q * (1 - Q) = Q - Q * Q := by noncomm_ring
  rw [heq] at h
  exact sub_nonneg.mp h
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N] [DecidableEq N]
omit [DecidableEq N] in
theorem snorm_sq_add_le (v : N → ℂ) (M M' : Matrix N N ℂ) :
    snorm v (M + M') ^ 2 ≤ 2 * snorm v M ^ 2 + 2 * snorm v M' ^ 2 := by
  have h := snorm_add_le v M M'
  have h0 := snorm_nonneg v (M + M')
  nlinarith [sq_nonneg (snorm v M - snorm v M')]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- The squared norm of `(S ⊗ D) ψ` for a projector `S`, as a Born probability. -/
theorem snorm_sq_aOp_mul_bOp (ψ : dA × dB → ℂ) {S : Matrix dA dA ℂ} (hsa : Sᴴ = S)
    (hidem : S * S = S) (D : Matrix dB dB ℂ) :
    snorm ψ ((aOp S : Matrix (dA × dB) _ ℂ) * bOp D) ^ 2 = bornProb ψ S (Dᴴ * D) := by
  rw [snorm_sq_eq_qform, aOp_bOp_conjTranspose, aOp_bOp_mul_aOp_bOp, hsa, hidem,
    ← bornProb_eq_qform]
end
end MIPRE

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {RA RB : Type*} [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]
omit [Algebra (ZMod 2) F] [NeZero m] in
theorem ptComb_posSemidef {Q : F × F → Matrix RB RB ℂ} (hQ : ∀ p, (Q p).PosSemidef)
    (a b c : F) : (ptComb Q a b c).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp
    (Finset.sum_nonneg fun p _ => Matrix.nonneg_iff_posSemidef.mpr (hQ p))
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {RA RB : Type*} [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]
omit [Algebra (ZMod 2) F] [NeZero m] in
theorem ptComb_le_one {Q : F × F → Matrix RB RB ℂ} (hQ : ∀ p, (Q p).PosSemidef)
    (hsum : ∑ p, Q p = 1) (a b c : F) : ptComb Q a b c ≤ 1 := by
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun p _ _ => Matrix.nonneg_iff_posSemidef.mpr (hQ p)
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {RA RB : Type*} [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]
omit [Algebra (ZMod 2) F] [NeZero m] in
theorem ptComb_conjTranspose {Q : F × F → Matrix RB RB ℂ} (hQ : ∀ p, (Q p)ᴴ = Q p) (a b c : F) :
    (ptComb Q a b c)ᴴ = ptComb Q a b c := by
  rw [ptComb, Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun p _ => hQ p
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {RA RB : Type*} [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]
variable {X Z : Point F m → F → Matrix RB RB ℂ}
omit [Algebra (ZMod 2) F] in
theorem sandComb_posSemidef (hX : ∀ x, IsPVM (X x)) (hZ : ∀ z, IsPVM (Z z))
    (u : Point F (4 * m)) (c : F) : (sandComb X Z u c).PosSemidef :=
  ptComb_posSemidef (fun p => sand_posSemidef (hX _) (hZ _) p) _ _ _
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {RA RB : Type*} [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]
variable {X Z : Point F m → F → Matrix RB RB ℂ}
omit [Algebra (ZMod 2) F] in
theorem sandComb_le_one (hX : ∀ x, IsPVM (X x)) (hZ : ∀ z, IsPVM (Z z)) (u : Point F (4 * m))
    (c : F) : sandComb X Z u c ≤ 1 :=
  ptComb_le_one (fun p => sand_posSemidef (hX _) (hZ _) p) (sum_sand (hX _) (hZ _)) _ _ _
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {RA RB : Type*} [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]
variable {X Z : Point F m → F → Matrix RB RB ℂ}
omit [Algebra (ZMod 2) F] in
theorem sandComb_conjTranspose (hX : ∀ x, IsPVM (X x)) (hZ : ∀ z, IsPVM (Z z))
    (u : Point F (4 * m)) (c : F) : (sandComb X Z u c)ᴴ = sandComb X Z u c :=
  ptComb_conjTranspose (fun p => sand_conjTranspose (hX _) (hZ _) p) _ _ _
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {RA RB : Type*} [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]
variable {X Z : Point F m → F → Matrix RB RB ℂ}
omit [Algebra (ZMod 2) F] in
theorem sandComb_sub_ordComb (ord : (F → Matrix RB RB ℂ) → (F → Matrix RB RB ℂ) → F × F →
    Matrix RB RB ℂ) (u : Point F (4 * m)) (c : F) :
    sandComb X Z u c - ordComb ord X Z u c
      = ptComb (fun p => sand (X (xBlk u)) (Z (zBlk u)) p - ord (X (xBlk u)) (Z (zBlk u)) p)
          (alph u) (bet u) c := by
  simp only [sandComb, ordComb, ptComb, Finset.sum_sub_distrib]
end
end MIPRE.QLD

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {RA RB : Type*} [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]
variable {X Z : Point F m → F → Matrix RB RB ℂ}
theorem _root_.solution {Φ : RA × RB → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix RA RA ℂ))
    (hX : ∀ x, IsPVM (X x)) (hZ : ∀ z, IsPVM (Z z))
    {ord : (F → Matrix RB RB ℂ) → (F → Matrix RB RB ℂ) → F × F → Matrix RB RB ℂ}
    (hord1 : ∀ x z, ∑ p : F × F, ord (X x) (Z z) p = 1)
    (hordle : ∀ x z p, ‖stateVecB Φ (sand (X x) (Z z) p - ord (X x) (Z z) p)‖
      ≤ ‖stateVecB Φ (comm (X x) (Z z) p)‖)
    {δ κ : ℝ}
    (hcons : 1 - δ ≤ ∑ u, uniform (Point F (4 * m)) u
      * ∑ g, bornProb Φ (G.M () g) (sandComb X Z u (g.eval u)))
    (hcomm : ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z)
      * ∑ p : F × F, ‖stateVecB Φ (comm (X x) (Z z) p)‖ ^ 2 ≤ κ) :
    ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
        * bOp (1 - ordComb ord X Z u (g.eval u))) ^ 2
      ≤ 2 * δ + 2 * κ := by
  have hμ0 : ∀ u, 0 ≤ uniform (Point F (4 * m)) u := fun u => inv_nonneg.mpr (Nat.cast_nonneg _)
  have hμ1 : ∑ u, uniform (Point F (4 * m)) u = 1 := sum_uniform_eq_one _
  have hGpvm : IsPVM (G.M ()) :=
    ⟨fun g => G.selfAdjoint () g, fun g => G.projective () g, G.normalized ()⟩
  -- the pointwise split along `1 - B = (1 - P) + (P - B)`
  have hsplit : ∀ u g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
        * bOp (1 - ordComb ord X Z u (g.eval u))) ^ 2
      ≤ 2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
          * bOp (1 - sandComb X Z u (g.eval u))) ^ 2
        + 2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
          * bOp (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2 := by
    intro u g
    have h : (1 : Matrix RB RB ℂ) - ordComb ord X Z u (g.eval u)
        = (1 - sandComb X Z u (g.eval u))
          + (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u)) := by abel
    rw [h, bOp_add, Matrix.mul_add]
    exact snorm_sq_add_le _ _ _
  -- the first term: the consistency itself
  have hfirst : ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - sandComb X Z u (g.eval u))) ^ 2 ≤ δ := by
    have hpt : ∀ u g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
          * bOp (1 - sandComb X Z u (g.eval u))) ^ 2
        ≤ bornProb Φ (G.M () g) 1 - bornProb Φ (G.M () g) (sandComb X Z u (g.eval u)) := by
      intro u g
      rw [snorm_sq_aOp_mul_bOp Φ (G.selfAdjoint () g) (G.projective () g), ← bornProb_sub_right]
      have hsa : ((1 : Matrix RB RB ℂ) - sandComb X Z u (g.eval u))ᴴ
          = 1 - sandComb X Z u (g.eval u) := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, sandComb_conjTranspose hX hZ]
      rw [hsa]
      refine bornProb_mono_right Φ (G.posSemidef_M () g) (mul_self_le_self_of_le_one ?_ ?_)
      · exact sub_nonneg.mpr (sandComb_le_one hX hZ u _)
      · exact sub_le_self _ (Matrix.nonneg_iff_posSemidef.mpr (sandComb_posSemidef hX hZ u _))
    calc ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
          ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - sandComb X Z u (g.eval u))) ^ 2
        ≤ ∑ u, uniform (Point F (4 * m)) u * ∑ g, (bornProb Φ (G.M () g) 1
            - bornProb Φ (G.M () g) (sandComb X Z u (g.eval u))) :=
          Finset.sum_le_sum fun u _ =>
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ => hpt u g) (hμ0 u)
      _ = 1 - ∑ u, uniform (Point F (4 * m)) u
            * ∑ g, bornProb Φ (G.M () g) (sandComb X Z u (g.eval u)) := by
          simp only [Finset.sum_sub_distrib, sum_bornProb_M_one hΦ G, mul_sub, mul_one, hμ1]
      _ ≤ δ := by linarith
  -- the second term: the commutators, through Parseval
  have hsecond : ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
        * bOp (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2 ≤ κ := by
    have hu : ∀ u, ∑ g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
          * bOp (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2
        ≤ ∑ c, ‖stateVecB Φ (ptComb (fun p => sand (X (xBlk u)) (Z (zBlk u)) p
            - ord (X (xBlk u)) (Z (zBlk u)) p) (alph u) (bet u) c)‖ ^ 2 := by
      intro u
      have h := sum_snorm_sq_aOp_mul_bOp_le Φ hGpvm (fun g => g.eval u)
        (fun c => sandComb X Z u c - ordComb ord X Z u c)
      simpa only [sandComb_sub_ordComb] using h
    calc ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
          ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2
        ≤ ∑ u, uniform (Point F (4 * m)) u * ∑ c, ‖stateVecB Φ (ptComb
            (fun p => sand (X (xBlk u)) (Z (zBlk u)) p - ord (X (xBlk u)) (Z (zBlk u)) p)
            (alph u) (bet u) c)‖ ^ 2 :=
          Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hu u) (hμ0 u)
      _ = ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z)
            * ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
              * ∑ c, ‖stateVecB Φ (ptComb (fun p => sand (X x) (Z z) p - ord (X x) (Z z) p)
                  ab.1 ab.2 c)‖ ^ 2 :=
          sum_uniform_pad4 fun x z a b => ∑ c, ‖stateVecB Φ (ptComb
            (fun p => sand (X x) (Z z) p - ord (X x) (Z z) p) a b c)‖ ^ 2
      _ ≤ ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z)
            * ∑ p : F × F, ‖stateVecB Φ (comm (X x) (Z z) p)‖ ^ 2 := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ =>
            mul_le_mul_of_nonneg_left ?_
              (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (inv_nonneg.mpr (Nat.cast_nonneg _)))
          exact sum_avg_fibre_sand_sub_ord_le (hX x) (hZ z) Φ (hord1 x z) (hordle x z)
      _ ≤ κ := hcomm
  have hsum : ∑ u, uniform (Point F (4 * m)) u * ∑ g, (2 * snorm Φ
        ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - sandComb X Z u (g.eval u))) ^ 2
        + 2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
          * bOp (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2)
      = 2 * (∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
          ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - sandComb X Z u (g.eval u))) ^ 2)
        + 2 * (∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
          ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2) := by
    simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    congr 1 <;> exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun g _ => by ring
  calc ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
          * bOp (1 - ordComb ord X Z u (g.eval u))) ^ 2
      ≤ ∑ u, uniform (Point F (4 * m)) u * ∑ g, (2 * snorm Φ
          ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - sandComb X Z u (g.eval u))) ^ 2
          + 2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2) :=
        Finset.sum_le_sum fun u _ =>
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ => hsplit u g) (hμ0 u)
    _ = _ := hsum
    _ ≤ 2 * δ + 2 * κ := by linarith [hfirst, hsecond]
end MIPRE.QLD
