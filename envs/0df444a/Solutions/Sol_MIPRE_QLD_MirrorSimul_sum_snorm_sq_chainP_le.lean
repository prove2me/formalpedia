-- Prove2me | solution 1 for MIPRE.QLD.MirrorSimul.sum_snorm_sq_chainP_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:12:29.840983+00:00
-- url     : https://prove2.me/submissions/1f543fd1-641c-431e-bfe6-65605056025c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Chain.lean (solution of MIPRE.QLD.MirrorSimul.sum_snorm_sq_chainP_le);
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
import Definitions.Def_MIPRE_Background_LIDT_BlockPoly
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
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
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
import Definitions.Def_MIPRE_Background_QLD_Linear
import Definitions.Def_MIPRE_Background_QLD_Separate
import Definitions.Def_MIPRE_Background_QLD_Simul
import Definitions.Def_MIPRE_Background_QLD_Complete
import Definitions.Def_MIPRE_Background_QLD_PauliBasis
import Definitions.Def_MIPRE_Background_QLD_Multilinear
import Definitions.Def_MIPRE_Background_QLD_ExactPauli
import Definitions.Def_MIPRE_Background_QLD_SwapUnitary
import Definitions.Def_MIPRE_Background_QLD_MTilde
import Definitions.Def_MIPRE_Background_QLD_Pulling
import Definitions.Def_MIPRE_Background_QLD_SwapMeasure
import Definitions.Def_MIPRE_Background_QLD_ChainProbe
import Definitions.Def_MIPRE_Background_QLD_TwoPairs
import Definitions.Def_MIPRE_Background_QLD_Mirror
import Definitions.Def_MIPRE_Background_QLD_SwapState
import Definitions.Def_MIPRE_Background_QLD_Chain
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_IsPVM_orthogonal
import Theorems.Thm_MIPRE_IsPVM_posSemidef
import Theorems.Thm_MIPRE_QLD_MirrorSimul_bobHat_conj_bobWeyl
import Theorems.Thm_MIPRE_QLD_isPVM_hatMats
import Theorems.Thm_MIPRE_Weyl_epr_unit
import Theorems.Thm_MIPRE_Weyl_proj_mul_proj
import Theorems.Thm_MIPRE_Weyl_sum_proj
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_aOp_sub
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_bornProb_nonneg
import Theorems.Thm_MIPRE_bornProb_reindex
import Theorems.Thm_MIPRE_kronecker_sum_right
import Theorems.Thm_MIPRE_mulVec_kron_kron_expVec
import Theorems.Thm_MIPRE_snorm_sq_sum_proj_mul
import Theorems.Thm_MIPRE_star_sgn
import Theorems.Thm_MIPRE_sum_kron_le_one
import Theorems.Thm_MIPRE_sum_kronecker_left

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
theorem bOp_mul (X Y : Matrix HB HB ℂ) :
    bOp (X * Y) = (bOp X : Matrix (HA × HB) _ ℂ) * bOp Y := by
  rw [bOp, bOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
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
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_conjTranspose (X : Matrix HB HB ℂ) :
    (bOp X : Matrix (HA × HB) _ ℂ)ᴴ = bOp (Xᴴ) := by
  rw [bOp, bOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bOp_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix dB dB ℂ) :
    bOp (∑ i ∈ s, f i) = ∑ i ∈ s, (bOp (f i) : Matrix (dA × dB) _ ℂ) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, bOp, Matrix.kronecker_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, bOp_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']
/-- A product of sums as a sum over the product. -/
theorem sum_prod_mul {X Y M : Type*} [Fintype X] [Fintype Y] [CommRing M] (f : X → M)
    (g : Y → M) : ∑ q : X × Y, f q.1 * g q.2 = (∑ x, f x) * ∑ y, g y := by
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']
theorem expVec_dotProduct_of_pair (u u' : dA × dB → ℂ) (v v' : anc × anc' → ℂ) :
    star (expVec u v) ⬝ᵥ expVec u' v' = (star u ⬝ᵥ u') * (star v ⬝ᵥ v') := by
  classical
  rw [dotProduct, dotProduct, dotProduct, ← sum_prod_mul]
  refine Fintype.sum_equiv (expEquiv dA dB anc anc') _ _ fun p => ?_
  obtain ⟨⟨a, x⟩, ⟨b, y⟩⟩ := p
  simp only [expEquiv, Equiv.coe_fn_mk, Pi.star_apply, expVec, star_mul']
  ring
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']
/-- **The Born probability of a product measurement on the expanded state factorizes.** Only the
ancilla's two operators need to be positive: that is what makes their quadratic form real, which is
what lets the real part of the product split. -/
theorem bornProb_expVec_kron (ψ : dA × dB → ℂ) (e : anc × anc' → ℂ) {X : Matrix dA dA ℂ}
    {Y : Matrix anc anc ℂ} {X' : Matrix dB dB ℂ} {Y' : Matrix anc' anc' ℂ}
    (hY : Y.PosSemidef) (hY' : Y'.PosSemidef) :
    bornProb (expVec ψ e) (X ⊗ₖ Y) (X' ⊗ₖ Y') = bornProb ψ X X' * bornProb e Y Y' := by
  have hre : ∀ (Z : Matrix (anc × anc') (anc × anc') ℂ), Z.PosSemidef →
      (star e ⬝ᵥ (Z *ᵥ e)).im = 0 :=
    fun Z hZ => ((Complex.nonneg_iff.mp (hZ.dotProduct_mulVec_nonneg e)).2).symm
  rw [bornProb, mulVec_kron_kron_expVec, expVec_dotProduct_of_pair, bornProb, bornProb,
    Complex.mul_re, hre _ (hY.kronecker hY'), mul_zero, sub_zero]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']
/-- **A product of projective measurements is projective.** -/
theorem isPVM_kron {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {P : ι → Matrix dA dA ℂ} {Q : κ → Matrix anc anc ℂ} (hP : IsPVM P) (hQ : IsPVM Q) :
    IsPVM (fun p : ι × κ => P p.1 ⊗ₖ Q p.2) where
  isSelfAdjoint p := by
    rw [Matrix.conjTranspose_kronecker, hP.isSelfAdjoint, hQ.isSelfAdjoint]
  idem p := by
    rw [← Matrix.mul_kronecker_mul, hP.idem, hQ.idem]
  sum_eq_one := by
    rw [Fintype.sum_prod_type,
      show (∑ i : ι, ∑ j : κ, P i ⊗ₖ Q j) = ∑ i : ι, P i ⊗ₖ (∑ j : κ, Q j) from
        Finset.sum_congr rfl fun i _ => (kronecker_sum_right _ _ _).symm,
      hQ.sum_eq_one, ← sum_kronecker_left, hP.sum_eq_one, Matrix.one_kronecker_one]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']
/-- **A coarse-graining of a projective POVM is projective**, in the `POVM.map` form the games
use. -/
theorem isPVM_povm_map {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (M : POVM A dA) (h : IsPVM fun a => ((M.mats a).val)) (f : A → B) :
    IsPVM fun b => (((M.map f).mats b).val) := by
  have hval : ∀ b : B, (((M.map f).mats b).val)
      = ∑ a ∈ Finset.univ.filter fun a => f a = b, ((M.mats a).val) := fun b =>
    AddSubmonoidClass.coe_finsetSum _ _
  simpa only [hval] using h.coarse f
end
end MIPRE

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- The defining Fourier average, as a rewrite. -/
theorem proj_def (w : (n → F) → Matrix (n → F) (n → F) ℂ) (e : n → F) :
    proj w e = (Fintype.card (n → F) : ℂ)⁻¹ • ∑ a : n → F, sgn (trDot a e) • w a := rfl
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
/-- The projectors are self-adjoint. -/
theorem proj_conjTranspose (hw : IsWeylFamily w) (e : n → F) : (proj w e)ᴴ = proj w e := by
  classical
  rw [proj_def w e, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
    Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
      rw [Matrix.conjTranspose_smul, hw.selfAdjoint a, star_sgn]]
  congr 1
  simp
end
end MIPRE.Weyl

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
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bornProb_sum_right {ι : Type*} (ψ : dA × dB → ℂ) (s : Finset ι)
    (A : Matrix dA dA ℂ) (B : ι → Matrix dB dB ℂ) :
    bornProb ψ A (∑ i ∈ s, B i) = ∑ i ∈ s, bornProb ψ A (B i) := by
  rw [bornProb_eq_qform, bOp_sum, Finset.mul_sum, qform_sum]
  exact Finset.sum_congr rfl fun i _ => (bornProb_eq_qform ψ A (B i)).symm
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
theorem IsPVM.bOp {ι : Type*} [Fintype ι] {Q : ι → Matrix dB dB ℂ} (h : IsPVM Q) :
    IsPVM fun i => (bOp (Q i) : Matrix (dA × dB) (dA × dB) ℂ) where
  isSelfAdjoint i := by rw [bOp_conjTranspose, h.isSelfAdjoint]
  idem i := by rw [← bOp_mul, h.idem]
  sum_eq_one := by rw [← bOp_sum, h.sum_eq_one, bOp_one]
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

namespace MIPRE.QLD.SimulPair
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
theorem hatMats_conjTranspose {d' : Type} [Fintype d'] [DecidableEq d']
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (u : Point F m) (a : F) :
    (hatMats M W u a)ᴴ = hatMats M W u a := by
  rw [hatMats, ← Matrix.star_eq_conjTranspose]
  exact ((hatPtPOVM M W u).mats a).2
end
end MIPRE.QLD.SimulPair

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl MvPolynomial
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {R : Type*} [Fintype R] [DecidableEq R]
omit [Field F] [Algebra (ZMod 2) F] [NeZero m] in
/-- The polynomial marginal of a projective pair measurement is projective. -/
theorem isPVM_polyMarg {S : POVM (PolyPair F m d) R} (hS : IsPVM fun p => ((S.mats p).val))
    (W : Bas) : IsPVM fun g => (((polyMarg S W).mats g).val) :=
  isPVM_povm_map S hS _
end
end MIPRE.QLD

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
variable {R S T E : Type*} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]
/-- **The quadratic form is carried by any reindexing of the whole space.** The bipartite version
`quadForm_reindex` reindexes the two parties separately and so cannot move a factor between them;
this one makes no reference to a cut. -/
theorem qform_comp_equiv {N N' : Type*} [Fintype N] [Fintype N'] (e : N ≃ N') (ψ : N → ℂ)
    (A : Matrix N N ℂ) :
    star (ψ ∘ e.symm) ⬝ᵥ ((Matrix.reindex e e A) *ᵥ (ψ ∘ e.symm)) = star ψ ⬝ᵥ (A *ᵥ ψ) := by
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  have hcomp : (ψ ∘ e.symm) ∘ e.symm.symm = ψ := by
    rw [Equiv.symm_symm, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
  rw [hcomp]
  show ∑ p, star ψ (e.symm p) * (A *ᵥ ψ) (e.symm p) = ∑ p, star ψ p * (A *ᵥ ψ) p
  exact Equiv.sum_comp e.symm fun p => star ψ p * (A *ᵥ ψ) p
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
variable {R S T E : Type*} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]
omit [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
  [Fintype E] in
/-- The same operator, grouped the two ways. -/
theorem reindex_regroupEquiv (X : Matrix R R ℂ) (M : Matrix S S ℂ) (N : Matrix T T ℂ) :
    Matrix.reindex (regroupEquiv (R := R) (S := S) (T := T) (E := E))
        (regroupEquiv (R := R) (S := S) (T := T) (E := E))
        (X ⊗ₖ (aOp (M ⊗ₖ N) : Matrix ((S × T) × E) ((S × T) × E) ℂ))
      = (X ⊗ₖ N) ⊗ₖ (aOp M : Matrix (S × E) (S × E) ℂ) := by
  ext p q
  obtain ⟨⟨r, t⟩, s, e⟩ := p
  obtain ⟨⟨r', t'⟩, s', e'⟩ := q
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, regroupEquiv, Equiv.coe_fn_symm_mk,
    kroneckerMap_apply, aOp]
  ring
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
variable {R S T E : Type*} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]
omit [DecidableEq R] [DecidableEq S] [DecidableEq T] in
/-- **The Born probability across the regrouped cut.** -/
theorem bornProb_regroupVec (ψ : R × ((S × T) × E) → ℂ) (X : Matrix R R ℂ) (M : Matrix S S ℂ)
    (N : Matrix T T ℂ) :
    bornProb (regroupVec ψ) (X ⊗ₖ N) (aOp M) = bornProb ψ X (aOp (M ⊗ₖ N)) := by
  rw [bornProb, bornProb, regroupVec, ← reindex_regroupEquiv, qform_comp_equiv]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
variable {dB anc X : Type*} [Fintype dB] [DecidableEq dB] [Fintype anc] [DecidableEq anc]
  [Fintype X]
/-- **Discarding that index.** Against a positive semidefinite operator on the other party, the
family's total contribution is at most the operator's own weight. -/
theorem sum_bornProb_kron_le {dA : Type*} [Fintype dA] [DecidableEq dA] (ψ : dA × (dB × anc) → ℂ)
    {A : Matrix dA dA ℂ} (hA : A.PosSemidef) {B : X → Matrix dB dB ℂ}
    (hBsa : ∀ x, (B x)ᴴ = B x) (hB : ∀ x, B x * B x = B x) {T : X → Matrix anc anc ℂ}
    (hT : IsPVM T) :
    ∑ x, bornProb ψ A (B x ⊗ₖ T x) ≤ bornProb ψ A 1 := by
  rw [← bornProb_sum_right]
  exact bornProb_mono_right ψ hA (sum_kron_le_one hBsa hB hT)
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N] [DecidableEq N] {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- **The squared norm of a sum over orthogonal outcomes is a sum of sandwiches.** One term per
outcome, with the operator beside it on both sides; the cross terms vanish because the outcomes
annihilate each other. -/
theorem snorm_sq_sum_proj_sandwich (v : N → ℂ) {P : ι → Matrix N N ℂ} (hP : IsPVM P)
    (W : ι → Matrix N N ℂ) (s : Finset ι) :
    snorm v (∑ i ∈ s, P i * W i) ^ 2 = ∑ i ∈ s, qform v ((W i)ᴴ * P i * W i) := by
  rw [snorm_sq_sum_proj_mul v hP.isSelfAdjoint (fun i j hij => hP.orthogonal hij) W s]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (W i)ᴴ * (P i)ᴴ * (P i * W i) = (W i)ᴴ * P i * W i := by
    rw [hP.isSelfAdjoint, Matrix.mul_assoc, ← Matrix.mul_assoc (P i) (P i) (W i), hP.idem,
      ← Matrix.mul_assoc]
  rw [snorm_sq_eq_qform, Matrix.conjTranspose_mul, h]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
universe u
variable {R S C : Type*} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype C] [DecidableEq C]
omit [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C] in
/-- It is an `expVec` whose first party's register is trivial. -/
theorem sndExtVec_eq (ψ : R × S → ℂ) (χ : C → ℂ) :
    sndExtVec ψ χ
      = reindexVec (Equiv.prodPUnit R : R × Unit ≃ R) (Equiv.refl (S × C))
          (expVec ψ fun q : Unit × C => χ q.2) :=
  rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
universe u
variable {R S C : Type*} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype C] [DecidableEq C]
omit [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C] in
/-- Padding an operator by the trivial register changes nothing. -/
theorem reindex_prodPUnit (X : Matrix R R ℂ) :
    Matrix.reindex (Equiv.prodPUnit R : R × Unit ≃ R) (Equiv.prodPUnit R : R × Unit ≃ R)
        (X ⊗ₖ (1 : Matrix Unit Unit ℂ)) = X := by
  ext r r'
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
universe u
variable {R S C : Type*} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype C] [DecidableEq C]
omit [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [DecidableEq C] in
/-- The trivially padded state is a unit vector when the appended one is. -/
theorem expVec_punit_unit {χ : C → ℂ} (hχ : star χ ⬝ᵥ χ = 1) :
    star (fun q : Unit × C => χ q.2) ⬝ᵥ (fun q : Unit × C => χ q.2) = 1 := by
  rw [← hχ, dotProduct, dotProduct, Fintype.sum_prod_type, Fintype.sum_unique]
  rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
universe u
variable {R S C : Type*} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype C] [DecidableEq C]
/-- **The appended state contributes its norm and nothing else.** A Born probability whose second
operator is the identity on the appended register is the one the original state gives. -/
theorem bornProb_sndExtVec {χ : C → ℂ} (hχ : star χ ⬝ᵥ χ = 1) (ψ : R × S → ℂ)
    (X : Matrix R R ℂ) (Y : Matrix S S ℂ) :
    bornProb (sndExtVec ψ χ) X (Y ⊗ₖ (1 : Matrix C C ℂ)) = bornProb ψ X Y := by
  have h := bornProb_reindex (Equiv.prodPUnit R : R × Unit ≃ R) (Equiv.refl (S × C))
    (expVec ψ fun q : Unit × C => χ q.2) (X ⊗ₖ (1 : Matrix Unit Unit ℂ))
    (Y ⊗ₖ (1 : Matrix C C ℂ))
  rw [reindex_prodPUnit,
    show Matrix.reindex (Equiv.refl (S × C)) (Equiv.refl (S × C)) (Y ⊗ₖ (1 : Matrix C C ℂ))
      = Y ⊗ₖ (1 : Matrix C C ℂ) from rfl] at h
  rw [sndExtVec_eq, h, bornProb_expVec_kron ψ _ Matrix.PosSemidef.one Matrix.PosSemidef.one,
    bornProb_one_one (expVec_punit_unit hχ), mul_one]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
universe u
variable {R S C : Type*} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype C] [DecidableEq C]
variable {T T2 : Type*} [Fintype T] [DecidableEq T] [Fintype T2] [DecidableEq T2]
omit [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
  [Fintype T2] [DecidableEq T2] in
/-- A product of the four factors is carried by it to the product in the physical order. -/
theorem reindex_sndPairEquiv (Y : Matrix S S ℂ) (Z : Matrix C C ℂ) (V : Matrix T T ℂ)
    (V2 : Matrix T2 T2 ℂ) :
    Matrix.reindex (sndPairEquiv (S := S) (C := C) (T := T) (T2 := T2))
        (sndPairEquiv (S := S) (C := C) (T := T) (T2 := T2)) ((Y ⊗ₖ Z) ⊗ₖ (V ⊗ₖ V2))
      = ((Y ⊗ₖ V2) ⊗ₖ Z) ⊗ₖ V := by
  ext p q
  obtain ⟨⟨⟨s1, u1⟩, c1⟩, v1⟩ := p
  obtain ⟨⟨⟨s2, u2⟩, c2⟩, v2⟩ := q
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, sndPairEquiv, Equiv.coe_fn_symm_mk,
    kroneckerMap_apply]
  ring
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
universe u
variable {R S C : Type*} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype C] [DecidableEq C]
variable {T T2 : Type*} [Fintype T] [DecidableEq T] [Fintype T2] [DecidableEq T2]
/-- **The one-sided appending, read on the second party's physical register.** -/
theorem bornProb_sndPair {χ : T × T2 → ℂ} (hχ : star χ ⬝ᵥ χ = 1) (ψ : R × (S × C) → ℂ)
    (X : Matrix R R ℂ) (Y : Matrix S S ℂ) (Z : Matrix C C ℂ) :
    bornProb (reindexVec (Equiv.refl R) sndPairEquiv (sndExtVec ψ χ)) X
        (((Y ⊗ₖ (1 : Matrix T2 T2 ℂ)) ⊗ₖ Z) ⊗ₖ (1 : Matrix T T ℂ))
      = bornProb ψ X (Y ⊗ₖ Z) := by
  have h := bornProb_reindex (Equiv.refl R) (sndPairEquiv (S := S) (C := C) (T := T) (T2 := T2))
    (sndExtVec ψ χ) X ((Y ⊗ₖ Z) ⊗ₖ (1 : Matrix (T × T2) (T × T2) ℂ))
  rw [bornProb_sndExtVec hχ] at h
  rw [show Matrix.reindex (Equiv.refl R) (Equiv.refl R) X = X from rfl,
    show (1 : Matrix (T × T2) (T × T2) ℂ)
      = (1 : Matrix T T ℂ) ⊗ₖ (1 : Matrix T2 T2 ℂ) from (Matrix.one_kronecker_one).symm,
    reindex_sndPairEquiv] at h
  exact h
end
end MIPRE

attribute [instance] MIPRE.QLD.MirrorSimul.instFintypeEa MIPRE.QLD.MirrorSimul.instDecEqEa MIPRE.QLD.MirrorSimul.instFintypeEb MIPRE.QLD.MirrorSimul.instDecEqEb

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
universe u
set_option synthInstance.maxSize 1000
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
attribute [instance] MIPRE.QLD.MirrorSimul.instFintypeEa MIPRE.QLD.MirrorSimul.instDecEqEa MIPRE.QLD.MirrorSimul.instFintypeEb MIPRE.QLD.MirrorSimul.instDecEqEb
/-- **The physical state is the first cut's `mVec` with the appended pair, both halves on Bob's
side.** Along the cut `mTilde` needs, `A''` has already moved to Alice, so what the appending adds
is entirely Bob's: `B'` beside his own space and `B''` outermost. -/
theorem physVec_eq_sndPair :
    M.physVec = reindexVec (Equiv.refl _) sndPairEquiv
      (sndExtVec M.toFirst.mVec (epr (F := F) (n := Fin m → Bool))) :=
  rfl
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
universe u
set_option synthInstance.maxSize 1000
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
attribute [instance] MIPRE.QLD.MirrorSimul.instFintypeEa MIPRE.QLD.MirrorSimul.instDecEqEa MIPRE.QLD.MirrorSimul.instFintypeEb MIPRE.QLD.MirrorSimul.instDecEqEb
/-- **Everything proved on the first cut's `mVec` reads on the physical state.** Bob's operator is
extended by the identity on both halves of the appended pair, and the pair contributes its own norm
and nothing else; Alice's needs no extension, being already on her physical register. This is the
bridge the assemblies of `lem:qld-pauli-selfcons` and `lem:qld-swap` run through, and its mirror
image --- by `physVec_mirror` --- does the same for Bob's side. -/
theorem bornProb_physVec (X : Matrix (((dA × Anc F m) × M.Ea) × Anc F m)
      (((dA × Anc F m) × M.Ea) × Anc F m) ℂ) (Y : Matrix dB dB ℂ) (Z : Matrix M.Eb M.Eb ℂ) :
    bornProb M.physVec X
        (((Y ⊗ₖ (1 : Matrix (Anc F m) (Anc F m) ℂ)) ⊗ₖ Z) ⊗ₖ (1 : Matrix (Anc F m) (Anc F m) ℂ))
      = bornProb M.toFirst.mVec X (Y ⊗ₖ Z) := by
  rw [M.physVec_eq_sndPair]
  exact bornProb_sndPair (epr_unit (F := F) (n := Fin m → Bool)) _ _ _ _
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
/-- `A (x) (sum B) = sum (A (x) B)`, on any registers. -/
theorem kron_sum' {R S ι : Type*} [Fintype R] [Fintype S] (s : Finset ι)
    (A : Matrix R R ℂ) (B : ι → Matrix S S ℂ) :
    A ⊗ₖ (∑ x ∈ s, B x) = ∑ x ∈ s, A ⊗ₖ B x := by
  ext p q
  simp [Matrix.sum_apply, Finset.mul_sum]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
/-- **A Weyl family's spectral projectors are a projective measurement.** The three facts are in
Foundations one by one; this is them bundled, which is the form `isPVM_kron` consumes. -/
theorem isPVM_proj {n : Type*} [Fintype n] [DecidableEq n]
    {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w) : IsPVM (proj w) where
  isSelfAdjoint e := proj_conjTranspose hw e
  idem e := by simpa using proj_mul_proj hw e e
  sum_eq_one := sum_proj hw
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
/-- **The chain's summands are a projective measurement** in the pair `(g, h)`: a marginal of a
projective pair measurement, tensored with a Weyl spectral projector. -/
theorem isPVM_chainOp (P : SimulPair ψ MA MB δ) (W : Bas) :
    IsPVM fun p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m => P.chainOp W p := by
  exact isPVM_kron (isPVM_polyMarg P.SA_proj W) (isPVM_proj (isWeylFamily_weylOf W))
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable {d' : Type} [Fintype d'] [DecidableEq d']
variable {dA' dB' anc ι κ : Type*} [Fintype dA'] [DecidableEq dA'] [Fintype dB'] [DecidableEq dB']
  [Fintype anc] [DecidableEq anc] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [Field F] [Algebra (ZMod 2) F] in
/-- **The outer shape both remaining displays share.** Each is a bound on the summed squared norm
of the chain's terms, grouped by the measurement outcome. Projectivity turns each group into a sum
of sandwiches (`snorm_sq_sum_proj_sandwich`), the groups are the fibres of the outcome map, so the
double sum is the single one over the index --- and what is left to bound is a sum of sandwiches
with no outcome in it. The index may be a subset, which is what `eq:qld-pulling-10` needs: it sums
over the pairs whose outcomes *disagree*. -/
theorem sum_snorm_sq_fiber_sandwich_subset_le {N : Type*} [Fintype N] [DecidableEq N] (v : N → ℂ)
    {P : ι → Matrix N N ℂ} (hP : IsPVM P) (W : ι → Matrix N N ℂ)
    (c : ι → F) (D : Finset ι) {ε : ℝ}
    (hbound : ∑ i ∈ D, qform v ((W i)ᴴ * P i * W i) ≤ ε) :
    ∑ a : F, snorm v (∑ i ∈ D.filter fun i => c i = a, P i * W i) ^ 2 ≤ ε := by
  classical
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => snorm_sq_sum_proj_sandwich v hP W _,
    Finset.sum_fiberwise D c fun i => qform v ((W i)ᴴ * P i * W i)]
  exact hbound
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable {d' : Type} [Fintype d'] [DecidableEq d']
variable {dA' dB' anc ι κ : Type*} [Fintype dA'] [DecidableEq dA'] [Fintype dB'] [DecidableEq dB']
  [Fintype anc] [DecidableEq anc] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [Field F] [Algebra (ZMod 2) F] in
/-- The case the first of the two displays uses, where the whole index is summed over. -/
theorem sum_snorm_sq_fiber_sandwich_le {N : Type*} [Fintype N] [DecidableEq N] (v : N → ℂ)
    {P : ι → Matrix N N ℂ} (hP : IsPVM P) (W : ι → Matrix N N ℂ)
    (c : ι → F) {ε : ℝ} (hbound : ∑ i, qform v ((W i)ᴴ * P i * W i) ≤ ε) :
    ∑ a : F, snorm v (∑ i ∈ univ.filter fun i => c i = a, P i * W i) ^ 2 ≤ ε :=
  sum_snorm_sq_fiber_sandwich_subset_le v hP W c univ hbound
end
end MIPRE.QLD

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
/-- It is a projective family in the pair `(g, h)`, by the lemma that says the first cut's is. -/
theorem isPVM_aliceChainOp (W : Bas) : IsPVM (M.aliceChainOp W) := isPVM_chainOp M.toFirst W
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
/-- It is projective: `aOp U * bOp V` is `U (x) V`, and each party's family is projective. -/
theorem isPVM_chainP (W : Bas) : IsPVM (M.chainP W) := by
  have hrw : M.chainP W = fun t => (M.aliceChainOp W t.1) ⊗ₖ (M.bobWeyl W t.2) :=
    funext fun t => aOp_mul_bOp_eq _ _
  rw [hrw]
  exact isPVM_kron (M.isPVM_aliceChainOp W)
    (IsPVM.bOp (isPVM_proj (isWeylFamily_weylOf W)))
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
/-- **The sandwich splits across the parties**, each factor being local. -/
theorem chainW_sandwich (W : Bas) (u : Point F m)
    (t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m) :
    (M.chainW W u t)ᴴ * (aOp (M.aliceChainOp W t.1) * bOp (M.bobWeyl W t.2))
        * M.chainW W u t
      = aOp ((1 - M.aliceHat W u (t.1.1.eval u))ᴴ * M.aliceChainOp W t.1
            * (1 - M.aliceHat W u (t.1.1.eval u)))
        * bOp ((M.bobHat W u (t.1.1.eval u + dotF t.1.2 (indVec u) + dotF t.2 (indVec u)))ᴴ
            * M.bobWeyl W t.2
            * M.bobHat W u (t.1.1.eval u + dotF t.1.2 (indVec u) + dotF t.2 (indVec u))) := by
  rw [chainW, aOp_bOp_conjTranspose, aOp_bOp_mul_aOp_bOp, aOp_bOp_mul_aOp_bOp]
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
/-- **Summing the Weyl outcome out of Alice's summand** leaves her pair measurement's marginal
alone, extended by the identity on `A''`. -/
theorem sum_aliceChainOp (W : Bas) (g : LowIndDegPoly (F := F) (m := m) (d := d)) :
    (∑ h : Anc F m, M.aliceChainOp W (g, h))
      = aOp (((polyMarg M.SA W).mats g).val) := by
  rw [show (∑ h : Anc F m, M.aliceChainOp W (g, h))
      = ∑ h : Anc F m, (((polyMarg M.SA W).mats g).val) ⊗ₖ proj (weylOf W) h from rfl,
    ← kron_sum' univ, (isPVM_proj (isWeylFamily_weylOf W)).sum_eq_one]
  rfl
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
/-- **So the Weyl index collapses out of her sandwich**, the gap operator not depending on it. -/
theorem sum_aliceChainOp_sandwich (W : Bas) (u : Point F m)
    (g : LowIndDegPoly (F := F) (m := m) (d := d)) :
    (∑ h : Anc F m, (1 - M.aliceHat W u (g.eval u))ᴴ * M.aliceChainOp W (g, h)
        * (1 - M.aliceHat W u (g.eval u)))
      = (1 - M.aliceHat W u (g.eval u))ᴴ * aOp (((polyMarg M.SA W).mats g).val)
        * (1 - M.aliceHat W u (g.eval u)) := by
  rw [← Finset.sum_mul, ← Finset.mul_sum, M.sum_aliceChainOp W g]
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
/-- **Alice's sandwich is positive semidefinite**, being a projector conjugated. -/
theorem posSemidef_aliceSand (W : Bas) (u : Point F m)
    (t : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :
    ((1 - M.aliceHat W u (t.1.eval u))ᴴ * M.aliceChainOp W t
      * (1 - M.aliceHat W u (t.1.eval u))).PosSemidef :=
  Matrix.PosSemidef.conjTranspose_mul_mul_same ((M.isPVM_aliceChainOp W).posSemidef t) _
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
/-- **Display `eq:qld-pulling-8`: dropping the far party.** Summed over Bob's Weyl outcome, his
factor is a projector times a projective measurement, so at most the identity. -/
theorem sum_bornProb_chainW_drop_le (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
    (W : Bas) (u : Point F m)
    (t : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :
    (∑ h' : Anc F m, bornProb M.physVec
        ((1 - M.aliceHat W u (t.1.eval u))ᴴ * M.aliceChainOp W t
          * (1 - M.aliceHat W u (t.1.eval u)))
        ((M.bobHat W u (t.1.eval u + dotF t.2 (indVec u) + dotF h' (indVec u)))ᴴ
          * M.bobWeyl W h'
          * M.bobHat W u (t.1.eval u + dotF t.2 (indVec u) + dotF h' (indVec u))))
      ≤ bornProb M.physVec ((1 - M.aliceHat W u (t.1.eval u))ᴴ * M.aliceChainOp W t
          * (1 - M.aliceHat W u (t.1.eval u))) 1 := by
  rw [Finset.sum_congr rfl fun h' (_ : h' ∈ univ) => by
    rw [M.bobHat_conj_bobWeyl hprojB W u _ h']]
  exact sum_bornProb_kron_le M.physVec (M.posSemidef_aliceSand W u t)
    (fun h' => by
      rw [aOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        SimulPair.hatMats_conjTranspose])
    (fun h' => by rw [← aOp_mul, (isPVM_hatMats hprojB W u).idem])
    (isPVM_proj (isWeylFamily_weylOf W))
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
/-- **The bridge from the physical state back to `Phi`.** An operator that is Alice's alone, and
the identity on the half of the appended pair she holds, sees the state `lem:qld-simultaneous`
already describes. The identity is spelled out as a fourfold tensor product because the
intermediate `mVec` carries Bob's padding under `toFirst`'s name for it, and rewriting inside
that application is not type-correct. -/
theorem bornProb_physVec_aOp_kron
    (Z : Matrix ((dA × Anc F m) × M.Ea) ((dA × Anc F m) × M.Ea) ℂ) :
    bornProb M.physVec (aOp Z)
        ((((1 : Matrix dB dB ℂ) ⊗ₖ (1 : Matrix (Anc F m) (Anc F m) ℂ))
          ⊗ₖ (1 : Matrix M.Eb M.Eb ℂ)) ⊗ₖ (1 : Matrix (Anc F m) (Anc F m) ℂ))
      = bornProb M.Φ Z 1 := by
  have h1 := M.bornProb_physVec (aOp Z) (1 : Matrix dB dB ℂ) (1 : Matrix M.Eb M.Eb ℂ)
  have h2 := bornProb_regroupVec M.Φ Z (1 : Matrix dB dB ℂ) (1 : Matrix (Anc F m) (Anc F m) ℂ)
  rw [show (aOp ((1 : Matrix dB dB ℂ) ⊗ₖ (1 : Matrix (Anc F m) (Anc F m) ℂ))
      : Matrix ((dB × Anc F m) × M.Eb) _ ℂ) = 1 from by
    rw [Matrix.one_kronecker_one, aOp_one]] at h2
  exact h1.trans h2
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
/-- The same, with the identity collapsed. -/
theorem bornProb_physVec_aOp
    (Z : Matrix ((dA × Anc F m) × M.Ea) ((dA × Anc F m) × M.Ea) ℂ) :
    bornProb M.physVec (aOp Z) 1 = bornProb M.Φ Z 1 := by
  have e : ((((1 : Matrix dB dB ℂ) ⊗ₖ (1 : Matrix (Anc F m) (Anc F m) ℂ))
      ⊗ₖ (1 : Matrix M.Eb M.Eb ℂ)) ⊗ₖ (1 : Matrix (Anc F m) (Anc F m) ℂ)) = 1 := by
    rw [Matrix.one_kronecker_one, Matrix.one_kronecker_one, Matrix.one_kronecker_one]
  rw [← e]
  exact M.bornProb_physVec_aOp_kron Z
end
end MIPRE.QLD.MirrorSimul

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD.MirrorSimul
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
set_option maxHeartbeats 1000000 in
theorem _root_.solution (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
    (W : Bas) (v : Anc F m) (u : Point F m) :
    ∑ a : F, snorm M.physVec
        (∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m
            => dotF (chainLabel t.1.1 t.1.2) v = a,
          M.chainP W t * M.chainW W u t) ^ 2
      ≤ ∑ g : LowIndDegPoly (F := F) (m := m) (d := d), snorm M.Φ
          (aOp (((polyMarg M.SA W).mats g).val
            * (1 - (aOp (hatMats MA W u (g.eval u)) : Matrix ((dA × Anc F m) × M.Ea) _ ℂ))))
          ^ 2 := by
  classical
  refine sum_snorm_sq_fiber_sandwich_le M.physVec (M.isPVM_chainP W) (M.chainW W u)
    (fun t => dotF (chainLabel t.1.1 t.1.2) v) ?_
  rw [Finset.sum_congr rfl fun t (_ : t ∈ univ) => by
    rw [show M.chainP W t = aOp (M.aliceChainOp W t.1) * bOp (M.bobWeyl W t.2) from rfl,
      M.chainW_sandwich W u t, ← bornProb_eq_qform], Fintype.sum_prod_type]
  refine le_trans (Finset.sum_le_sum fun t1 (_ : t1 ∈ univ) =>
    M.sum_bornProb_chainW_drop_le hprojB W u t1) ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun g _ => le_of_eq ?_
  have hexp : (1 - M.aliceHat W u (g.eval u))ᴴ * aOp (((polyMarg M.SA W).mats g).val)
        * (1 - M.aliceHat W u (g.eval u))
      = aOp ((1 - (aOp (hatMats MA W u (g.eval u)) : Matrix ((dA × Anc F m) × M.Ea) _ ℂ))ᴴ
          * ((polyMarg M.SA W).mats g).val
          * (1 - (aOp (hatMats MA W u (g.eval u)) : Matrix ((dA × Anc F m) × M.Ea) _ ℂ))) := by
    rw [aliceHat, ← aOp_one, ← aOp_sub, aOp_conjTranspose, ← aOp_mul, ← aOp_mul]
  rw [← bornProb_sum_left, M.sum_aliceChainOp_sandwich W u g, hexp, M.bornProb_physVec_aOp,
    snorm_sq_eq_qform, bornProb_eq_qform, bOp_one, Matrix.mul_one, aOp_conjTranspose, ← aOp_mul]
  congr 1
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (((polyMarg M.SA W).mats g).val)ᴴ,
    (isPVM_polyMarg M.SA_proj W).isSelfAdjoint g, (isPVM_polyMarg M.SA_proj W).idem g]
end MIPRE.QLD.MirrorSimul
