-- Prove2me | solution 1 for MIPRE.QLD.MirrorSimul.sum_bornProb_physVec_ge
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:22:30.853139+00:00
-- url     : https://prove2.me/submissions/fef6c560-c75d-44fc-830b-4eb6b68dbe9c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/SwapItemTwo.lean (solution of MIPRE.QLD.MirrorSimul.sum_bornProb_physVec_ge);
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
import Definitions.Def_MIPRE_Background_QLD_ChainAssembly
import Definitions.Def_MIPRE_Background_QLD_SelfCons
import Definitions.Def_MIPRE_Background_QLD_SwapItemOne
import Definitions.Def_MIPRE_Background_QLD_SwapItemTwo
import Theorems.Thm_MIPRE_QLD_SimulPair_sum_bornProb_cubeData_ge
import Theorems.Thm_MIPRE_QLD_inconsistency_pt_pauli_le
import Theorems.Thm_MIPRE_QLD_inconsistency_pt_pt_le
import Theorems.Thm_MIPRE_QLD_povmValue_swapped_le
import Theorems.Thm_MIPRE_QLD_sum_diag_eq_one_sub
import Theorems.Thm_MIPRE_QLD_swapVec_unit
import Theorems.Thm_MIPRE_Weyl_epr_unit
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_bornProb_reindex
import Theorems.Thm_MIPRE_bornProb_swapVec
import Theorems.Thm_MIPRE_mulVec_kron_kron_expVec
import Theorems.Thm_MIPRE_norm_stateVecB
import Theorems.Thm_MIPRE_sum_snorm_sq_triangle3
import Theorems.Thm_MIPRE_sum_stateSqNorm_le_one
import Theorems.Thm_MIPRE_sum_uniform_eq_one
import Theorems.Thm_MIPRE_swapVec_dotProduct
import Theorems.Thm_MIPRE_weightA_ge
import Theorems.Thm_MIPRE_weightB_ge
import Theorems.Thm_MIPRE_xDev_eq

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
omit [Fintype N] in
theorem evec_sub (v w : N → ℂ) : evec (v - w) = evec v - evec w := rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem snorm_sub_comm (M M' : Matrix N N ℂ) : snorm v (M - M') = snorm v (M' - M) := by
  rw [snorm, snorm, Matrix.sub_mulVec, Matrix.sub_mulVec, evec_sub, evec_sub, norm_sub_rev]
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
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- Bob's version, by the swap. -/
theorem sum_stateSqNormB_le_one {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (N : POVM B dB) :
    ∑ b, ‖stateVecB ψ (((N.mats b).val))‖ ^ 2 ≤ 1 := by
  have hψ' : star (swapVec ψ) ⬝ᵥ swapVec ψ = 1 := by rw [swapVec_dotProduct]; exact hψ
  have h := sum_stateSqNorm_le_one (dA := dB) (dB := dA) (A := B) hψ' N
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_)) h
  rw [norm_stateVecB, stateSqNorm]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
theorem xSqNorm_eq_sq (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xSqNorm ψ A B = xNorm ψ A B ^ 2 := rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
/-- The deviation is the state-norm of the single operator `A ⊗ Id - Id ⊗ B` on the product
space, which is what the operator-norm calculus of `MIPRE/Foundations/OpBound.lean` consumes. -/
theorem xNorm_eq_snorm (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xNorm ψ A B = snorm ψ ((aOp A : Matrix (dA × dB) _ ℂ) - bOp B) := by
  rw [xNorm, snorm, Matrix.sub_mulVec, evec_sub]
  rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
/-- The squared cross-party deviation as a `snorm` on the joint space, which is the form the
chains of the appendix are run in. -/
theorem xSqNorm_eq_snorm_sq (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xSqNorm ψ A B = snorm ψ ((aOp A : Matrix (dA × dB) (dA × dB) ℂ) - bOp B) ^ 2 := by
  rw [xSqNorm_eq_sq, xNorm_eq_snorm]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
/-- The weighted form, over a set of questions: the shape every item of `lem:qld-win` is stated
in. -/
theorem sum_weighted_snorm_sq_triangle3 {ι κ : Type*} [Fintype κ] (v : N → ℂ)
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (S : Finset ι) (P Q R T : ι → κ → Matrix N N ℂ) :
    ∑ i ∈ S, w i * ∑ o, snorm v (P i o - T i o) ^ 2
      ≤ 3 * ∑ i ∈ S, w i * ∑ o, snorm v (P i o - Q i o) ^ 2
        + 3 * ∑ i ∈ S, w i * ∑ o, snorm v (Q i o - R i o) ^ 2
        + 3 * ∑ i ∈ S, w i * ∑ o, snorm v (R i o - T i o) ^ 2 := by
  have hstep : ∀ i ∈ S, w i * ∑ o, snorm v (P i o - T i o) ^ 2
      ≤ 3 * (w i * ∑ o, snorm v (P i o - Q i o) ^ 2)
        + 3 * (w i * ∑ o, snorm v (Q i o - R i o) ^ 2)
        + 3 * (w i * ∑ o, snorm v (R i o - T i o) ^ 2) := by
    intro i _
    have h := sum_snorm_sq_triangle3 v (P i) (Q i) (R i) (T i)
    nlinarith [hw i]
  refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
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
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
variable {μ : X → ℝ} {ψ : dA × dB → ℂ}
theorem weightA_le_one (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : X → POVM Λ dA) : weightA μ ψ M ≤ 1 := by
  calc weightA μ ψ M ≤ ∑ x, μ x * 1 :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (sum_stateSqNorm_le_one hψ (M x)) (hμ x)
    _ = 1 := by simp [hμ1]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
variable {μ : X → ℝ} {ψ : dA × dB → ℂ}
theorem weightB_le_one (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (N : X → POVM Λ dB) : weightB μ ψ N ≤ 1 := by
  calc weightB μ ψ N ≤ ∑ x, μ x * 1 :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (sum_stateSqNormB_le_one hψ (N x)) (hμ x)
    _ = 1 := by simp [hμ1]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
variable {μ : X → ℝ} {ψ : dA × dB → ℂ}
/-- The cross deviation is at most twice the disagreement. -/
theorem xDev_le (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : X → POVM Λ dA) (N : X → POVM Λ dB) :
    xDev μ ψ M N ≤ 2 * (1 - agreeSum μ ψ M N) := by
  rw [xDev_eq]
  have := weightA_le_one hμ hμ1 hψ M
  have := weightB_le_one hμ hμ1 hψ N
  linarith
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
variable {μ : X → ℝ} {ψ : dA × dB → ℂ}
/-- **The weighted triangle inequality for cross deviations**: Alice's `A` against Bob's `D`,
through Bob's `B` and Alice's `C`. -/
theorem xDev_triangle (hμ : ∀ x, 0 ≤ μ x) (A C : X → POVM Λ dA) (B D : X → POVM Λ dB) :
    xDev μ ψ A D ≤ 3 * xDev μ ψ A B + 3 * xDev μ ψ C B + 3 * xDev μ ψ C D := by
  have h := sum_weighted_snorm_sq_triangle3 ψ hμ (univ : Finset X)
    (fun x a => (aOp (((A x).mats a).val) : Matrix (dA × dB) (dA × dB) ℂ))
    (fun x a => bOp (((B x).mats a).val)) (fun x a => aOp (((C x).mats a).val))
    (fun x a => bOp (((D x).mats a).val))
  have hmid : ∀ x a, snorm ψ ((bOp (((B x).mats a).val) : Matrix (dA × dB) (dA × dB) ℂ)
      - aOp (((C x).mats a).val)) ^ 2
      = xSqNorm ψ (((C x).mats a).val) (((B x).mats a).val) := fun x a => by
    rw [xSqNorm_eq_snorm_sq, snorm_sub_comm]
  simp only [← xSqNorm_eq_snorm_sq, hmid] at h
  exact h
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
variable {μ : X → ℝ} {ψ : dA × dB → ℂ}
/-- **The agreement triangle** (`fact:triangle-for-simeq`, item 1, with `11 δ` in place of the
paper's `9 δ`): agreement is transitive across the two parties, for POVMs. -/
theorem agreeSum_triangle (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (A C : X → POVM Λ dA) (B D : X → POVM Λ dB) {δ : ℝ}
    (hAB : 1 - agreeSum μ ψ A B ≤ δ) (hCB : 1 - agreeSum μ ψ C B ≤ δ)
    (hCD : 1 - agreeSum μ ψ C D ≤ δ) :
    1 - agreeSum μ ψ A D ≤ 11 * δ := by
  have hAD := xDev_eq (μ := μ) (ψ := ψ) A D
  have htri := xDev_triangle (μ := μ) (ψ := ψ) hμ A C B D
  have h1 := xDev_le hμ hμ1 hψ A B
  have h2 := xDev_le hμ hμ1 hψ C B
  have h3 := xDev_le hμ hμ1 hψ C D
  have hwA := weightA_ge hμ hμ1 hψ A B hAB
  have hwD := weightB_ge hμ hμ1 hψ C D hCD
  linarith
end
end MIPRE

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem inconsistency_eq_sum_pairInconsistency {X : Type*} [Fintype X] (μ : X → ℝ)
    (ψ : dA × dB → ℂ) (M : X → POVM A dA) (N : X → POVM A dB) :
    inconsistency μ ψ M N = ∑ x, μ x * pairInconsistency ψ (M x) (N x) := rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem synPOVM_mats (W : Bas) (u : Point F m) (a : F) :
    (((synPOVM W u).mats a).val) = syn (weylOf W) (indVec u) a := rfl
end
end MIPRE.QLD

namespace MIPRE
noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
theorem uniform_nonneg (X : Type*) [Fintype X] (x : X) : 0 ≤ uniform X x :=
  inv_nonneg.mpr (Nat.cast_nonneg _)
end
end MIPRE

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {X A dA dB : Type*} [Fintype X] [Fintype A] [DecidableEq A] [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
/-- **The inconsistency is one minus the agreement.** -/
theorem sum_bornProb_diag_eq {μ : X → ℝ} (hμ : ∑ x, μ x = 1) {Φ : dA × dB → ℂ}
    (hΦ : star Φ ⬝ᵥ Φ = 1) (M : X → POVM A dA) (N : X → POVM A dB) :
    ∑ x, μ x * ∑ a, bornProb Φ (((M x).mats a).val) (((N x).mats a).val)
      = 1 - inconsistency μ Φ M N := by
  have hx : ∀ x, ∑ a, bornProb Φ (((M x).mats a).val) (((N x).mats a).val)
      = 1 - pairInconsistency Φ (M x) (N x) := fun x => sum_diag_eq_one_sub hΦ (M x) (N x)
  rw [Finset.sum_congr rfl fun x (_ : x ∈ univ) => by rw [hx x],
    inconsistency_eq_sum_pairInconsistency,
    Finset.sum_congr rfl fun x (_ : x ∈ univ) => mul_sub (μ x) 1 (pairInconsistency Φ (M x) (N x)),
    Finset.sum_sub_distrib]
  simp only [mul_one]
  rw [hμ]
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
variable {R S T E : Type*} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]
omit [DecidableEq R] [DecidableEq S] [DecidableEq T] [DecidableEq E] in
/-- A regrouped unit vector is a unit vector. -/
theorem regroupVec_unit {ψ : R × ((S × T) × E) → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    star (regroupVec ψ) ⬝ᵥ regroupVec ψ = 1 := by
  rw [← hψ]
  exact Equiv.sum_comp (regroupEquiv (R := R) (S := S) (T := T) (E := E)).symm
    fun p => star ψ p * ψ p
end
end MIPRE

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
omit [Fintype F] [DecidableEq F] in
/-- In characteristic two a sum is its own difference. -/
theorem add_self_eq_zero' (a : F) : a + a = 0 := by
  rw [← two_mul, MIPRE.Weyl.two_eq_zero, zero_mul]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
omit [Fintype F] [DecidableEq F] in
/-- The partner of `a` in a fibre of the sum, in characteristic two. -/
theorem add_eq_iff_eq_add (a b c : F) : a + b = c ↔ b = c + a := by
  constructor
  · rintro rfl
    rw [add_comm a b, add_assoc, add_self_eq_zero', add_zero]
  · rintro rfl
    rw [← add_assoc, add_comm a c, add_assoc, add_self_eq_zero', add_zero]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {d' : Type} [Fintype d'] [DecidableEq d']
theorem hatPtPOVM_eq_kron (M : Question F m → POVM (Answer F m d) d') (W : Bas)
    (u : Point F m) :
    hatPtPOVM M W u = ((ptAtPOVM M W u).kron (synPOVM W u)).map fun p => p.1 + p.2 := rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {d' : Type} [Fintype d'] [DecidableEq d']
/-- **The convolution, summed along the shift.** In characteristic two `c + a` is the partner of
`a` in the fibre of the sum over `c`, so summing the product family along `a` is summing it over
that fibre --- which is the hatted point measurement at `c`. This is the step that turns
`mTilde`'s defining sum into the hatted point measurement the helper's agreement names. -/
theorem sum_kron_syn_eq_hatMats (M : Question F m → POVM (Answer F m d) d') (W : Bas)
    (u : Point F m) (c : F) :
    ∑ a : F, (((ptAtPOVM M W u).mats a).val ⊗ₖ ((synPOVM W u).mats (c + a)).val)
      = hatMats M W u c := by
  classical
  rw [hatMats, hatPtPOVM_eq_kron, POVM.map_mats, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (c + a) (fun b _ hb => if_neg fun h => hb
      ((add_eq_iff_eq_add a b c).mp h)) fun hmem => absurd (mem_univ (c + a)) hmem,
    if_pos ((add_eq_iff_eq_add a (c + a) c).mpr rfl), POVM.kron_mats]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
omit [Field F] [Algebra (ZMod 2) F] [NeZero m] in
/-- The marginal `sCoarse` of `ExactPauli.lean` is `polyMarg`. -/
theorem sCoarse_eq_polyMarg {R : Type*} [Fintype R] [DecidableEq R]
    (S : POVM (PolyPair F m d) R) (W : Bas)
    (g : LowIndDegPoly (F := F) (m := m) (d := d)) :
    sCoarse (fun p => ((S.mats p).val)) (PolyPair.proj W) g = ((polyMarg S W).mats g).val :=
  (POVM.map_mats _ _ _).symm
end
end MIPRE.QLD

namespace MIPRE.QLD.SimulPair
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
theorem mVec_unit : star P.mVec ⬝ᵥ P.mVec = 1 := regroupVec_unit P.Φ_unit
end
end MIPRE.QLD.SimulPair

namespace MIPRE.QLD.SimulPair
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
theorem mTildeAt_eq (W : Bas) (u : Point F m) (a : F) :
    P.mTildeAt W u a
      = ∑ g, ((polyMarg P.SA W).mats g).val
          ⊗ₖ ((synPOVM W u).mats (dotF (cubeData g) (indVec u) + a)).val :=
  Finset.sum_congr rfl fun g _ => by rw [sCoarse_eq_polyMarg, synPOVM_mats]
end
end MIPRE.QLD.SimulPair

namespace MIPRE.QLD.SimulPair
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
/-- **One term of the agreement, across the cut.** -/
theorem bornProb_mTildeAt (W : Bas) (u : Point F m) (a : F) :
    bornProb P.mVec (P.mTildeAt W u a) (aOp (((ptAtPOVM MB W u).mats a).val))
      = ∑ g, bornProb P.Φ (((polyMarg P.SA W).mats g).val)
          (aOp ((((ptAtPOVM MB W u).mats a).val)
            ⊗ₖ ((synPOVM W u).mats (dotF (cubeData g) (indVec u) + a)).val)) := by
  rw [P.mTildeAt_eq W u a, bornProb_sum_left, mVec]
  exact Finset.sum_congr rfl fun g _ => bornProb_regroupVec _ _ _ _
end
end MIPRE.QLD.SimulPair

namespace MIPRE.QLD.SimulPair
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
/-- **The agreement of `M~^{W,ind_m(u)}` with the strategy's point measurement is the outcome sum
the helper's chain bounds.** -/
theorem sum_bornProb_mTildeAt (W : Bas) (u : Point F m) :
    ∑ a : F, bornProb P.mVec (P.mTildeAt W u a) (aOp (((ptAtPOVM MB W u).mats a).val))
      = ∑ g, bornProb P.Φ (((polyMarg P.SA W).mats g).val)
          (aOp (hatMats MB W u (dotF (cubeData g) (indVec u)))) := by
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => P.bornProb_mTildeAt W u a, Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← sum_kron_syn_eq_hatMats MB W u (dotF (cubeData g) (indVec u)), aOp_sum,
    bornProb_sum_right]
end
end MIPRE.QLD.SimulPair

namespace MIPRE.QLD.SimulPair
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
/-- **Item 1 of `lem:qld-exact-paulis`**: the measurement `M~^{W,ind_m(u)}` agrees with the
strategy's `(Point, W)` measurement with probability at least `1 - delta_qld`, on average over a
uniform point, where
`delta_qld = delta_S + 2 (delta_S + sqrt(688 eps) + md/q)`. -/
theorem sum_bornProb_mTilde_ge {hm : m ∣ Fintype.card F} {ε : ℝ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d) (W : Bas) :
    1 - (δ + 2 * ((δ + Real.sqrt (688 * ε)) + (m : ℝ) * d / Fintype.card F))
      ≤ ∑ u, uniform (Point F m) u * ∑ a : F,
          bornProb P.mVec (P.mTildeAt W u a) (aOp (((ptAtPOVM MB W u).mats a).val)) := by
  have h := P.sum_bornProb_cubeData_ge (hm := hm) hψ hfail hprojB hd W
  have hrw : ∀ u : Point F m,
      uniform (Point F m) u * ∑ g, bornProb P.Φ (((polyMarg P.SA W).mats g).val)
          (aOp (hatMats MB W u (dotF (cubeData g) (indVec u))))
        = uniform (Point F m) u * ∑ a : F,
          bornProb P.mVec (P.mTildeAt W u a) (aOp (((ptAtPOVM MB W u).mats a).val)) :=
    fun u => by rw [P.sum_bornProb_mTildeAt W u]
  rwa [Finset.sum_congr rfl fun u (_ : u ∈ univ) => hrw u] at h
end
end MIPRE.QLD.SimulPair

namespace MIPRE.QLD.SimulPair
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
/-- **Item 1 of `lem:qld-exact-paulis` as the paper states it**: on average over a uniform point,
the measurement `M~^{W, ind_m(u)}` and the strategy's `(Point, W)` measurement are consistent to
within `delta_S + 2 (delta_S + sqrt(688 eps) + md/q)`. -/
theorem inconsistency_mTilde_le {hm : m ∣ Fintype.card F} {ε : ℝ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d) (W : Bas) :
    inconsistency (uniform (Point F m)) P.mVec
        (fun u => (P.isPVM_mTildeAt W u).toPOVM) (fun u => (ptAtPOVM MB W u).aOp)
      ≤ δ + 2 * ((δ + Real.sqrt (688 * ε)) + (m : ℝ) * d / Fintype.card F) := by
  have hd0 := sum_bornProb_diag_eq (sum_uniform_eq_one (Point F m)) P.mVec_unit
    (fun u => (P.isPVM_mTildeAt W u).toPOVM) fun u => (ptAtPOVM MB W u).aOp (E := P.EB)
  have hge := P.sum_bornProb_mTilde_ge (hm := hm) hψ hfail hprojB hd W
  simp only [IsPVM.toPOVM_mats, POVM.aOp_mats] at hd0
  linarith
end
end MIPRE.QLD.SimulPair

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {X Λ : Type*} [Fintype X] [Fintype Λ] [DecidableEq Λ]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **The agreement triangle, read as inconsistencies.** `A` against `D` through `B` and `C`,
where the two middle legs share a family on each side. -/
theorem inconsistency_triangle {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (A C : X → POVM Λ dA) (B D : X → POVM Λ dB)
    {δ : ℝ} (hAB : inconsistency μ ψ A B ≤ δ) (hCB : inconsistency μ ψ C B ≤ δ)
    (hCD : inconsistency μ ψ C D ≤ δ) :
    inconsistency μ ψ A D ≤ 11 * δ := by
  have hbridge : ∀ (M : X → POVM Λ dA) (N : X → POVM Λ dB),
      1 - agreeSum μ ψ M N = inconsistency μ ψ M N := fun M N => by
    rw [agreeSum, sum_bornProb_diag_eq hμ1 hψ M N]
    ring
  have h := agreeSum_triangle (δ := δ) hμ0 hμ1 hψ A C B D
    ((hbridge A B).symm ▸ hAB) ((hbridge C B).symm ▸ hCB) ((hbridge C D).symm ▸ hCD)
  rwa [hbridge] at h
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {R S T E X Λ : Type*} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E] [Fintype X] [Fintype Λ] [DecidableEq Λ]
/-- **A consistency between operators that ignore the moved register reads the same on both
cuts.** -/
theorem inconsistency_regroupVec (μ : X → ℝ) (ψ : R × ((S × T) × E) → ℂ)
    (A : X → POVM Λ R) (B : X → POVM Λ S) :
    inconsistency μ (regroupVec ψ) (fun x => (A x).aOp (E := T)) (fun x => (B x).aOp (E := E))
      = inconsistency μ ψ A fun x => ((B x).aOp (E := T)).aOp (E := E) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rfl
  · show bornProb (regroupVec ψ) _ _ = bornProb ψ _ _
    rw [POVM.aOp_mats, POVM.aOp_mats, POVM.aOp_mats, POVM.aOp_mats]
    exact bornProb_regroupVec ψ ((A x).mats a).val ((B x).mats b).val 1
end
end MIPRE.QLD

namespace MIPRE.QLD.SimulPair
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
open MIPRE.LIDT MIPRE.LowDegree
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
/-- **A Born probability of the strategy's own measurements reads the same on the padded state.**
Both operators are extended by the identity on the expansion's ancillas and on the padding, so the
padded state's reduction carries them to the expanded state and the expanded state's factorization
carries them down to the original one, the entangled pair contributing its own norm and nothing
else. -/
theorem bornProb_padded (X : Matrix dA dA ℂ) (Y : Matrix dB dB ℂ) :
    bornProb P.Φ (aOp (aOp X)) (aOp (aOp Y)) = bornProb ψ X Y := by
  rw [P.Φ_reduced (aOp X) (aOp Y)]
  show bornProb (expVec ψ (epr (F := F) (n := Fin m → Bool))) (X ⊗ₖ 1) (Y ⊗ₖ 1) = _
  rw [bornProb_expVec_kron ψ _ Matrix.PosSemidef.one Matrix.PosSemidef.one,
    bornProb_one_one epr_unit, mul_one]
end
end MIPRE.QLD.SimulPair

namespace MIPRE.QLD.SimulPair
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
open MIPRE.LIDT MIPRE.LowDegree
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
/-- **And so does a consistency between them.** This is what puts the game's own consistencies ---
which are statements about the strategy's measurements on the original state --- into the
vocabulary the appendix's interface reads them in. -/
theorem inconsistency_padded {Y Λ : Type*} [Fintype Y] [Fintype Λ] [DecidableEq Λ] (μ : Y → ℝ)
    (M : Y → POVM Λ dA) (N : Y → POVM Λ dB) :
    inconsistency μ P.Φ (fun y => ((M y).aOp (E := Anc F m)).aOp (E := P.EA))
        (fun y => ((N y).aOp (E := Anc F m)).aOp (E := P.EB))
      = inconsistency μ ψ M N := by
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rfl
  · show bornProb P.Φ _ _ = bornProb ψ _ _
    rw [POVM.aOp_mats, POVM.aOp_mats, POVM.aOp_mats, POVM.aOp_mats]
    exact P.bornProb_padded ((M y).mats a).val ((N y).mats b).val
end
end MIPRE.QLD.SimulPair

namespace MIPRE.QLD.SimulPair
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
open MIPRE.LIDT MIPRE.LowDegree
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
/-- **Display `eq:qld-unitary-5` at the interface.** The exact Pauli measurement agrees with the
strategy's `(Pauli, W)` measurement, read at the sampled point, to within eleven times whatever
bounds the three legs. Its own leg is item 1 of Lemma `lem:qld-exact-paulis`
(\texttt{inconsistency\_mTilde\_le}); the two middle legs are the game's own consistencies ---
point against point and point against Pauli --- and are hypotheses here, stated along the padded
state's own cut and carried across by \texttt{inconsistency\_regroupVec}. -/
theorem inconsistency_mTilde_pauli_le (W : Bas) {δ' : ℝ}
    (hpt : inconsistency (uniform (Point F m)) P.Φ
        (fun u => ((ptAtPOVM MA W u).aOp (E := Anc F m)).aOp (E := P.EA))
        (fun u => ((ptAtPOVM MB W u).aOp (E := Anc F m)).aOp (E := P.EB)) ≤ δ')
    (hpauli : inconsistency (uniform (Point F m)) P.Φ
        (fun u => ((ptAtPOVM MA W u).aOp (E := Anc F m)).aOp (E := P.EA))
        (fun u => ((pauliAtPOVM MB W u).aOp (E := Anc F m)).aOp (E := P.EB)) ≤ δ')
    (hmt : inconsistency (uniform (Point F m)) P.mVec
        (fun u => (P.isPVM_mTildeAt W u).toPOVM) (fun u => (ptAtPOVM MB W u).aOp) ≤ δ') :
    inconsistency (uniform (Point F m)) P.mVec
        (fun u => (P.isPVM_mTildeAt W u).toPOVM) (fun u => (pauliAtPOVM MB W u).aOp)
      ≤ 11 * δ' := by
  refine inconsistency_triangle (uniform_nonneg (Point F m)) (sum_uniform_eq_one (Point F m))
    P.mVec_unit _ (fun u => (((ptAtPOVM MA W u).aOp (E := Anc F m)).aOp (E := P.EA)).aOp
      (E := Anc F m)) _ _ hmt ?_ ?_
  · rw [SimulPair.mVec, inconsistency_regroupVec]
    exact hpt
  · rw [SimulPair.mVec, inconsistency_regroupVec]
    exact hpauli
end
end MIPRE.QLD.SimulPair

namespace MIPRE.QLD.SimulPair
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
open MIPRE.LIDT MIPRE.LowDegree
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
/-- **Display `eq:qld-unitary-5`, with its two middle legs read on the strategy's own state.**
This is the form the game supplies them in: `agree_subtest_le` bounds a cross-party deviation of
the strategy's measurements on `psi`, and nothing there knows about the expansion or the padding.
-/
theorem inconsistency_mTilde_pauli_le' (W : Bas) {δ' : ℝ}
    (hpt : inconsistency (uniform (Point F m)) ψ (fun u => ptAtPOVM MA W u)
      (fun u => ptAtPOVM MB W u) ≤ δ')
    (hpauli : inconsistency (uniform (Point F m)) ψ (fun u => ptAtPOVM MA W u)
      (fun u => pauliAtPOVM MB W u) ≤ δ')
    (hmt : inconsistency (uniform (Point F m)) P.mVec
        (fun u => (P.isPVM_mTildeAt W u).toPOVM) (fun u => (ptAtPOVM MB W u).aOp) ≤ δ') :
    inconsistency (uniform (Point F m)) P.mVec
        (fun u => (P.isPVM_mTildeAt W u).toPOVM) (fun u => (pauliAtPOVM MB W u).aOp)
      ≤ 11 * δ' :=
  P.inconsistency_mTilde_pauli_le W (by rw [P.inconsistency_padded]; exact hpt)
    (by rw [P.inconsistency_padded]; exact hpauli) hmt
end
end MIPRE.QLD.SimulPair

namespace MIPRE.QLD.SimulPair
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
open MIPRE.LIDT MIPRE.LowDegree
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
/-- **Display `eq:qld-unitary-5`, from the game's soundness and item 1 of
`lem:qld-exact-paulis` alone.** The two middle legs are now discharged: they are items 1 and 3 of
`lem:qld-win` at the point and Pauli types, and `86 = 172/2` is `agree_subtest_le`'s constant
halved by the passage from a cross-party deviation to an inconsistency. -/
theorem inconsistency_mTilde_pauli_le_of_win {hm : m ∣ Fintype.card F} {ε δ' : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (W : Bas) (hε : 86 * ε ≤ δ')
    (hmt : inconsistency (uniform (Point F m)) P.mVec
        (fun u => (P.isPVM_mTildeAt W u).toPOVM) (fun u => (ptAtPOVM MB W u).aOp) ≤ δ') :
    inconsistency (uniform (Point F m)) P.mVec
        (fun u => (P.isPVM_mTildeAt W u).toPOVM) (fun u => (pauliAtPOVM MB W u).aOp)
      ≤ 11 * δ' :=
  P.inconsistency_mTilde_pauli_le' W
    (le_trans (inconsistency_pt_pt_le hψ hfail hprojA hprojB W) hε)
    (le_trans (inconsistency_pt_pauli_le hψ hfail hprojA hprojB W) hε) hmt
end
end MIPRE.QLD.SimulPair

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE
open scoped Kronecker ComplexOrder MatrixOrder
variable {A B T1 T2 S1 S2 E E' : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype T1] [DecidableEq T1] [Fintype T2] [DecidableEq T2] [Fintype S1] [DecidableEq S1]
  [Fintype S2] [DecidableEq S2] [Fintype E] [DecidableEq E] [Fintype E'] [DecidableEq E']
omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype T1] [DecidableEq T1]
  [Fintype T2] [DecidableEq T2] [Fintype S1] [DecidableEq S1] [Fintype S2] [DecidableEq S2]
  [Fintype E] [DecidableEq E] [Fintype E'] [DecidableEq E'] in
/-- **The two readings meet on the physical grouping**, and they meet on the nose: pulling each
party's far half home from the mirrored cut lands on the very same vector as doing it from the
original one, with only the two parties written in the other order. This is why the mirror costs
nothing --- every statement proved on one cut is a statement about `pairSwapVec ψ` once it is
pushed to the physical grouping, whichever cut it came from. -/
theorem pairSwapVec_mirrorVec (ψ : (((A × T1) × E) × T2) × (((B × S1) × E') × S2) → ℂ) :
    pairSwapVec (mirrorVec ψ) = pairSwapVec ψ ∘ Prod.swap := rfl
end
end MIPRE.QLD

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
/-- **The second cut lands on the same physical state**, with only the two parties written in the
other order. This is `hmirror` pushed through `pairSwapVec_mirrorVec`, and it is what lets a
statement proved on one cut be combined with one proved on the other. -/
theorem physVec_mirror :
    pairSwapVec (expVec M.Φ' (epr (F := F) (n := Fin m → Bool))) = M.physVec ∘ Prod.swap := by
  rw [M.hmirror]
  exact pairSwapVec_mirrorVec _
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
/-- **The mirror reads the same physical state**, with only the two parties written in the other
order. This is `physVec_mirror` in the form the instantiations use: whatever is proved about
`physVec` holds for Bob by being proved about `M.mirror.physVec`. -/
theorem mirror_physVec : M.mirror.physVec = M.physVec ∘ Prod.swap := M.physVec_mirror
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
/-- **Alice's `(Pauli, W)` measurement read at `u`, against Bob's exact Pauli measurement, on the
physical state, is the same pair on the mirror's cut** --- where Bob's `M~` is the first party's
`mTildeAt` and Alice's reading is the second party's, which is the orientation
`eq:qld-unitary-5` is proved in. -/
theorem bornProb_physVec_pauli_bobMTilde (W : Bas) (u : Point F m) (a : F) :
    bornProb M.physVec (aOp (aOp (aOp (((pauliAtPOVM MA W u).mats a).val))))
        (M.bobMTilde W (indVec u) a)
      = bornProb M.toSecond.mVec (M.toSecond.mTildeAt W u a)
          (aOp (((pauliAtPOVM MA W u).mats a).val)) := by
  rw [← bornProb_swapVec]
  have h := M.mirror.bornProb_physVec (M.bobMTilde W (indVec u) a)
    (((pauliAtPOVM MA W u).mats a).val) 1
  rw [M.mirror_physVec] at h
  exact h
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
theorem _root_.solution {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (W : Bas) :
    1 - 11 * deltaLegs δ ε m d (Fintype.card F)
      ≤ ∑ u, uniform (Point F m) u * ∑ a : F, bornProb M.physVec
          (aOp (aOp (aOp (((pauliAtPOVM MA W u).mats a).val)))) (M.bobMTilde W (indVec u) a) := by
  have hψ' : star (ψ ∘ Prod.swap) ⬝ᵥ (ψ ∘ Prod.swap) = 1 := swapVec_unit hψ
  have hfail' : 1 - povmValue (qldGame hm) (ψ ∘ Prod.swap) MB MA ≤ ε :=
    povmValue_swapped_le hfail
  have hmt := M.toSecond.inconsistency_mTilde_le (hm := hm) hψ' hfail' hprojA hd W
  have hsq : 0 ≤ Real.sqrt (688 * ε) := Real.sqrt_nonneg _
  have hmd : (0 : ℝ) ≤ (m : ℝ) * d / Fintype.card F := by positivity
  have hle : δ + 2 * ((δ + Real.sqrt (688 * ε)) + (m : ℝ) * d / Fintype.card F)
      ≤ deltaLegs δ ε m d (Fintype.card F) := by
    rw [deltaLegs]
    linarith
  have h86 : 86 * ε ≤ deltaLegs δ ε m d (Fintype.card F) := by
    rw [deltaLegs]
    nlinarith
  have hinc := M.toSecond.inconsistency_mTilde_pauli_le_of_win (hm := hm) hψ' hfail' hprojB hprojA
    W h86 (le_trans hmt hle)
  have hdiag := sum_bornProb_diag_eq (sum_uniform_eq_one (Point F m)) M.toSecond.mVec_unit
    (fun u => (M.toSecond.isPVM_mTildeAt W u).toPOVM)
    (fun u => (pauliAtPOVM MA W u).aOp)
  simp only [IsPVM.toPOVM_mats, POVM.aOp_mats] at hdiag
  simp only [M.bornProb_physVec_pauli_bobMTilde]
  linarith
end MIPRE.QLD.MirrorSimul
