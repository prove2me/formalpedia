-- Prove2me | solution 1 for MIPRE.QLD.MirrorSimul.sum_uniform_snorm_sq_chainT_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:32:13.50502+00:00
-- url     : https://prove2.me/submissions/5ec14758-73a0-4183-9b27-d0bfd2943037

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/ChainAssembly.lean (solution of MIPRE.QLD.MirrorSimul.sum_uniform_snorm_sq_chainT_le);
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
import Theorems.Thm_MIPRE_QLD_MirrorSimul_chainT_eight_sub_nine
import Theorems.Thm_MIPRE_QLD_MirrorSimul_chainT_eight_sub_seven
import Theorems.Thm_MIPRE_QLD_MirrorSimul_chainT_five_eq_six
import Theorems.Thm_MIPRE_QLD_MirrorSimul_chainT_five_sub_four
import Theorems.Thm_MIPRE_QLD_MirrorSimul_physLift_chainU3b_mulVec
import Theorems.Thm_MIPRE_QLD_MirrorSimul_sum_snorm_sq_chainP_le
import Theorems.Thm_MIPRE_QLD_MirrorSimul_sum_snorm_sq_chainQ_agree_le
import Theorems.Thm_MIPRE_QLD_MirrorSimul_sum_uniform_snorm_sq_chainQ_notCoupled_le
import Theorems.Thm_MIPRE_QLD_MirrorSimul_sum_uniform_snorm_sq_chainT_six_seven
import Theorems.Thm_MIPRE_QLD_SimulPair_aOp_mTildeAnc_mul_nearId
import Theorems.Thm_MIPRE_QLD_SimulPair_chainS_three_mulVec
import Theorems.Thm_MIPRE_QLD_SimulPair_sum_snorm_sq_insert_chain
import Theorems.Thm_MIPRE_QLD_SimulPair_sum_snorm_sq_polyMarg_one_sub_le
import Theorems.Thm_MIPRE_QLD_SimulPair_sum_uniform_snorm_sq_nearId_le
import Theorems.Thm_MIPRE_QLD_SimulPair_sum_uniform_xSqNorm_pt_le
import Theorems.Thm_MIPRE_QLD_kron_mulVec_one
import Theorems.Thm_MIPRE_QLD_povmValue_swapped_le
import Theorems.Thm_MIPRE_QLD_qform_kron_one_of_unit
import Theorems.Thm_MIPRE_QLD_sum_snorm_sq_chain_le
import Theorems.Thm_MIPRE_QLD_swapVec_unit
import Theorems.Thm_MIPRE_Weyl_epr_unit

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
/-- **The squared state norm is the quadratic form of `M† M`.** -/
theorem snorm_sq_eq_qform (M : Matrix N N ℂ) : snorm v M ^ 2 = qform v (Mᴴ * M) := by
  rw [snorm, norm_evec_mulVec_sq, qform]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB] in
/-- A difference in the left factor of a Kronecker product splits off. -/
theorem sub_kronecker_right (N P : Matrix dA dA ℂ) (R : Matrix dB dB ℂ) :
    (N - P) ⊗ₖ R = N ⊗ₖ R - P ⊗ₖ R := by
  ext p q
  simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply]
  ring
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
open Matrix
open scoped ComplexOrder MatrixOrder
theorem uniform_nonneg (X : Type*) [Fintype X] (x : X) : 0 ≤ uniform X x :=
  inv_nonneg.mpr (Nat.cast_nonneg _)
end
end MIPRE

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

namespace MIPRE.QLD.SimulPair
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
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
/-- **Displays `eq:qld-pulling-2` and `-2b` say the second and third terms are one.** -/
theorem chainS_one_eq_two (W : Bas) (v : Anc F m) (u : Point F m) :
    P.chainS W v u 1 = P.chainS W v u 2 := by
  funext a
  show (aOp (P.mTildeAnc W v a) : Matrix _ _ ℂ) * P.nearId W u
    = ∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
      (aOp (P.chainOp W p) : Matrix _ _ ℂ) * bOp (P.ptB W u (chainShift u p))
  rw [P.aOp_mTildeAnc_mul_nearId W v u a]
  exact Finset.sum_congr rfl fun p _ => (aOp_mul_bOp_eq _ _).symm
end
end MIPRE.QLD.SimulPair

namespace MIPRE.QLD.SimulPair
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
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
/-- **And the third and fourth differ by what `eq:qld-pulling-3` bounds.** -/
theorem chainS_two_sub_three (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    P.chainS W v u 2 a - P.chainS W v u 3 a
      = ∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
        (aOp (P.chainOp W p) : Matrix _ _ ℂ)
          * (((1 : Matrix ((((dA × Anc F m) × P.EA) × Anc F m) × (dB × P.EB)) _ ℂ)
              - aOp (P.ptA W u (chainShift u p))) * bOp (P.ptB W u (chainShift u p))) := by
  show (∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
      (aOp (P.chainOp W p) : Matrix _ _ ℂ) * bOp (P.ptB W u (chainShift u p)))
    - (∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
      (aOp (P.chainOp W p) : Matrix _ _ ℂ)
        * (aOp (P.ptA W u (chainShift u p)) * bOp (P.ptB W u (chainShift u p)))) = _
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub]
end
end MIPRE.QLD.SimulPair

namespace MIPRE.QLD.SimulPair
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
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
/-- **Step 0 to 1 is `eq:qld-pulling-1`**, at item 1 of `lem:qld-helper`'s own constant. -/
theorem sum_uniform_snorm_sq_chainS_zero_one
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm P.mVec (P.chainS W v u 0 a - P.chainS W v u 1 a) ^ 2) ≤ δ :=
  P.sum_uniform_snorm_sq_nearId_le hprojB W v
end
end MIPRE.QLD.SimulPair

namespace MIPRE.QLD.SimulPair
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
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
/-- **Step 1 to 2 is free**, being displays `eq:qld-pulling-2` and `-2b`, which are identities. -/
theorem sum_snorm_sq_chainS_one_two (W : Bas) (v : Anc F m) (u : Point F m) :
    (∑ a : F, snorm P.mVec (P.chainS W v u 1 a - P.chainS W v u 2 a) ^ 2) = 0 := by
  rw [P.chainS_one_eq_two W v u]
  have hz : snorm P.mVec 0 = 0 := by
    rw [snorm, Matrix.zero_mulVec]
    simp [evec]
  simp [hz]
end
end MIPRE.QLD.SimulPair

namespace MIPRE.QLD.SimulPair
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
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
/-- **Step 2 to 3 is `eq:qld-pulling-3`**, the insertion. -/
theorem sum_snorm_sq_chainS_two_three {ε : ℝ} (W : Bas) (v : Anc F m) (u : Point F m)
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
    (hcons : ∑ k : F, xSqNorm P.mVec (P.ptA W u k) (P.ptB W u k) ≤ ε) :
    (∑ a : F, snorm P.mVec (P.chainS W v u 2 a - P.chainS W v u 3 a) ^ 2) ≤ ε := by
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => by rw [P.chainS_two_sub_three W v u a]]
  exact P.sum_snorm_sq_insert_chain W v u hprojB hcons
end
end MIPRE.QLD.SimulPair

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
set_option maxHeartbeats 1000000 in
/-- **Display `eq:qld-pulling-9`**: the chain's step from `eq:qld-pulling-5` to
`eq:qld-pulling-7` costs item 2 of `lem:qld-helper` and nothing more. -/
theorem sum_uniform_snorm_sq_chainP_le {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (W : Bas) (v : Anc F m) :
    ∑ u, uniform (Point F m) u * ∑ a : F, snorm M.physVec
        (∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m
            => dotF (chainLabel t.1.1 t.1.2) v = a,
          M.chainP W t * M.chainW W u t) ^ 2
      ≤ 4 * δ + 2 * (172 * ε) := by
  refine le_trans (Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (M.sum_snorm_sq_chainP_le hprojB W v u)
      (uniform_nonneg (Point F m) u)) ?_
  exact M.toFirst.sum_snorm_sq_polyMarg_one_sub_le (hm := hm) hψ hfail hprojB W
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
set_option maxHeartbeats 1000000 in
/-- **And its cost**, which is item 2 of `lem:qld-helper` at the second cut --- available, with no
new proof, because the mirror of a `MirrorSimul` is a `MirrorSimul`. -/
theorem sum_uniform_snorm_sq_chainQ_agree_le {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val)) (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u * ∑ a : F, snorm M.physVec
        (∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
              × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
              chainQShift u q = q.2.1.eval u).filter
            fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
          M.chainQ W q
            * M.bobLift (1 - (aOp (hatMats MB W u (q.2.1.eval u))
                : Matrix ((dB × Anc F m) × M.Eb) _ ℂ))) ^ 2)
      ≤ 4 * δ + 2 * (172 * ε) := by
  refine le_trans (Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (M.sum_snorm_sq_chainQ_agree_le W v u)
      (uniform_nonneg (Point F m) u)) ?_
  exact M.toSecond.sum_snorm_sq_polyMarg_one_sub_le (hm := hm) (swapVec_unit hψ)
    (povmValue_swapped_le hfail) hprojA W
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
/-- **The physical state, read through that regrouping, is the first cut's with the pair beside
it.** -/
theorem physVec_comp_physLiftEquiv :
    M.physVec ∘ M.physLiftEquiv
      = fun p => M.toFirst.mVec p.1 * epr (F := F) (n := Fin m → Bool) p.2 := rfl
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
theorem physLift_sub (U V : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb))
    ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb)) ℂ) :
    M.physLift (U - V) = M.physLift U - M.physLift V := by
  rw [physLift, physLift, physLift, sub_kronecker_right]
  ext p q
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]
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
theorem physLift_mul (U V : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb))
    ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb)) ℂ) :
    M.physLift (U * V) = M.physLift U * M.physLift V := by
  rw [physLift, physLift, physLift,
    show (U * V) ⊗ₖ (1 : Matrix (Anc F m × Anc F m) (Anc F m × Anc F m) ℂ)
      = (U ⊗ₖ (1 : Matrix (Anc F m × Anc F m) (Anc F m × Anc F m) ℂ))
        * (V ⊗ₖ (1 : Matrix (Anc F m × Anc F m) (Anc F m × Anc F m) ℂ)) from by
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_one],
    Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply]
  exact (Matrix.submatrix_mul_equiv _ _ _ _ _).symm
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
theorem physLift_conjTranspose (U : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb))
    ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb)) ℂ) :
    (M.physLift U)ᴴ = M.physLift Uᴴ := by
  rw [physLift, physLift, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
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
/-- **The transport**: a first-cut operator, lifted, has the same quadratic form on the physical
state that it has on the first cut's own. The appended pair contributes its norm and nothing
else. -/
theorem qform_physLift (U : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb))
    ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb)) ℂ) :
    qform M.physVec (M.physLift U) = qform M.toFirst.mVec U := by
  have h := qform_comp_equiv M.physLiftEquiv (M.physVec ∘ M.physLiftEquiv)
    (U ⊗ₖ (1 : Matrix (Anc F m × Anc F m) (Anc F m × Anc F m) ℂ))
  rw [show (M.physVec ∘ M.physLiftEquiv) ∘ M.physLiftEquiv.symm = M.physVec from by
    rw [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]] at h
  have h2 : qform M.physVec (M.physLift U)
      = qform (M.physVec ∘ M.physLiftEquiv)
        (U ⊗ₖ (1 : Matrix (Anc F m × Anc F m) (Anc F m × Anc F m) ℂ)) :=
    congrArg Complex.re h
  rw [h2, M.physVec_comp_physLiftEquiv]
  exact qform_kron_one_of_unit (epr_unit (F := F) (n := Fin m → Bool)) M.toFirst.mVec U
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
/-- And the same for a state-norm, a state-norm being the square root of a quadratic form. -/
theorem snorm_physLift (U : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb))
    ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb)) ℂ) :
    snorm M.physVec (M.physLift U) = snorm M.toFirst.mVec U := by
  have hsq : snorm M.physVec (M.physLift U) ^ 2 = snorm M.toFirst.mVec U ^ 2 := by
    rw [snorm_sq_eq_qform M.physVec (M.physLift U), M.physLift_conjTranspose,
      ← M.physLift_mul, M.qform_physLift]
    exact (snorm_sq_eq_qform M.toFirst.mVec U).symm
  nlinarith [snorm_nonneg M.physVec (M.physLift U), snorm_nonneg M.toFirst.mVec U]
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
/-- **The lift's action on the state**: the first cut's vector, acted on, beside the appended
pair. -/
theorem physLift_mulVec (U : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb))
    ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb)) ℂ) :
    M.physLift U *ᵥ M.physVec
      = (fun p => (U *ᵥ M.toFirst.mVec) p.1 * (epr (F := F) (n := Fin m → Bool)) p.2)
        ∘ M.physLiftEquiv.symm := by
  have hcomp : (M.physVec ∘ M.physLiftEquiv) ∘ M.physLiftEquiv.symm = M.physVec := by
    rw [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  rw [physLift, Matrix.reindex_apply]
  conv_lhs => rw [← hcomp]
  rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, hcomp, M.physVec_comp_physLiftEquiv]
  exact congrArg (· ∘ ⇑M.physLiftEquiv.symm)
    (kron_mulVec_one M.toFirst.mVec (epr (F := F) (n := Fin m → Bool)) U)
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
/-- **So an identity on the first cut's state lifts to one on the physical state.** -/
theorem physLift_mulVec_congr {U V : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb))
    ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb)) ℂ}
    (h : U *ᵥ M.toFirst.mVec = V *ᵥ M.toFirst.mVec) :
    M.physLift U *ᵥ M.physVec = M.physLift V *ᵥ M.physVec := by
  rw [M.physLift_mulVec U, M.physLift_mulVec V, h]
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
/-- It is the first cut's own `-3b` term. -/
theorem chainU3b_eq (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    M.chainU3b W v u a = M.toFirst.chainS3b W v u a := rfl
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
omit [Algebra (ZMod 2) F] [NeZero m] in
/-- A deviation that vanishes on the state has no state-norm. -/
theorem snorm_sub_eq_zero_of_mulVec {N : Type*} [Fintype N] [DecidableEq N] (w : N → ℂ)
    {X Y : Matrix N N ℂ} (h : X *ᵥ w = Y *ᵥ w) : snorm w (X - Y) = 0 := by
  rw [snorm, Matrix.sub_mulVec, h, sub_self]
  simp [evec]
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
/-- The lift preserves a deviation's state-norm, being a `*`-homomorphism. -/
theorem snorm_physLift_sub (U V : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb))
    ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb)) ℂ) :
    snorm M.physVec (M.physLift U - M.physLift V) = snorm M.toFirst.mVec (U - V) := by
  rw [← M.physLift_sub, M.snorm_physLift]
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
/-- **Step 0 to 1 is `eq:qld-pulling-1`**, at item 1 of `lem:qld-helper`'s own constant. -/
theorem sum_uniform_snorm_sq_chainT_zero_one
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm M.physVec (M.chainT W v u 0 a - M.chainT W v u 1 a) ^ 2) ≤ δ := by
  refine le_trans (le_of_eq ?_) (M.toFirst.sum_uniform_snorm_sq_chainS_zero_one hprojB W v)
  exact Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun a _ =>
    congrArg (· ^ 2) (M.snorm_physLift_sub _ _))
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
/-- **Step 1 to 2 is free**, being displays `eq:qld-pulling-2` and `-2b`. -/
theorem sum_snorm_sq_chainT_one_two (W : Bas) (v : Anc F m) (u : Point F m) :
    (∑ a : F, snorm M.physVec (M.chainT W v u 1 a - M.chainT W v u 2 a) ^ 2) = 0 := by
  refine Eq.trans (Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
    congrArg (· ^ 2) (M.snorm_physLift_sub (M.toFirst.chainS W v u 1 a)
      (M.toFirst.chainS W v u 2 a))) ?_
  exact M.toFirst.sum_snorm_sq_chainS_one_two W v u
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
/-- **Step 2 to 3 is `eq:qld-pulling-3`**, the insertion, at the game's point--point
consistency. -/
theorem sum_uniform_snorm_sq_chainT_two_three {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm M.physVec (M.chainT W v u 2 a - M.chainT W v u 3 a) ^ 2)
      ≤ 2 * (86 * ε) := by
  have hstep : ∀ u : Point F m,
      (∑ a : F, snorm M.physVec (M.chainT W v u 2 a - M.chainT W v u 3 a) ^ 2)
        ≤ ∑ k : F, xSqNorm M.toFirst.mVec (M.toFirst.ptA W u k) (M.toFirst.ptB W u k) := by
    intro u
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      congrArg (· ^ 2) (M.snorm_physLift_sub _ _))) ?_
    exact M.toFirst.sum_snorm_sq_chainS_two_three W v u hprojB (le_refl _)
  refine le_trans (Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (hstep u) (uniform_nonneg (Point F m) u)) ?_
  exact M.toFirst.sum_uniform_xSqNorm_pt_le (hm := hm) hψ hfail hprojA hprojB W
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
/-- **Step 3 to 4 is free**, being displays `eq:qld-pulling-3a`, `-3b`, `-4` and `-5`. -/
theorem snorm_chainT_three_four (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    snorm M.physVec (M.chainT W v u 3 a - M.chainT W v u 4 a) = 0 := by
  refine snorm_sub_eq_zero_of_mulVec _ ?_
  have h1 : M.physLift (M.toFirst.chainS W v u 3 a) *ᵥ M.physVec
      = M.physLift (M.chainU3b W v u a) *ᵥ M.physVec :=
    M.physLift_mulVec_congr (by
      rw [M.chainU3b_eq]
      exact M.toFirst.chainS_three_mulVec W v u a)
  exact h1.trans (M.physLift_chainU3b_mulVec W v u a)
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
/-- **And its cost is display `eq:qld-pulling-9`**, item 2 of `lem:qld-helper`. -/
theorem sum_uniform_snorm_sq_chainT_four_five {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm M.physVec (M.chainT W v u 4 a - M.chainT W v u 5 a) ^ 2)
      ≤ 4 * δ + 2 * (172 * ε) := by
  refine le_trans (le_of_eq ?_)
    (M.sum_uniform_snorm_sq_chainP_le (hm := hm) hψ hfail hprojB W v)
  refine Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [← snorm_sub_comm, M.chainT_five_sub_four W v u a]
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
/-- **And its cost**, which is item 2 of `lem:qld-helper` at the second cut. -/
theorem sum_uniform_snorm_sq_chainT_seven_eight {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val)) (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm M.physVec (M.chainT W v u 7 a - M.chainT W v u 8 a) ^ 2)
      ≤ 4 * δ + 2 * (172 * ε) := by
  refine le_trans (le_of_eq ?_)
    (M.sum_uniform_snorm_sq_chainQ_agree_le (hm := hm) hψ hfail hprojA W v)
  refine Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [← snorm_sub_comm, M.chainT_eight_sub_seven W v u a]
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
/-- **And its cost is `md/q`**, by Schwartz--Zippel. -/
theorem sum_uniform_snorm_sq_chainT_eight_nine (hd : 1 ≤ d) (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm M.physVec (M.chainT W v u 8 a - M.chainT W v u 9 a) ^ 2)
      ≤ (m : ℝ) * d / Fintype.card F := by
  refine le_trans (le_of_eq ?_) (M.sum_uniform_snorm_sq_chainQ_notCoupled_le hd W v)
  refine Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [M.chainT_eight_sub_nine W v u a]
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
theorem sum_uniform_snorm_sq_chainT_one_two (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm M.physVec (M.chainT W v u 1 a - M.chainT W v u 2 a) ^ 2) = 0 :=
  Finset.sum_eq_zero fun u _ => by rw [M.sum_snorm_sq_chainT_one_two W v u, mul_zero]
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
theorem sum_uniform_snorm_sq_chainT_three_four (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm M.physVec (M.chainT W v u 3 a - M.chainT W v u 4 a) ^ 2) = 0 :=
  Finset.sum_eq_zero fun u _ => by
    rw [Finset.sum_eq_zero fun a (_ : a ∈ univ) => by
      rw [M.snorm_chainT_three_four W v u a]
      norm_num, mul_zero]
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
theorem sum_uniform_snorm_sq_chainT_five_six (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm M.physVec (M.chainT W v u 5 a - M.chainT W v u 6 a) ^ 2) = 0 :=
  Finset.sum_eq_zero fun u _ => by
    rw [Finset.sum_eq_zero fun a (_ : a ∈ univ) => by
      rw [M.chainT_five_eq_six W v u a, sub_self, snorm, Matrix.zero_mulVec]
      simp [evec], mul_zero]
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
omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- Averaging a constant multiple of a chain's steps: the average goes inside. -/
theorem sum_mul_const_mul_sum_range {X : Type*} [Fintype X] (μ : X → ℝ) (n : ℕ)
    (f : ℕ → X → ℝ) (c : ℝ) :
    (∑ x, μ x * (c * ∑ k ∈ Finset.range n, f k x))
      = c * ∑ k ∈ Finset.range n, ∑ x, μ x * f k x :=
  calc (∑ x, μ x * (c * ∑ k ∈ Finset.range n, f k x))
      = ∑ x, ∑ k ∈ Finset.range n, c * (μ x * f k x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ k ∈ Finset.range n, ∑ x, c * (μ x * f k x) := Finset.sum_comm
    _ = c * ∑ k ∈ Finset.range n, ∑ x, μ x * f k x := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
end
end MIPRE.QLD

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
theorem _root_.solution {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm M.physVec (M.chainT W v u 0 a - M.chainT W v u 9 a) ^ 2)
      ≤ 9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F) := by
  classical
  refine le_trans (Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (sum_snorm_sq_chain_le M.physVec 9 (M.chainT W v u))
      (uniform_nonneg (Point F m) u)) ?_
  rw [sum_mul_const_mul_sum_range (uniform (Point F m)) 9
    (fun k u => ∑ a : F, snorm M.physVec (M.chainT W v u k a - M.chainT W v u (k + 1) a) ^ 2)
    ((9 : ℕ) : ℝ)]
  have b0 := M.sum_uniform_snorm_sq_chainT_zero_one hprojB W v
  have b1 := M.sum_uniform_snorm_sq_chainT_one_two W v
  have b2 := M.sum_uniform_snorm_sq_chainT_two_three (hm := hm) hψ hfail hprojA hprojB W v
  have b3 := M.sum_uniform_snorm_sq_chainT_three_four W v
  have b4 := M.sum_uniform_snorm_sq_chainT_four_five (hm := hm) hψ hfail hprojB W v
  have b5 := M.sum_uniform_snorm_sq_chainT_five_six W v
  have b6 := M.sum_uniform_snorm_sq_chainT_six_seven (hm := hm) hψ hfail hprojA hprojB W v
  have b7 := M.sum_uniform_snorm_sq_chainT_seven_eight (hm := hm) hψ hfail hprojA W v
  have b8 := M.sum_uniform_snorm_sq_chainT_eight_nine hd W v
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  push_cast
  linarith
end MIPRE.QLD.MirrorSimul
