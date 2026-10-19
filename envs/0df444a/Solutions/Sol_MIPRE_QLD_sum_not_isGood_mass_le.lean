-- Prove2me | solution 1 for MIPRE.QLD.sum_not_isGood_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:47:54.114827+00:00
-- url     : https://prove2.me/submissions/b265dbff-c483-4997-9dff-5cc53362afaf

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Separate.lean (solution of MIPRE.QLD.sum_not_isGood_mass_le);
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
import Definitions.Def_MIPRE_Background_QLD_Linear
import Definitions.Def_MIPRE_Background_QLD_Separate
import Theorems.Thm_MIPRE_QLD_isGood_of
import Theorems.Thm_MIPRE_QLD_sum_bad_mass_le_of_avg
import Theorems.Thm_MIPRE_QLD_sum_uniform_bornProb_readOn_le
import Theorems.Thm_MIPRE_QLD_sum_uniform_snorm_sq_ordComb_XZ_le_of_isLinAB
import Theorems.Thm_MIPRE_QLD_sum_uniform_snorm_sq_ordComb_ZX_le_of_isLinAB
import Theorems.Thm_MIPRE_QLD_sum_uniform_snorm_sq_ordComb_le_of_not_isLinAB
import Theorems.Thm_MIPRE_bornProb_nonneg
import Theorems.Thm_MIPRE_posSemidef_of_proj

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]
omit [Field F] [Fintype F] [DecidableEq F] in
theorem zIdx_mem_zSet (i : Fin m) : zIdx m i ∈ zSet := Finset.mem_image_of_mem _ (mem_univ i)
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]
omit [Field F] [Fintype F] [DecidableEq F] in
theorem xIdx_mem_xSet (i : Fin m) : xIdx m i ∈ xSet := Finset.mem_image_of_mem _ (mem_univ i)
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]
omit [Field F] [Fintype F] [DecidableEq F] in
theorem zBlk_mixOn_zSet (u u' : Point F (4 * m)) : zBlk (mixOn zSet u u') = zBlk u' :=
  funext fun i => if_pos (zIdx_mem_zSet i)
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]
omit [Field F] [Fintype F] [DecidableEq F] in
theorem xBlk_mixOn_xSet (u u' : Point F (4 * m)) : xBlk (mixOn xSet u u') = xBlk u' :=
  funext fun i => if_pos (xIdx_mem_xSet i)
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
omit [Fintype F] [DecidableEq F] in
/-- An outcome that is not good is not linear, or is linear with a coefficient reading a
coordinate outside its block. -/
theorem not_isGood_cases (hd : 1 ≤ d) {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)}
    (hg : ¬ IsGood g) :
    ¬ IsLinAB g ∨ (IsLinAB g ∧ (gB hd g).DepOutside zSet)
      ∨ (IsLinAB g ∧ (gA hd g).DepOutside xSet) := by
  by_cases hlin : IsLinAB g
  · by_cases hB : (gB hd g).DepOutside zSet
    · exact Or.inr (Or.inl ⟨hlin, hB⟩)
    · by_cases hA : (gA hd g).DepOutside xSet
      · exact Or.inr (Or.inr ⟨hlin, hA⟩)
      · exact absurd (isGood_of hd hlin hA hB) hg
  · exact Or.inl hlin
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m] {RA RB : Type*}
  [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]
variable {X Z : Point F m → F → Matrix RB RB ℂ}
/-- **A linear outcome whose `β` coefficient reads a coordinate outside the `z` block**, against
the order `X_a Z_b`: `E_u ‖(S ⊗ B_u(g(u))) Φ‖² ≤ (2 + 8md)/q · ⟨S ⊗ 1⟩`. -/
theorem sum_uniform_snorm_sq_ordComb_XZ_le_of_depB (hd : 1 ≤ d) (Φ : RA × RB → ℂ)
    {S : Matrix RA RA ℂ} (hsa : Sᴴ = S) (hidem : S * S = S) (hX : ∀ x, IsPVM (X x))
    (hZ : ∀ z, IsPVM (Z z)) {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)}
    (hlin : IsLinAB g) (hB : (gB hd g).DepOutside zSet) :
    ∑ u, uniform (Point F (4 * m)) u
        * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (ordComb ordXZ X Z u (g.eval u))) ^ 2
      ≤ (2 + 8 * m * d) / Fintype.card F * bornProb Φ S 1 := by
  calc _ ≤ 2 / Fintype.card F * bornProb Φ S 1
        + ∑ u₀, uniform (Point F (4 * m)) u₀
          * bornProb Φ S (Z (zBlk u₀) ((gB hd g).eval u₀)) :=
        sum_uniform_snorm_sq_ordComb_XZ_le_of_isLinAB hd Φ hsa hidem hX hZ hlin
    _ ≤ 2 / Fintype.card F * bornProb Φ S 1 + 8 * m * d / Fintype.card F * bornProb Φ S 1 :=
        add_le_add le_rfl (sum_uniform_bornProb_readOn_le (Op := fun u => Z (zBlk u))
          (fun u u' => by rw [zBlk_mixOn_zSet]) (fun u => hZ _) hB Φ (posSemidef_of_proj hsa hidem))
    _ = (2 + 8 * m * d) / Fintype.card F * bornProb Φ S 1 := by ring
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m] {RA RB : Type*}
  [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]
variable {X Z : Point F m → F → Matrix RB RB ℂ}
/-- **A linear outcome whose `α` coefficient reads a coordinate outside the `x` block**, against
the order `Z_b X_a`. -/
theorem sum_uniform_snorm_sq_ordComb_ZX_le_of_depA (hd : 1 ≤ d) (Φ : RA × RB → ℂ)
    {S : Matrix RA RA ℂ} (hsa : Sᴴ = S) (hidem : S * S = S) (hX : ∀ x, IsPVM (X x))
    (hZ : ∀ z, IsPVM (Z z)) {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)}
    (hlin : IsLinAB g) (hA : (gA hd g).DepOutside xSet) :
    ∑ u, uniform (Point F (4 * m)) u
        * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (ordComb ordZX X Z u (g.eval u))) ^ 2
      ≤ (2 + 8 * m * d) / Fintype.card F * bornProb Φ S 1 := by
  calc _ ≤ 2 / Fintype.card F * bornProb Φ S 1
        + ∑ u₀, uniform (Point F (4 * m)) u₀
          * bornProb Φ S (X (xBlk u₀) ((gA hd g).eval u₀)) :=
        sum_uniform_snorm_sq_ordComb_ZX_le_of_isLinAB hd Φ hsa hidem hX hZ hlin
    _ ≤ 2 / Fintype.card F * bornProb Φ S 1 + 8 * m * d / Fintype.card F * bornProb Φ S 1 :=
        add_le_add le_rfl (sum_uniform_bornProb_readOn_le (Op := fun u => X (xBlk u))
          (fun u u' => by rw [xBlk_mixOn_xSet]) (fun u => hX _) hA Φ (posSemidef_of_proj hsa hidem))
    _ = (2 + 8 * m * d) / Fintype.card F * bornProb Φ S 1 := by ring
end
end MIPRE.QLD

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m] {RA RB : Type*}
  [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]
variable {X Z : Point F m → F → Matrix RB RB ℂ}
theorem _root_.solution (hd : 1 ≤ d) (Φ : RA × RB → ℂ)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix RA RA ℂ))
    (hX : ∀ x, IsPVM (X x)) (hZ : ∀ z, IsPVM (Z z)) {Δ₁ Δ₂ : ℝ}
    (hXZ : ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - ordComb ordXZ X Z u (g.eval u))) ^ 2
      ≤ Δ₁)
    (hZX : ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - ordComb ordZX X Z u (g.eval u))) ^ 2
      ≤ Δ₂) :
    (1 - 2 * ((2 + 2 * d + 8 * m * d) / Fintype.card F))
        * ∑ g ∈ univ.filter (fun g => ¬ IsGood g), bornProb Φ (G.M () g) 1
      ≤ 2 * Δ₁ + 2 * Δ₂ := by
  have hsa : ∀ g, (G.M () g)ᴴ = G.M () g := fun g => G.selfAdjoint () g
  have hidem : ∀ g, G.M () g * G.M () g = G.M () g := fun g => G.projective () g
  have hw0 : ∀ g, 0 ≤ bornProb Φ (G.M () g) 1 := fun g =>
    bornProb_nonneg Φ (posSemidef_of_proj (hsa g) (hidem g)) Matrix.PosSemidef.one
  have hq0 : (0 : ℝ) ≤ (Fintype.card F : ℝ)⁻¹ := by positivity
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hmd0 : (0 : ℝ) ≤ m * d := mul_nonneg hm0 hd0
  have hη₁ : (1 + 2 * d + 4 * m * d) / (Fintype.card F : ℝ)
      ≤ (2 + 2 * d + 8 * m * d) / Fintype.card F := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ hq0
    linarith
  have hη₂ : (2 + 8 * m * d) / (Fintype.card F : ℝ)
      ≤ (2 + 2 * d + 8 * m * d) / Fintype.card F := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ hq0
    linarith
  -- the two applications of the assembly
  have h₁ := sum_bad_mass_le_of_avg Φ G (ordComb ordXZ X Z)
    (fun g => ¬ IsLinAB g ∨ (IsLinAB g ∧ (gB hd g).DepOutside zSet))
    (η := (2 + 2 * d + 8 * m * d) / Fintype.card F) (fun g hg => by
      rcases hg with hg | ⟨hlin, hB⟩
      · exact (sum_uniform_snorm_sq_ordComb_le_of_not_isLinAB hd Φ (hsa g) (hidem g) hX hZ
          hg).trans (mul_le_mul_of_nonneg_right hη₁ (hw0 g))
      · exact (sum_uniform_snorm_sq_ordComb_XZ_le_of_depB hd Φ (hsa g) (hidem g) hX hZ hlin
          hB).trans (mul_le_mul_of_nonneg_right hη₂ (hw0 g))) hXZ
  have h₂ := sum_bad_mass_le_of_avg Φ G (ordComb ordZX X Z)
    (fun g => IsLinAB g ∧ (gA hd g).DepOutside xSet)
    (η := (2 + 2 * d + 8 * m * d) / Fintype.card F) (fun g hg =>
      (sum_uniform_snorm_sq_ordComb_ZX_le_of_depA hd Φ (hsa g) (hidem g) hX hZ hg.1
        hg.2).trans (mul_le_mul_of_nonneg_right hη₂ (hw0 g))) hZX
  -- the union bound
  have hsub : univ.filter (fun g : LowIndDegPoly (F := F) (m := 4 * m) (d := d) => ¬ IsGood g)
      ⊆ univ.filter (fun g => ¬ IsLinAB g ∨ (IsLinAB g ∧ (gB hd g).DepOutside zSet))
        ∪ univ.filter (fun g => IsLinAB g ∧ (gA hd g).DepOutside xSet) := by
    intro g hg
    rw [mem_filter] at hg
    rw [Finset.mem_union, mem_filter, mem_filter]
    rcases not_isGood_cases hd hg.2 with h | h | h
    · exact Or.inl ⟨mem_univ _, Or.inl h⟩
    · exact Or.inl ⟨mem_univ _, Or.inr h⟩
    · exact Or.inr ⟨mem_univ _, h⟩
  have hunion := Finset.sum_union_inter
    (s₁ := univ.filter (fun g : LowIndDegPoly (F := F) (m := 4 * m) (d := d) =>
      ¬ IsLinAB g ∨ (IsLinAB g ∧ (gB hd g).DepOutside zSet)))
    (s₂ := univ.filter (fun g => IsLinAB g ∧ (gA hd g).DepOutside xSet))
    (f := fun g => bornProb Φ (G.M () g) 1)
  have hinter := Finset.sum_nonneg (s := univ.filter (fun g : LowIndDegPoly (F := F) (m := 4 * m)
    (d := d) => ¬ IsLinAB g ∨ (IsLinAB g ∧ (gB hd g).DepOutside zSet))
      ∩ univ.filter (fun g => IsLinAB g ∧ (gA hd g).DepOutside xSet))
    fun g _ => hw0 g
  have hcover := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun g => bornProb Φ (G.M () g) 1) fun g _ _ => hw0 g
  have hΔ₁ : 0 ≤ Δ₁ := le_trans (Finset.sum_nonneg fun u _ => mul_nonneg (uniform_nonneg _ _)
    (Finset.sum_nonneg fun g _ => sq_nonneg _)) hXZ
  have hΔ₂ : 0 ≤ Δ₂ := le_trans (Finset.sum_nonneg fun u _ => mul_nonneg (uniform_nonneg _ _)
    (Finset.sum_nonneg fun g _ => sq_nonneg _)) hZX
  by_cases hc : 0 ≤ 1 - 2 * ((2 + 2 * d + 8 * m * d) / (Fintype.card F : ℝ))
  · have hW : ∑ g ∈ univ.filter (fun g => ¬ IsGood g), bornProb Φ (G.M () g) 1
        ≤ ∑ g ∈ univ.filter (fun g => ¬ IsLinAB g ∨ (IsLinAB g ∧ (gB hd g).DepOutside zSet)),
            bornProb Φ (G.M () g) 1
          + ∑ g ∈ univ.filter (fun g => IsLinAB g ∧ (gA hd g).DepOutside xSet),
            bornProb Φ (G.M () g) 1 := by linarith
    calc _ ≤ (1 - 2 * ((2 + 2 * d + 8 * m * d) / Fintype.card F))
          * (∑ g ∈ univ.filter (fun g => ¬ IsLinAB g ∨ (IsLinAB g ∧ (gB hd g).DepOutside zSet)),
              bornProb Φ (G.M () g) 1
            + ∑ g ∈ univ.filter (fun g => IsLinAB g ∧ (gA hd g).DepOutside xSet),
              bornProb Φ (G.M () g) 1) := mul_le_mul_of_nonneg_left hW hc
      _ ≤ 2 * Δ₁ + 2 * Δ₂ := by rw [mul_add]; exact add_le_add h₁ h₂
  · push Not at hc
    have hsum : 0 ≤ ∑ g ∈ univ.filter (fun g => ¬ IsGood g), bornProb Φ (G.M () g) 1 :=
      Finset.sum_nonneg fun g _ => hw0 g
    have hprod0 := mul_nonneg (neg_nonneg.mpr hc.le) hsum
    linarith
end MIPRE.QLD
