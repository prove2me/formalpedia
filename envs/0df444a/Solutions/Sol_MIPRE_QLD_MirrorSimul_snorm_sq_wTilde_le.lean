-- Prove2me | solution 1 for MIPRE.QLD.MirrorSimul.snorm_sq_wTilde_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:36:12.898828+00:00
-- url     : https://prove2.me/submissions/d7cd4e1f-6db5-4eac-b4bb-f0d0afe3bbcc

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/SelfCons.lean (solution of MIPRE.QLD.MirrorSimul.snorm_sq_wTilde_le);
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
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_QLD_MirrorSimul_sum_uniform_snorm_sq_chainT_le
import Theorems.Thm_MIPRE_QLD_povmValue_swapped_le
import Theorems.Thm_MIPRE_QLD_snorm_sq_obs_sub_le
import Theorems.Thm_MIPRE_QLD_swapVec_unit
import Theorems.Thm_MIPRE_Weyl_epr_unit
import Theorems.Thm_MIPRE_aOp_smul
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_one_sub_sum_bornProb_eq
import Theorems.Thm_MIPRE_sum_bornProb_le_map
import Theorems.Thm_MIPRE_sum_uniform_eq_one

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
theorem snorm_sub_comm (M M' : Matrix N N ℂ) : snorm v (M - M') = snorm v (M' - M) := by
  rw [snorm, snorm, Matrix.sub_mulVec, Matrix.sub_mulVec, evec_sub, evec_sub, norm_sub_rev]
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
/-- `sgn` takes values `±1`, hence modulus one. -/
theorem norm_sgn (x : ZMod 2) : ‖sgn x‖ = 1 := by
  rw [sgn]; split_ifs <;> norm_num
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
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
omit [DecidableEq dA] [DecidableEq dB] in
theorem mulVec_kronecker_swapVec (X : Matrix dB dB ℂ) (Y : Matrix dA dA ℂ)
    (ψ : dA × dB → ℂ) :
    (X ⊗ₖ Y) *ᵥ swapVec ψ = swapVec ((Y ⊗ₖ X) *ᵥ ψ) := by
  classical
  funext p
  obtain ⟨j, i⟩ := p
  show ∑ q : dB × dA, (X ⊗ₖ Y) (j, i) q * swapVec ψ q
      = ∑ q : dA × dB, (Y ⊗ₖ X) (i, j) q * ψ q
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
  show X j j' * Y i i' * ψ (i', j') = Y i i' * X j j' * ψ (i', j')
  ring
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
omit [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB] in
theorem swapVec_sub (u v : dA × dB → ℂ) :
    swapVec (u - v) = swapVec u - swapVec v := rfl
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
omit [DecidableEq dA] [DecidableEq dB] in
theorem norm_swapVec (v : dA × dB → ℂ) : ‖evec (swapVec v)‖ = ‖evec v‖ := by
  classical
  rw [evec, evec, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact Fintype.sum_equiv (Equiv.prodComm dB dA) _ _ fun _ => rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
/-- The triangle inequality for a family of deviations, at the usual cost of a factor two. -/
theorem sum_snorm_sq_triangle' {ι : Type*} [Fintype ι] (v : N → ℂ)
    (P Q R : ι → Matrix N N ℂ) :
    ∑ i, snorm v (P i - R i) ^ 2
      ≤ 2 * ∑ i, snorm v (P i - Q i) ^ 2 + 2 * ∑ i, snorm v (Q i - R i) ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hsplit : P i - R i = (P i - Q i) + (Q i - R i) := by abel
  have htri : snorm v (P i - R i) ≤ snorm v (P i - Q i) + snorm v (Q i - R i) := by
    rw [hsplit]; exact snorm_add_le v _ _
  nlinarith [snorm_nonneg v (P i - Q i), snorm_nonneg v (Q i - R i),
    snorm_nonneg v (P i - R i), sq_nonneg (snorm v (P i - Q i) - snorm v (Q i - R i))]
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
/-- The expanded state's norm splits, so it is a unit vector when both factors are. -/
theorem expVec_dotProduct (ψ : dA × dB → ℂ) (e : anc × anc' → ℂ) :
    star (expVec ψ e) ⬝ᵥ expVec ψ e = (star ψ ⬝ᵥ ψ) * (star e ⬝ᵥ e) := by
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
theorem expVec_unit {ψ : dA × dB → ℂ} {e : anc × anc' → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (he : star e ⬝ᵥ e = 1) : star (expVec ψ e) ⬝ᵥ expVec ψ e = 1 := by
  rw [expVec_dotProduct, hψ, he, mul_one]
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

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem norm_evec_eq_one_of_unit {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) : ‖evec ψ‖ = 1 := by
  have h : ‖evec ψ‖ ^ 2 = 1 := by rw [norm_evec_sq, hψ, Complex.one_re]
  nlinarith [norm_nonneg (evec ψ), h]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {A C : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **Coarse-graining two projective measurements the same way costs nothing.** The
state-dependent distance has no data-processing inequality, and a per-fibre triangle inequality
would cost the fibre size; what makes this free is that for *projective* families the summed
deviation and the agreement probability determine each other exactly
(`one_sub_sum_bornProb_eq`), and agreement can only increase under a coarse-graining. -/
theorem sum_xSqNorm_map_le {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (Q : POVM A dA) (Q' : POVM A dB)
    (hQ : IsPVM fun a => ((Q.mats a).val)) (hQ' : IsPVM fun a => ((Q'.mats a).val))
    (f : A → C) :
    ∑ v : C, xSqNorm ψ (((Q.map f).mats v).val) (((Q'.map f).mats v).val)
      ≤ ∑ a : A, xSqNorm ψ ((Q.mats a).val) ((Q'.mats a).val) := by
  have hψ' : ‖evec ψ‖ = 1 := norm_evec_eq_one_of_unit hψ
  have e1 := one_sub_sum_bornProb_eq (dA := dA) (dB := dB) (A := C) hψ'
    (isPVM_povm_map Q hQ f) (isPVM_povm_map Q' hQ' f)
  have e2 := one_sub_sum_bornProb_eq (dA := dA) (dB := dB) (A := A) hψ' hQ hQ'
  have e3 := sum_bornProb_le_map ψ Q Q' f
  linarith
end
end MIPRE

namespace MIPRE.LIDT
noncomputable section
open Finset MvPolynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ}
omit [Fintype F] [DecidableEq F] in
theorem LowIndDegPoly.eval_toMv (g : LowIndDegPoly (F := F) (m := n) (d := d)) (u : Point F n) :
    MvPolynomial.eval u g.toMv = g.eval u := by
  simp only [LowIndDegPoly.toMv, map_sum, MvPolynomial.eval_monomial, LowIndDegPoly.eval]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finsupp.prod_fintype _ _ fun i => pow_zero _]
  rfl
end
end MIPRE.LIDT

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {Λ Λ' : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']
/-- **Coarse-graining a cross-party consistency costs nothing.** Two projective measurements
relabelled the same way stay as close as they were --- with no factor for the size of a fibre,
which a per-fibre triangle inequality would have cost. -/
theorem sum_xSqNorm_fibre_le {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    {A : Λ → Matrix dA dA ℂ} {B : Λ → Matrix dB dB ℂ} (hA : IsPVM A) (hB : IsPVM B)
    (f : Λ → Λ') :
    ∑ c, xSqNorm ψ (∑ a ∈ univ.filter fun a => f a = c, A a)
        (∑ a ∈ univ.filter fun a => f a = c, B a)
      ≤ ∑ a, xSqNorm ψ (A a) (B a) := by
  have h := sum_xSqNorm_map_le hψ hA.toPOVM hB.toPOVM hA hB f
  simpa only [POVM.map_mats, IsPVM.toPOVM_mats] using h
end
end MIPRE

namespace MIPRE.QLD.SimulPair
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
/-- It is a projective measurement, at every probe. -/
theorem isPVM_mTildeAnc (W : Bas) (v : Anc F m) : IsPVM (P.mTildeAnc W v) :=
  isPVM_mTilde P.SA_proj (PolyPair.proj W) cubeData (isWeylFamily_weylOf W) v
end
end MIPRE.QLD.SimulPair

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE
open scoped Kronecker ComplexOrder MatrixOrder
variable {A B T1 T2 S1 S2 E E' : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype T1] [DecidableEq T1] [Fintype T2] [DecidableEq T2] [Fintype S1] [DecidableEq S1]
  [Fintype S2] [DecidableEq S2] [Fintype E] [DecidableEq E] [Fintype E'] [DecidableEq E']
omit [DecidableEq A] [DecidableEq B] [DecidableEq T1] [DecidableEq T2] [DecidableEq S1]
  [DecidableEq S2] [DecidableEq E] [DecidableEq E'] in
/-- A regrouped unit vector is a unit vector. -/
theorem pairSwapVec_unit
    {ψ : (((A × T1) × E) × T2) × (((B × S1) × E') × S2) → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    star (pairSwapVec ψ) ⬝ᵥ pairSwapVec ψ = 1 := by
  rw [← hψ]
  exact Equiv.sum_comp (pairSwapEquiv (A := A) (B := B) (T1 := T1) (T2 := T2) (S1 := S1)
    (S2 := S2) (E := E) (E' := E')).symm fun p => star ψ p * ψ p
end
end MIPRE.QLD

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
theorem physVec_unit : star M.physVec ⬝ᵥ M.physVec = 1 :=
  pairSwapVec_unit (expVec_unit M.Φ_unit (epr_unit (F := F) (n := Fin m → Bool)))
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

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- The coupling is symmetric on its face, which is half of the display's symmetry. -/
theorem chainCoupled_symm {g g' : LowIndDegPoly (F := F) (m := m) (d := d)} {h h' : Anc F m}
    (hc : ChainCoupled g g' h h') : ChainCoupled g' g h' h := Eq.symm hc
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- **Coupled pairs carry the same label**, which is the other half. Evaluating the coupling at a
cube point reads off the two labels there, the encoding of a cube datum being that datum on the
cube. -/
theorem chainLabel_eq_of_coupled {g g' : LowIndDegPoly (F := F) (m := m) (d := d)}
    {h h' : Anc F m} (hc : ChainCoupled g g' h h') : chainLabel g h = chainLabel g' h' := by
  funext y
  have hy := congrArg (fun p => MvPolynomial.eval (pt (F := F) y) p) hc
  simpa [chainLabel, cubeData, LowIndDegPoly.eval_toMv] using hy
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- **So the chain's last display is symmetric between the two pairs.** Its index set is cut out by
the coupling, symmetric on its face, and by a pairing condition read off one pair --- and the two
readings agree, so it may be read off either. That is what lets the derivation starting from Bob's
exact Pauli measurement reach the same expression as Alice's, and hence what makes
`lem:qld-pauli-selfcons` conclude. -/
theorem dotF_chainLabel_eq_of_coupled {g g' : LowIndDegPoly (F := F) (m := m) (d := d)}
    {h h' : Anc F m} (hc : ChainCoupled g g' h h') (v : Anc F m) :
    dotF (chainLabel g h) v = dotF (chainLabel g' h') v := by
  rw [chainLabel_eq_of_coupled hc]
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
omit [Algebra (ZMod 2) F] [NeZero m] in
/-- **The index set does not care which pair the label is read off.** This is the paper's sentence:
the conditions `(cd(g) - h) . u-tilde = a` and `g - g_h = g' - g_{h'}` are together equivalent to
`(cd(g') - h') . u-tilde = a` and the same coupling. -/
theorem swap_mem_coupledIdx {v : Anc F m} {a : F}
    {q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)} :
    q.swap ∈ coupledIdx v a ↔ q ∈ coupledIdx v a := by
  simp only [mem_coupledIdx, Prod.fst_swap, Prod.snd_swap]
  constructor
  · rintro ⟨hc, hl⟩
    exact ⟨chainCoupled_symm hc, (dotF_chainLabel_eq_of_coupled (chainCoupled_symm hc) v).trans hl⟩
  · rintro ⟨hc, hl⟩
    exact ⟨chainCoupled_symm hc, (dotF_chainLabel_eq_of_coupled (chainCoupled_symm hc) v).trans hl⟩
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
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
/-- **The chain's conclusion.** Given that each party's exact Pauli measurement is close to the
endpoint, the two are close to each other, which is `eq:qld-pulling-cons`. The factor two is the
triangle inequality's, and the paper absorbs it into `delta_S`. -/
theorem sum_xSqNorm_le_of_endOp (M : MirrorSimul ψ MA MB δ) (W : Bas) (v : Anc F m) {δ₁ δ₂ : ℝ}
    (h1 : ∑ a : F, snorm M.physVec
            ((aOp (M.aliceMTilde W v a) : Matrix _ _ ℂ) - M.endOp W v a) ^ 2 ≤ δ₁)
    (h2 : ∑ a : F, snorm M.physVec
            (M.endOp W v a - (bOp (M.bobMTilde W v a) : Matrix _ _ ℂ)) ^ 2 ≤ δ₂) :
    ∑ a : F, xSqNorm M.physVec (M.aliceMTilde W v a) (M.bobMTilde W v a) ≤ 2 * δ₁ + 2 * δ₂ := by
  have h := sum_snorm_sq_triangle' M.physVec
    (fun a : F => (aOp (M.aliceMTilde W v a) : Matrix _ _ ℂ))
    (fun a : F => M.endOp W v a)
    (fun a : F => (bOp (M.bobMTilde W v a) : Matrix _ _ ℂ))
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => xSqNorm_eq_snorm_sq M.physVec _ _]
  linarith
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
/-- **An operator of Alice's is unchanged by the lift**, the appended pair being Bob's. -/
theorem physLift_aOp (X : Matrix (((dA × Anc F m) × M.Ea) × Anc F m)
    (((dA × Anc F m) × M.Ea) × Anc F m) ℂ) :
    M.physLift (aOp X) = aOp X := by
  ext p q
  obtain ⟨p1, ⟨⟨p2, p3⟩, p4⟩, p5⟩ := p
  obtain ⟨q1, ⟨⟨q2, q3⟩, q4⟩, q5⟩ := q
  simp only [physLift, Matrix.reindex_apply, Matrix.submatrix_apply, physLiftEquiv,
    Equiv.coe_fn_symm_mk, kroneckerMap_apply, aOp, Matrix.one_apply, Prod.mk.injEq]
  by_cases h2 : p2 = q2 <;> by_cases h3 : p3 = q3 <;> by_cases h4 : p4 = q4 <;>
    by_cases h5 : p5 = q5 <;> simp [h2, h3, h4, h5]
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
/-- The chain starts at Alice's exact Pauli measurement on her physical triple. -/
theorem chainT_zero_eq (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    M.chainT W v u 0 a = aOp (M.toFirst.mTildeAnc W v a) :=
  M.physLift_aOp _
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
/-- And ends at `eq:qld-pulling-12`. -/
theorem chainT_nine_eq (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    M.chainT W v u 9 a = M.endOp W v a := rfl
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
/-- **Display `eq:qld-pulling-cons` for Alice**: her exact Pauli measurement on her physical
triple is close, in summed squared state distance, to the chain's endpoint. -/
theorem sum_uniform_snorm_sq_mTildeAnc_endOp_le {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u * ∑ a : F, snorm M.physVec
        ((aOp (M.toFirst.mTildeAnc W v a)
          : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
            × (((dB × Anc F m) × M.Eb) × Anc F m)) _ ℂ) - M.endOp W v a) ^ 2)
      ≤ 9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F) := by
  refine le_trans (le_of_eq ?_)
    (M.sum_uniform_snorm_sq_chainT_le (hm := hm) hψ hfail hprojA hprojB hd W v)
  refine Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [M.chainT_zero_eq W v u a, M.chainT_nine_eq W v u a]
  rfl
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {N : Type*} [Fintype N] [DecidableEq N]
omit [Fintype N] [DecidableEq N] in
/-- **Regrouping a weighted sum by the fibres of a relabelling.** -/
theorem sum_fibre_smul {Λ Λ' : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']
    (f : Λ → Λ') (α : Λ' → ℂ) (X : Λ → Matrix N N ℂ) :
    (∑ c : Λ', α c • ∑ a ∈ univ.filter fun a => f a = c, X a)
      = ∑ a : Λ, α (f a) • X a := by
  classical
  rw [← Finset.sum_fiberwise (univ : Finset Λ) f fun a => α (f a) • X a]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.mp ha).2]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m]
  [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB] in
/-- The swap carries a finite sum of vectors. -/
theorem swapVec_sum {ι : Type*} (s : Finset ι) (f : ι → dA × dB → ℂ) :
    swapVec (∑ i ∈ s, f i) = ∑ i ∈ s, swapVec (f i) := by
  funext p
  simp only [swapVec, Finset.sum_apply]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m]
  [DecidableEq dA] [DecidableEq dB] in
/-- **A sum of Kronecker products applied to the swapped state** is the swap of the exchanged
sum applied to the state. -/
theorem mulVec_kron_sum_swapVec {ι : Type*} (s : Finset ι) (X : ι → Matrix dB dB ℂ)
    (Y : ι → Matrix dA dA ℂ) (ψ : dA × dB → ℂ) :
    (∑ i ∈ s, (X i ⊗ₖ Y i)) *ᵥ swapVec ψ = swapVec ((∑ i ∈ s, (Y i ⊗ₖ X i)) *ᵥ ψ) := by
  rw [Matrix.sum_mulVec, Matrix.sum_mulVec, swapVec_sum]
  exact Finset.sum_congr rfl fun i _ => mulVec_kronecker_swapVec _ _ _
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m]
  [DecidableEq dB] in
/-- **The swap exchanges the two parties in the chain's conclusion.** -/
theorem snorm_swapVec_aOp_sub_kron_sum {ι : Type*} (s : Finset ι) (ψ : dA × dB → ℂ)
    (Z : Matrix dB dB ℂ) (X : ι → Matrix dB dB ℂ) (Y : ι → Matrix dA dA ℂ) :
    snorm (swapVec ψ) ((aOp Z : Matrix (dB × dA) (dB × dA) ℂ) - ∑ i ∈ s, (X i ⊗ₖ Y i))
      = snorm ψ ((bOp Z : Matrix (dA × dB) (dA × dB) ℂ) - ∑ i ∈ s, (Y i ⊗ₖ X i)) := by
  rw [snorm, snorm, Matrix.sub_mulVec, Matrix.sub_mulVec, mulVec_kron_sum_swapVec,
    show (aOp Z : Matrix (dB × dA) (dB × dA) ℂ) = Z ⊗ₖ (1 : Matrix dA dA ℂ) from rfl,
    show (bOp Z : Matrix (dA × dB) (dA × dB) ℂ) = (1 : Matrix dA dA ℂ) ⊗ₖ Z from rfl,
    mulVec_kronecker_swapVec, ← swapVec_sub, norm_swapVec]
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
set_option maxHeartbeats 4000000 in
/-- **The chain's endpoint does not care which party's pair carries the label.** Reindexing by
the exchange of the two pairs is a bijection of the index set (`swap_mem_coupledIdx`), and it
turns the one reading into the other. -/
theorem endOp_swap_sum (W : Bas) (v : Anc F m) (a : F) :
    (∑ q ∈ coupledIdx (F := F) (m := m) (d := d) v a,
        (M.toFirst.chainOp W q.2) ⊗ₖ (M.toSecond.chainOp W q.1))
      = M.endOp W v a :=
  Finset.sum_equiv (Equiv.prodComm (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m))
    (fun _ => swap_mem_coupledIdx.symm) fun _ _ => rfl
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
set_option maxHeartbeats 4000000 in
/-- **Display `eq:qld-pulling-cons` for Alice**, with the average over the sampled point dropped:
neither side depends on it. -/
theorem sum_snorm_sq_aliceMTilde_endOp_le {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (W : Bas) (v : Anc F m) :
    (∑ a : F, snorm M.physVec
        ((aOp (M.aliceMTilde W v a)
          : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
              × (((dB × Anc F m) × M.Eb) × Anc F m))
            ((((dA × Anc F m) × M.Ea) × Anc F m)
              × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ) - M.endOp W v a) ^ 2)
      ≤ 9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F) := by
  have h := M.sum_uniform_snorm_sq_mTildeAnc_endOp_le (hm := hm) hψ hfail hprojA hprojB hd W v
  rwa [← Finset.sum_mul, sum_uniform_eq_one, one_mul] at h
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
set_option maxHeartbeats 4000000 in
/-- **The same at the mirror, read on the physical state.** The mirror of a `MirrorSimul` is a
`MirrorSimul`, its physical state is this one with the parties written in the other order, and
its endpoint is this one read from the other side. -/
theorem snorm_endOp_bobMTilde_eq (W : Bas) (v : Anc F m) (a : F) :
    snorm M.mirror.physVec (aOp (M.mirror.aliceMTilde W v a) - M.mirror.endOp W v a)
      = snorm M.physVec (M.endOp W v a
          - (bOp (M.bobMTilde W v a)
            : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
                × (((dB × Anc F m) × M.Eb) × Anc F m))
              ((((dA × Anc F m) × M.Ea) × Anc F m)
                × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)) := by
  have h1 := snorm_swapVec_aOp_sub_kron_sum (coupledIdx (F := F) (m := m) (d := d) v a)
    M.physVec (M.bobMTilde W v a) (fun q => M.toSecond.chainOp W q.1)
    (fun q => M.toFirst.chainOp W q.2)
  have h2 := congrArg (fun X => snorm M.physVec ((bOp (M.bobMTilde W v a)
      : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
          × (((dB × Anc F m) × M.Eb) × Anc F m))
        ((((dA × Anc F m) × M.Ea) × Anc F m)
          × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ) - X)) (M.endOp_swap_sum W v a)
  rw [show M.mirror.physVec = swapVec M.physVec from M.mirror_physVec]
  exact (h1.trans h2).trans (snorm_sub_comm M.physVec _ _)
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
set_option maxHeartbeats 4000000 in
/-- **Display `eq:qld-pulling-cons` for Bob.** -/
theorem sum_snorm_sq_endOp_bobMTilde_le {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (W : Bas) (v : Anc F m) :
    (∑ a : F, snorm M.physVec (M.endOp W v a
        - (bOp (M.bobMTilde W v a)
          : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
              × (((dB × Anc F m) × M.Eb) × Anc F m))
            ((((dA × Anc F m) × M.Ea) × Anc F m)
              × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)) ^ 2)
      ≤ 9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F) := by
  have h := M.mirror.sum_snorm_sq_aliceMTilde_endOp_le (hm := hm) (swapVec_unit hψ)
    (povmValue_swapped_le hfail) hprojB hprojA hd W v
  refine le_trans (le_of_eq ?_) h
  exact (Finset.sum_congr rfl fun a _ =>
    congrArg (· ^ 2) (M.snorm_endOp_bobMTilde_eq W v a)).symm
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
set_option maxHeartbeats 4000000 in
/-- **Lemma `lem:qld-pauli-selfcons` at the level of the two exact Pauli measurements**: they
agree on the physical state, at four times what each costs to reach the chain's endpoint. -/
theorem sum_selfConsGap_le {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (W : Bas) (v : Anc F m) :
    (∑ a : F, M.selfConsGap W v a)
      ≤ 4 * (9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F)) := by
  have h := sum_xSqNorm_le_of_endOp M W v
    (M.sum_snorm_sq_aliceMTilde_endOp_le (hm := hm) hψ hfail hprojA hprojB hd W v)
    (M.sum_snorm_sq_endOp_bobMTilde_le (hm := hm) hψ hfail hprojA hprojB hd W v)
  have hgap : (∑ a : F, M.selfConsGap W v a)
      = ∑ a : F, xSqNorm M.physVec (M.aliceMTilde W v a) (M.bobMTilde W v a) := rfl
  rw [hgap]
  linarith
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
set_option maxHeartbeats 4000000 in
theorem _root_.solution {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (W : Bas) (e : F) (v : Anc F m) :
    snorm M.physVec ((aOp (M.aliceWTilde W e v)
        : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
            × (((dB × Anc F m) × M.Eb) × Anc F m))
          ((((dA × Anc F m) × M.Ea) × Anc F m)
            × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
        - bOp (M.bobWTilde W e v)) ^ 2
      ≤ 2 * (4 * (9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F))) := by
  classical
  have hA : (aOp (M.aliceWTilde W e v)
        : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
            × (((dB × Anc F m) × M.Eb) × Anc F m))
          ((((dA × Anc F m) × M.Ea) × Anc F m)
            × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
      = ∑ c : ZMod 2, sgn c • aOp (∑ a ∈ univ.filter
          fun a : F => Algebra.trace (ZMod 2) F (e * a) = c, M.aliceMTilde W v a) := by
    have h1 : (∑ c : ZMod 2, sgn c • ∑ a ∈ univ.filter
          fun a : F => Algebra.trace (ZMod 2) F (e * a) = c, M.aliceMTilde W v a)
        = M.aliceWTilde W e v :=
      sum_fibre_smul (fun a : F => Algebra.trace (ZMod 2) F (e * a)) sgn (M.aliceMTilde W v)
    rw [← h1, aOp_sum]
    exact Finset.sum_congr rfl fun c _ => aOp_smul _ _
  have hB : (bOp (M.bobWTilde W e v)
        : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
            × (((dB × Anc F m) × M.Eb) × Anc F m))
          ((((dA × Anc F m) × M.Ea) × Anc F m)
            × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
      = ∑ c : ZMod 2, sgn c • bOp (∑ a ∈ univ.filter
          fun a : F => Algebra.trace (ZMod 2) F (e * a) = c, M.bobMTilde W v a) := by
    have h1 : (∑ c : ZMod 2, sgn c • ∑ a ∈ univ.filter
          fun a : F => Algebra.trace (ZMod 2) F (e * a) = c, M.bobMTilde W v a)
        = M.bobWTilde W e v :=
      sum_fibre_smul (fun a : F => Algebra.trace (ZMod 2) F (e * a)) sgn (M.bobMTilde W v)
    rw [← h1, bOp_sum]
    exact Finset.sum_congr rfl fun c _ => bOp_smul _ _
  have hcoarse := sum_xSqNorm_fibre_le (ψ := M.physVec) M.physVec_unit
    (M.toFirst.isPVM_mTildeAnc W v) (M.toSecond.isPVM_mTildeAnc W v)
    fun a : F => Algebra.trace (ZMod 2) F (e * a)
  have hgap := M.sum_selfConsGap_le (hm := hm) hψ hfail hprojA hprojB hd W v
  have hfib : (∑ c : ZMod 2, snorm M.physVec
        ((aOp (∑ a ∈ univ.filter fun a : F => Algebra.trace (ZMod 2) F (e * a) = c,
            M.aliceMTilde W v a)
          : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
              × (((dB × Anc F m) × M.Eb) × Anc F m))
            ((((dA × Anc F m) × M.Ea) × Anc F m)
              × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
          - bOp (∑ a ∈ univ.filter fun a : F => Algebra.trace (ZMod 2) F (e * a) = c,
              M.bobMTilde W v a)) ^ 2)
      ≤ 4 * (9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F)) := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ =>
      (xSqNorm_eq_snorm_sq M.physVec _ _).symm)) ?_
    exact le_trans hcoarse hgap
  rw [hA, hB]
  refine le_trans (snorm_sq_obs_sub_le M.physVec sgn (fun c => le_of_eq (norm_sgn c)) _ _) ?_
  rw [show (Fintype.card (ZMod 2) : ℝ) = 2 from by norm_num]
  exact mul_le_mul_of_nonneg_left hfib (by norm_num)
end MIPRE.QLD.MirrorSimul
