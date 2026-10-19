-- Prove2me | solution 1 for MIPRE.QLD.agreeSum_ptFam_lineEvalFam
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:32:06.829182+00:00
-- url     : https://prove2.me/submissions/4c6ef81f-b5c8-45d1-b75c-af7ebd61b652

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/PaddedValue.lean (solution of MIPRE.QLD.agreeSum_ptFam_lineEvalFam);
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
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
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
import Definitions.Def_MIPRE_Background_QLD_PaddedValue
import Theorems.Thm_MIPRE_QLD_lineMats_pairCX_padShift
import Theorems.Thm_MIPRE_QLD_lineMats_pairCZ_padShift
import Theorems.Thm_MIPRE_QLD_padPt_mats
import Theorems.Thm_MIPRE_QLD_rep_add_lineParam_smul
import Theorems.Thm_MIPRE_QLD_sum_filter_padLineMats
import Theorems.Thm_MIPRE_QLD_sum_padGR_eq
import Theorems.Thm_MIPRE_QLD_sum_rawSet_fiber

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
variable {A : Type*} [Fintype A] {d : Type*} [Fintype d] [DecidableEq d] {ι : Type*} [Fintype ι]
variable {dA dB : Type*} [Fintype dA] [Fintype dB]
/-- The Born probability is linear in a real multiple of Bob's operator. -/
theorem bornProb_smul_right (ψ : dA × dB → ℂ) (r : ℝ) (EA : Matrix dA dA ℂ)
    (EB : Matrix dB dB ℂ) : bornProb ψ EA (r • EB) = r * bornProb ψ EA EB := by
  rw [bornProb, bornProb, Matrix.kronecker_smul, Matrix.smul_mulVec, dotProduct_smul,
    Complex.real_smul, Complex.re_ofReal_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A] {d : Type*} [Fintype d] [DecidableEq d]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The operators of a uniform average over a nonempty finset. -/
theorem POVM.avgOn_mats {S : Finset ι} (hS : S.Nonempty) (Q : ι → POVM A d) (a₀ : A) (a : A) :
    ((POVM.avgOn S Q a₀).mats a).val = (S.card : ℝ)⁻¹ • ∑ i ∈ S, ((Q i).mats a).val := by
  rw [POVM.avgOn, dif_pos hS, POVM.mix_mats, Finset.smul_sum]
  simp only [unifOn, ite_smul, zero_smul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
end
end MIPRE

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]
variable [Algebra (ZMod 2) F] {hm : m ∣ Fintype.card F}
variable {d : ℕ} {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {ε : ℝ}
variable {M : Question F m → POVM (Answer F m d) dB}
theorem factorsX_aPres : FactorsX (aPres hm .X) := fun _ _ => ⟨rfl, rfl, rfl⟩
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]
variable [Algebra (ZMod 2) F] {hm : m ∣ Fintype.card F}
variable {d : ℕ} {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {ε : ℝ}
variable {M : Question F m → POVM (Answer F m d) dB}
theorem factorsX_dPres : FactorsX (dPres hm .X) := fun _ _ => ⟨rfl, rfl, rfl⟩
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]
variable [Algebra (ZMod 2) F] {hm : m ∣ Fintype.card F}
variable {d : ℕ} {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {ε : ℝ}
variable {M : Question F m → POVM (Answer F m d) dB}
theorem factorsZ_aPres : FactorsZ (aPres hm .Z) := fun _ _ => ⟨rfl, rfl, rfl⟩
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]
variable [Algebra (ZMod 2) F] {hm : m ∣ Fintype.card F}
variable {d : ℕ} {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {ε : ℝ}
variable {M : Question F m → POVM (Answer F m d) dB}
theorem factorsZ_dPres : FactorsZ (dPres hm .Z) := fun _ _ => ⟨rfl, rfl, rfl⟩
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)
theorem aPres_base_eq (W : Bas) (c : Content F m) :
    (aPres hm W).base c = CL.rep ((aPres hm W).dir c) (c.pt W) := rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)
theorem dPres_base_eq (W : Bas) (c : Content F m) :
    (dPres hm W).base c = CL.rep ((dPres hm W).dir c) (c.pt W) := rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)
theorem aPres_dir_ofLPX (D : LPData F m) (u : Point F m) :
    (aPres hm .X).dir (ofLPX D u) = D.dir hm .aline := rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)
theorem aPres_dir_ofLPZ (D : LPData F m) (u : Point F m) :
    (aPres hm .Z).dir (ofLPZ D u) = D.dir hm .aline := rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)
theorem dPres_dir_ofLPX (D : LPData F m) (u : Point F m) :
    (dPres hm .X).dir (ofLPX D u) = D.dir hm .dline := rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)
theorem dPres_dir_ofLPZ (D : LPData F m) (u : Point F m) :
    (dPres hm .Z).dir (ofLPZ D u) = D.dir hm .dline := rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA : Type} [Fintype dA] [DecidableEq dA] {hm : m ∣ Fintype.card F}
variable (hm4 : 4 * m ∣ Fintype.card F)
variable (hm)
theorem factorsX_presOf (ty : CL.Ty) : FactorsX (presOf hm ty .X) := by
  cases ty
  · exact factorsX_aPres
  · exact factorsX_aPres
  · exact factorsX_dPres
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA : Type} [Fintype dA] [DecidableEq dA] {hm : m ∣ Fintype.card F}
variable (hm4 : 4 * m ∣ Fintype.card F)
variable (hm)
theorem factorsZ_presOf (ty : CL.Ty) : FactorsZ (presOf hm ty .Z) := by
  cases ty
  · exact factorsZ_aPres
  · exact factorsZ_aPres
  · exact factorsZ_dPres
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA : Type} [Fintype dA] [DecidableEq dA] {hm : m ∣ Fintype.card F}
variable (hm4 : 4 * m ∣ Fintype.card F)
variable (hm)
theorem presOf_base_eq (ty : CL.Ty) (W : Bas) (c : Content F m) :
    (presOf hm ty W).base c = CL.rep ((presOf hm ty W).dir c) (c.pt W) := by
  cases ty
  · exact aPres_base_eq hm W c
  · exact aPres_base_eq hm W c
  · exact dPres_base_eq hm W c
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA : Type} [Fintype dA] [DecidableEq dA] {hm : m ∣ Fintype.card F}
variable (hm4 : 4 * m ∣ Fintype.card F)
variable (hm)
theorem presOf_dir_ofLPX (ty : CL.Ty) (hty : ty ≠ .point) (D : LPData F m) (u : Point F m) :
    (presOf hm ty .X).dir (ofLPX D u) = D.dir hm ty := by
  cases ty
  · exact absurd rfl hty
  · exact aPres_dir_ofLPX hm D u
  · exact dPres_dir_ofLPX hm D u
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA : Type} [Fintype dA] [DecidableEq dA] {hm : m ∣ Fintype.card F}
variable (hm4 : 4 * m ∣ Fintype.card F)
variable (hm)
theorem presOf_dir_ofLPZ (ty : CL.Ty) (hty : ty ≠ .point) (D : LPData F m) (u : Point F m) :
    (presOf hm ty .Z).dir (ofLPZ D u) = D.dir hm ty := by
  cases ty
  · exact absurd rfl hty
  · exact aPres_dir_ofLPZ hm D u
  · exact dPres_dir_ofLPZ hm D u
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA : Type} [Fintype dA] [DecidableEq dA] {hm : m ∣ Fintype.card F}
variable (hm4 : 4 * m ∣ Fintype.card F)
variable (hm)
theorem lineMeas_mats (ty : CL.Ty) {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u₀ : Point F (4 * m)) (s : F)
    {S : Finset (Point F (4 * m))} (hS : S.Nonempty) (f : LinePoly F (m * d + 1)) :
    ((lineMeas hm hm4 ty hM u₀ s S).mats f).val
      = (S.card : ℝ)⁻¹ • ∑ raw ∈ S,
          padLineMats hm4 ty (presOf hm ty .X) (presOf hm ty .Z) M ⟨u₀, s, raw⟩ f := by
  rw [lineMeas, POVM.avgOn_mats hS]
  rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA : Type} [Fintype dA] [DecidableEq dA] {hm : m ∣ Fintype.card F}
variable (hm4 : 4 * m ∣ Fintype.card F)
variable (hm)
omit [Algebra (ZMod 2) F] in
theorem mem_rawFiber {s : F} {v' raw : Point F (4 * m)} :
    raw ∈ rawFiber hm4 s v' ↔ zeroBelow (chi hm4 s) raw = v' := by
  rw [rawFiber, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA : Type} [Fintype dA] [DecidableEq dA] {hm : m ∣ Fintype.card F}
variable (hm4 : 4 * m ∣ Fintype.card F)
variable (hm)
omit [DecidableEq F] [Algebra (ZMod 2) F] in
theorem LPData.dir_eq_lineDir (ty : CL.Ty) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) :
    (⟨u, s, raw⟩ : LPData F (4 * m)).dir hm4 ty = lineDir hm4 ty s raw := by
  cases ty <;> rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA : Type} [Fintype dA] [DecidableEq dA] {hm : m ∣ Fintype.card F}
variable (hm4 : 4 * m ∣ Fintype.card F)
variable (hm)
omit [Algebra (ZMod 2) F] in
theorem rawSet_nonempty (ty : CL.Ty) (s : F) (raw : Point F (4 * m)) :
    (rawSet hm4 ty s raw).Nonempty := by
  cases ty
  · exact ⟨raw, mem_univ _⟩
  · exact ⟨raw, mem_univ _⟩
  · exact ⟨raw, (mem_rawFiber hm4).mpr rfl⟩
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA : Type} [Fintype dA] [DecidableEq dA] {hm : m ∣ Fintype.card F}
variable (hm4 : 4 * m ∣ Fintype.card F)
variable (hm)
omit [Algebra (ZMod 2) F] in
/-- Every raw direction the strategy averages over describes the sample's line. -/
theorem lineDir_of_mem_rawSet (ty : CL.Ty) {s : F} {raw raw' : Point F (4 * m)}
    (h : raw' ∈ rawSet hm4 ty s raw) : lineDir hm4 ty s raw' = lineDir hm4 ty s raw := by
  cases ty
  · rfl
  · rfl
  · exact (mem_rawFiber hm4).mp h
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA : Type} [Fintype dA] [DecidableEq dA] {hm : m ∣ Fintype.card F}
variable (hm4 : 4 * m ∣ Fintype.card F)
variable (hm)
/-- **The strategy's line data, moved to the sample's point along the line, is the sample's own
data**, for every raw direction the strategy averages over. -/
theorem padShift_lineData (ty : CL.Ty) (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m))
    {raw' : Point F (4 * m)} (h : raw' ∈ rawSet hm4 ty s raw) :
    padShift hm4 ty (lineTau hm4 ty u s raw) ⟨CL.rep (lineDir hm4 ty s raw) u, s, raw'⟩
      = ⟨u, s, raw'⟩ := by
  rw [padShift, LPData.dir_eq_lineDir, lineDir_of_mem_rawSet hm4 ty h]
  show (⟨CL.rep (lineDir hm4 ty s raw) u + lineTau hm4 ty u s raw • lineDir hm4 ty s raw, s,
    raw'⟩ : LPData F (4 * m)) = ⟨u, s, raw'⟩
  rw [lineTau, rep_add_lineParam_smul]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA : Type} [Fintype dA] [DecidableEq dA] {hm : m ∣ Fintype.card F}
variable (hm4 : 4 * m ∣ Fintype.card F)
variable (hm)
variable {dB : Type} [Fintype dB] [DecidableEq dB] {M : Question F m → POVM (Answer F m d) dB}
/-- **The pasted line measurement is unchanged by moving the padded point along the padded
line.** -/
theorem pasteLine_subPair_padShift (ty : CL.Ty) (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    (hfacX : FactorsX PX) (hfacZ : FactorsZ PZ)
    (hdirX : ∀ (D : LPData F m) (u : Point F m), PX.dir (ofLPX D u) = D.dir hm ty)
    (hdirZ : ∀ (D : LPData F m) (u : Point F m), PZ.dir (ofLPZ D u) = D.dir hm ty) (tau : F)
    (P : LPData F (4 * m)) (e : SubRand F m) (q : LinePoly F (m * d) × LinePoly F (m * d)) :
    pasteLine PX PZ d M (pairCX (subPair hm4 hm ty (padShift hm4 ty tau P) e))
        (pairCZ (subPair hm4 hm ty (padShift hm4 ty tau P) e)) q
      = pasteLine PX PZ d M (pairCX (subPair hm4 hm ty P e)) (pairCZ (subPair hm4 hm ty P e)) q :=
          by
  rw [pasteLine, pasteLine, lineMats_pairCX_padShift hm hm4 ty PX hfacX hdirX,
    lineMats_pairCZ_padShift hm hm4 ty PZ hfacZ hdirZ]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA : Type} [Fintype dA] [DecidableEq dA] {hm : m ∣ Fintype.card F}
variable (hm4 : 4 * m ∣ Fintype.card F)
variable (hm)
variable {dB : Type} [Fintype dB] [DecidableEq dB] {M : Question F m → POVM (Answer F m d) dB}
/-- **The padded line measurement read at the parameter of a point of the padded line is the
average over the fresh randomness of the pasted line measurement at that point, coarse-grained by
the combining map there.** -/
theorem sum_filter_padLineMats_eq_lineComb (ty : CL.Ty) (PX : LinePres F m hm .X)
    (PZ : LinePres F m hm .Z) (hfacX : FactorsX PX) (hfacZ : FactorsZ PZ)
    (hbaseX : ∀ c : Content F m, PX.base c = CL.rep (PX.dir c) (c.pt .X))
    (hdirX : ∀ (D : LPData F m) (u : Point F m), PX.dir (ofLPX D u) = D.dir hm ty)
    (hbaseZ : ∀ c : Content F m, PZ.base c = CL.rep (PZ.dir c) (c.pt .Z))
    (hdirZ : ∀ (D : LPData F m) (u : Point F m), PZ.dir (ofLPZ D u) = D.dir hm ty)
    (P : LPData F (4 * m)) (tau a : F) :
    ∑ f ∈ univ.filter fun f : LinePoly F (m * d + 1) => LinePoly.eval f tau = a,
        padLineMats hm4 ty PX PZ M P f
      = ((Fintype.card (SubRand F m) : ℝ))⁻¹ • ∑ e : SubRand F m,
          lineComb PX PZ d M (pairCX (subPair hm4 hm ty (padShift hm4 ty tau P) e))
            (pairCZ (subPair hm4 hm ty (padShift hm4 ty tau P) e))
            (alph (padShift hm4 ty tau P).pt) (bet (padShift hm4 ty tau P).pt) a := by
  rw [sum_filter_padLineMats hm4 ty PX PZ hbaseX hdirX hbaseZ hdirZ P tau a]
  refine congrArg _ (Finset.sum_congr rfl fun e _ => ?_)
  rw [lineComb]
  exact Finset.sum_congr rfl fun q _ =>
    (pasteLine_subPair_padShift hm hm4 ty PX PZ hfacX hfacZ hdirX hdirZ tau P e q).symm
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA : Type} [Fintype dA] [DecidableEq dA] {hm : m ∣ Fintype.card F}
variable (hm4 : 4 * m ∣ Fintype.card F)
variable (hm)
/-- **The strategy's line measurement, read at the parameter of the sample's point, is the
average over the raw directions and the fresh randomness of the pasted line measurement at the
sample's own data, coarse-grained by the combining map at the sample's point.** This is the
quantity `lem:qld-padded-lines` controls. -/
theorem lineMeas_map_eval_mats (ty : CL.Ty) (hty : ty ≠ .point)
    {M : Question F m → POVM (Answer F m d) dA} (hM : ∀ q, IsPVM fun a => (((M q).mats a).val))
    (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m)) (a : F) :
    (((lineMeas hm hm4 ty hM (CL.rep (lineDir hm4 ty s raw) u) s (rawSet hm4 ty s raw)).map
        fun f => LinePoly.eval f (lineTau hm4 ty u s raw)).mats a).val
      = ((rawSet hm4 ty s raw).card : ℝ)⁻¹ • ∑ raw' ∈ rawSet hm4 ty s raw,
          ((Fintype.card (SubRand F m) : ℝ))⁻¹ • ∑ e : SubRand F m,
            lineComb (presOf hm ty .X) (presOf hm ty .Z) d M
              (pairCX (subPair hm4 hm ty ⟨u, s, raw'⟩ e)) (pairCZ (subPair hm4 hm ty ⟨u, s, raw'⟩
                  e))
              (alph u) (bet u) a := by
  rw [POVM.map_mats]
  simp only [lineMeas_mats hm hm4 ty hM _ s (rawSet_nonempty hm4 ty s raw)]
  rw [← Finset.smul_sum, Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl fun raw' hraw' => ?_)
  rw [sum_filter_padLineMats_eq_lineComb hm hm4 ty _ _ (factorsX_presOf hm ty) (factorsZ_presOf hm
      ty)
    (presOf_base_eq hm ty .X) (presOf_dir_ofLPX hm ty hty) (presOf_base_eq hm ty .Z)
    (presOf_dir_ofLPZ hm ty hty) ⟨_, s, raw'⟩ _ a, padShift_lineData hm4 ty u s raw hraw']
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  (hMA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hMB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
  (Ψ : ((dA × Anc F m) × (F × F)) × ((dB × Anc F m) × (F × F)) → ℂ)
theorem sum_bornProb_ptFam_lineEvalFam (ty : CL.Ty) (hty : ty ≠ .point) (x : Amb F m) :
    ∑ a, bornProb Ψ (((ptFam hMA x).mats a).val) (((lineEvalFam hm hm4 ty hMB x).mats a).val)
      = ((rawSet hm4 ty x.2.1 x.2.2).card : ℝ)⁻¹
          * ∑ raw' ∈ rawSet hm4 ty x.2.1 x.2.2, lineTermR hm hm4 Ψ MA MB ty x.1 x.2.1 raw' := by
  obtain ⟨u, s, raw⟩ := x
  simp only [lineEvalFam, lineFam, ptFam, lineMeas_map_eval_mats hm hm4 ty hty hMB, padPt_mats,
    bornProb_smul_right, bornProb_sum_right, lineTermR, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun raw' _ => Finset.sum_comm
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  (hMA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hMB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
  (Ψ : ((dA × Anc F m) × (F × F)) × ((dB × Anc F m) × (F × F)) → ℂ)
omit [Field F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem card_amb : (Fintype.card (Amb F m) : ℝ)
    = (Fintype.card F : ℝ) ^ (4 * m) * ((Fintype.card F : ℝ) * (Fintype.card F : ℝ) ^ (4 * m)) := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  push_cast
  ring
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  (hMA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hMB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
  (Ψ : ((dA × Anc F m) × (F × F)) × ((dB × Anc F m) × (F × F)) → ℂ)
omit [Field F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem card_subRand : (Fintype.card (SubRand F m) : ℝ)
    = ((Fintype.card F : ℝ) * (Fintype.card F : ℝ) ^ m)
      * ((Fintype.card F : ℝ) * (Fintype.card F : ℝ) ^ m) := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  push_cast
  ring
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  (hMA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hMB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
  (Ψ : ((dA × Anc F m) × (F × F)) × ((dB × Anc F m) × (F × F)) → ℂ)
theorem avgSubAB_padGR (ty : CL.Ty) (s : F) :
    avgSubAB hm4 hm ty s (padGR hm Ψ MA MB ty)
      = ((Fintype.card F : ℝ) ^ (10 * m + 2))⁻¹ * ((Fintype.card (SubRand F m) : ℝ)
          * ∑ pt : Point F (4 * m), ∑ raw : Point F (4 * m), lineTermR hm hm4 Ψ MA MB ty pt s raw)
          := by
  rw [avgSubAB, sumSubAB]
  congr 1
  simp only [sumSubAt, Finset.mul_sum]
  exact Finset.sum_congr rfl fun pt _ => Finset.sum_congr rfl fun raw _ =>
    sum_padGR_eq hm hm4 Ψ ty s pt raw
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  (hMA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hMB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
  (Ψ : ((dA × Anc F m) × (F × F)) × ((dB × Anc F m) × (F × F)) → ℂ)
omit [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- The normalizations agree: the uniform average over the ambient sample is the average over the
seed of the padded average `avgSubAB`. -/
theorem inv_card_amb_eq :
    (Fintype.card (Amb F m) : ℝ)⁻¹
      = (Fintype.card F : ℝ)⁻¹ * (((Fintype.card F : ℝ) ^ (10 * m + 2))⁻¹
          * (Fintype.card (SubRand F m) : ℝ)) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [card_amb, card_subRand]
  field_simp
  ring
end
end MIPRE.QLD

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  (hMA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hMB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
  (Ψ : ((dA × Anc F m) × (F × F)) × ((dB × Anc F m) × (F × F)) → ℂ)
theorem _root_.solution (ty : CL.Ty) (hty : ty ≠ .point) :
    agreeSum (uniform (Amb F m)) Ψ (ptFam hMA) (lineEvalFam hm hm4 ty hMB)
      = (Fintype.card F : ℝ)⁻¹ * ∑ s : F, avgSubAB hm4 hm ty s (padGR hm Ψ MA MB ty) := by
  classical
  have hsum : ∑ x : Amb F m, ((rawSet hm4 ty x.2.1 x.2.2).card : ℝ)⁻¹
        * ∑ raw' ∈ rawSet hm4 ty x.2.1 x.2.2, lineTermR hm hm4 Ψ MA MB ty x.1 x.2.1 raw'
      = ∑ s : F, ∑ pt : Point F (4 * m), ∑ raw : Point F (4 * m),
          lineTermR hm hm4 Ψ MA MB ty pt s raw := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun u _ => ?_
    exact sum_rawSet_fiber hm4 ty s fun raw' => lineTermR hm hm4 Ψ MA MB ty u s raw'
  simp only [avgSubAB_padGR hm hm4 Ψ ty, agreeSum, uniform,
    sum_bornProb_ptFam_lineEvalFam hm hm4 hMA hMB Ψ ty hty]
  rw [← Finset.mul_sum, hsum, inv_card_amb_eq]
  simp only [← Finset.mul_sum]
  ring
end MIPRE.QLD
