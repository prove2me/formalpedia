-- Prove2me | solution 1 for MIPRE.QLD.sumSub_xc_dline
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:29:50.412602+00:00
-- url     : https://prove2.me/submissions/5caa754e-3789-4718-9ad1-c554386f59da

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Padded.lean (solution of MIPRE.QLD.sumSub_xc_dline);
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
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
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
import Theorems.Thm_MIPRE_QLD_sum_point_pad
import Theorems.Thm_MIPRE_QLD_sum_seedIn

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset
variable {α β F M : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype F]
  [AddCommMonoid M]
variable {A B C D E G M : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
  [Fintype G] [AddCommMonoid M]
theorem sum_congr1 {f g : A → M} (h : ∀ a, f a = g a) : ∑ a : A, f a = ∑ a : A, g a :=
  Finset.sum_congr rfl fun a _ => h a
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset
variable {α β F M : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype F]
  [AddCommMonoid M]
variable {A B C D E G M : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
  [Fintype G] [AddCommMonoid M]
theorem sum_congr2 {f g : A → B → M} (h : ∀ a b, f a b = g a b) :
    ∑ a : A, ∑ b : B, f a b = ∑ a : A, ∑ b : B, g a b :=
  sum_congr1 fun a => sum_congr1 fun b => h a b
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset
variable {α β F M : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype F]
  [AddCommMonoid M]
variable {A B C D E G M : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
  [Fintype G] [AddCommMonoid M]
theorem sum_congr3 {f g : A → B → C → M} (h : ∀ a b c, f a b c = g a b c) :
    ∑ a : A, ∑ b : B, ∑ c : C, f a b c = ∑ a : A, ∑ b : B, ∑ c : C, g a b c :=
  sum_congr1 fun a => sum_congr2 fun b c => h a b c
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset
variable {α β F M : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype F]
  [AddCommMonoid M]
variable {A B C D E G M : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
  [Fintype G] [AddCommMonoid M]
theorem sum_congr4 {f g : A → B → C → D → M} (h : ∀ a b c d, f a b c d = g a b c d) :
    ∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, f a b c d
      = ∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, g a b c d :=
  sum_congr1 fun a => sum_congr3 fun b c d => h a b c d
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset
variable {α β F M : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype F]
  [AddCommMonoid M]
variable {A B C D E G M : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
  [Fintype G] [AddCommMonoid M]
theorem sum_nsmul1 (n : ℕ) (f : A → M) : ∑ a : A, n • f a = n • ∑ a : A, f a :=
  Finset.sum_nsmul _ _ _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset
variable {α β F M : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype F]
  [AddCommMonoid M]
variable {A B C D E G M : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
  [Fintype G] [AddCommMonoid M]
theorem sum_nsmul2 (n : ℕ) (f : A → B → M) :
    ∑ a : A, ∑ b : B, n • f a b = n • ∑ a : A, ∑ b : B, f a b := by
  rw [sum_congr1 fun a => sum_nsmul1 n (f a), sum_nsmul1]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset
variable {α β F M : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype F]
  [AddCommMonoid M]
variable {A B C D E G M : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
  [Fintype G] [AddCommMonoid M]
theorem sum_nsmul3 (n : ℕ) (f : A → B → C → M) :
    ∑ a : A, ∑ b : B, ∑ c : C, n • f a b c = n • ∑ a : A, ∑ b : B, ∑ c : C, f a b c := by
  rw [sum_congr1 fun a => sum_nsmul2 n (f a), sum_nsmul1]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset
variable {α β F M : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype F]
  [AddCommMonoid M]
variable {A B C D E G M : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
  [Fintype G] [AddCommMonoid M]
/-- Moving the second of four nested sums inwards to last place. -/
theorem sum_comm_four_in (f : A → B → C → D → M) :
    ∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, f a b c d
      = ∑ a : A, ∑ c : C, ∑ d : D, ∑ b : B, f a b c d := by
  refine sum_congr1 fun a => ?_
  rw [Finset.sum_comm]
  exact sum_congr1 fun c => Finset.sum_comm
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset
variable {α β F M : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype F]
  [AddCommMonoid M]
variable {A B C D E G M : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
  [Fintype G] [AddCommMonoid M]
/-- Moving the second of six nested sums inwards past the next two. A block decomposition produces
the two sides' data interleaved, and this is what puts each side's data back together. -/
theorem sum_comm_six (f : A → B → C → D → E → G → M) :
    ∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, ∑ e : E, ∑ x : G, f a b c d e x
      = ∑ a : A, ∑ c : C, ∑ d : D, ∑ b : B, ∑ e : E, ∑ x : G, f a b c d e x := by
  refine sum_congr1 fun a => ?_
  rw [Finset.sum_comm]
  exact sum_congr1 fun c => Finset.sum_comm
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset
variable {α β F M : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype F]
  [AddCommMonoid M]
variable {A B C D E G M : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
  [Fintype G] [AddCommMonoid M]
/-- Swapping the fourth and fifth of six nested sums. -/
theorem sum_comm_six_swap (f : A → B → C → D → E → G → M) :
    ∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, ∑ e : E, ∑ x : G, f a b c d e x
      = ∑ a : A, ∑ b : B, ∑ c : C, ∑ e : E, ∑ d : D, ∑ x : G, f a b c d e x :=
  sum_congr3 fun a b c => Finset.sum_comm
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset
variable {α β F M : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype F]
  [AddCommMonoid M]
variable {A B C D E G M : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
  [Fintype G] [AddCommMonoid M]
/-- Only the first component of a pair is read. -/
theorem sum_prod_fst [DecidableEq A] (h : A → M) :
    ∑ p : A × B, h p.1 = Fintype.card B • ∑ a : A, h a := by
  classical
  rw [← Finset.univ_product_univ, Finset.sum_product]
  exact (sum_congr1 fun a => Finset.sum_const (h a)).trans
    (by rw [Finset.card_univ, sum_nsmul1])
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem _root_.solution (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) {s : F}
    {i : Fin m} (h : padCase (chi hm4 s) = .xc i) {M : Type*} [AddCommMonoid M]
    (g : LPData F m → LPData F m → M) :
    sumSub hm4 hm .dline s g
      = (Fintype.card (Fin (2 * m) → F) * Fintype.card (Fin (2 * m) → F)
            * Fintype.card (Point F m) * m * Fintype.card (Point F m) * m)
        • sumRestr hm i (fun cX => sumRestr hm 0 (fun cZ => g cX cZ)) := by
  have hX : ∀ (pt raw : Point F (4 * m)) (e : F × Point F m),
      subX hm4 hm ⟨pt, s, raw⟩ e = ⟨xBlk pt, seedIn hm i e.1, xBlk raw⟩ := fun pt raw e => by
    show subXof hm (padCase (chi hm4 s)) _ e = _
    rw [h]
    rfl
  have hZ : ∀ (pt raw : Point F (4 * m)) (e : F × Point F m),
      subZ hm4 hm .dline ⟨pt, s, raw⟩ e = ⟨zBlk pt, seedIn hm 0 e.1, zBlk raw⟩ :=
    fun pt raw e => by
      show subZof hm .dline (padCase (chi hm4 s)) _ e = _
      rw [h]
      rfl
  rw [sumSub, sum_congr4 (fun (pt raw : Point F (4 * m)) (eX eZ : F × Point F m) => by
      rw [hX pt raw eX, hZ pt raw eZ]),
    sum_comm_four_in (fun (pt raw : Point F (4 * m)) (eX eZ : F × Point F m) =>
      g ⟨xBlk pt, seedIn hm i eX.1, xBlk raw⟩ ⟨zBlk pt, seedIn hm 0 eZ.1, zBlk raw⟩),
    sum_congr3 (fun (pt : Point F (4 * m)) (eX eZ : F × Point F m) =>
      sum_point_pad (fun vX vZ =>
        g ⟨xBlk pt, seedIn hm i eX.1, vX⟩ ⟨zBlk pt, seedIn hm 0 eZ.1, vZ⟩)),
    sum_nsmul3 (Fintype.card (Fin (2 * m) → F))
      (fun (pt : Point F (4 * m)) (eX eZ : F × Point F m) =>
        ∑ vX : Point F m, ∑ vZ : Point F m,
          g ⟨xBlk pt, seedIn hm i eX.1, vX⟩ ⟨zBlk pt, seedIn hm 0 eZ.1, vZ⟩),
    show (∑ pt : Point F (4 * m), ∑ eX : F × Point F m, ∑ eZ : F × Point F m, ∑ vX : Point F m,
          ∑ vZ : Point F m,
            g ⟨xBlk pt, seedIn hm i eX.1, vX⟩ ⟨zBlk pt, seedIn hm 0 eZ.1, vZ⟩)
        = ∑ pt : Point F (4 * m), (fun pX pZ => ∑ eX : F × Point F m, ∑ eZ : F × Point F m,
            ∑ vX : Point F m, ∑ vZ : Point F m,
              g ⟨pX, seedIn hm i eX.1, vX⟩ ⟨pZ, seedIn hm 0 eZ.1, vZ⟩) (xBlk pt) (zBlk pt)
      from rfl,
    sum_point_pad (fun pX pZ => ∑ eX : F × Point F m, ∑ eZ : F × Point F m, ∑ vX : Point F m,
      ∑ vZ : Point F m, g ⟨pX, seedIn hm i eX.1, vX⟩ ⟨pZ, seedIn hm 0 eZ.1, vZ⟩), smul_smul,
    sum_congr2 (fun pX pZ : Point F m =>
      sum_prod_fst fun sX : F => ∑ eZ : F × Point F m, ∑ vX : Point F m, ∑ vZ : Point F m,
        g ⟨pX, seedIn hm i sX, vX⟩ ⟨pZ, seedIn hm 0 eZ.1, vZ⟩),
    sum_nsmul2 (Fintype.card (Point F m)) (fun pX pZ : Point F m =>
      ∑ sX : F, ∑ eZ : F × Point F m, ∑ vX : Point F m, ∑ vZ : Point F m,
        g ⟨pX, seedIn hm i sX, vX⟩ ⟨pZ, seedIn hm 0 eZ.1, vZ⟩),
    smul_smul,
    sum_congr2 (fun pX pZ : Point F m =>
      sum_seedIn hm i fun sX : F => ∑ eZ : F × Point F m, ∑ vX : Point F m, ∑ vZ : Point F m,
        g ⟨pX, sX, vX⟩ ⟨pZ, seedIn hm 0 eZ.1, vZ⟩),
    sum_nsmul2 m (fun pX pZ : Point F m =>
      ∑ o : Fin (Fintype.card F / m), ∑ eZ : F × Point F m, ∑ vX : Point F m, ∑ vZ : Point F m,
        g ⟨pX, (seedEquiv hm).symm (i, o), vX⟩ ⟨pZ, seedIn hm 0 eZ.1, vZ⟩),
    smul_smul,
    sum_congr3 (fun (pX pZ : Point F m) (o : Fin (Fintype.card F / m)) =>
      sum_prod_fst fun sZ : F => ∑ vX : Point F m, ∑ vZ : Point F m,
        g ⟨pX, (seedEquiv hm).symm (i, o), vX⟩ ⟨pZ, seedIn hm 0 sZ, vZ⟩),
    sum_nsmul3 (Fintype.card (Point F m))
      (fun (pX pZ : Point F m) (o : Fin (Fintype.card F / m)) =>
        ∑ sZ : F, ∑ vX : Point F m, ∑ vZ : Point F m,
          g ⟨pX, (seedEquiv hm).symm (i, o), vX⟩ ⟨pZ, seedIn hm 0 sZ, vZ⟩),
    smul_smul,
    sum_congr3 (fun (pX pZ : Point F m) (o : Fin (Fintype.card F / m)) =>
      sum_seedIn hm 0 fun sZ : F => ∑ vX : Point F m, ∑ vZ : Point F m,
        g ⟨pX, (seedEquiv hm).symm (i, o), vX⟩ ⟨pZ, sZ, vZ⟩),
    sum_nsmul3 m (fun (pX pZ : Point F m) (o : Fin (Fintype.card F / m)) =>
      ∑ o' : Fin (Fintype.card F / m), ∑ vX : Point F m, ∑ vZ : Point F m,
        g ⟨pX, (seedEquiv hm).symm (i, o), vX⟩ ⟨pZ, (seedEquiv hm).symm (0, o'), vZ⟩),
    smul_smul,
    sum_comm_six_swap (fun (pX pZ : Point F m) (o o' : Fin (Fintype.card F / m))
      (vX vZ : Point F m) =>
        g ⟨pX, (seedEquiv hm).symm (i, o), vX⟩ ⟨pZ, (seedEquiv hm).symm (0, o'), vZ⟩),
    sum_comm_six (fun (pX pZ : Point F m) (o : Fin (Fintype.card F / m)) (vX : Point F m)
      (o' : Fin (Fintype.card F / m)) (vZ : Point F m) =>
        g ⟨pX, (seedEquiv hm).symm (i, o), vX⟩ ⟨pZ, (seedEquiv hm).symm (0, o'), vZ⟩)]
  rfl
end MIPRE.QLD
