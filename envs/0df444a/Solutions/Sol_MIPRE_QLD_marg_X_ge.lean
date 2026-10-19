-- Prove2me | solution 1 for MIPRE.QLD.marg_X_ge
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:47:53.588966+00:00
-- url     : https://prove2.me/submissions/a0ac4864-e91a-471c-977e-3e43d7f0438b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Complete.lean (solution of MIPRE.QLD.marg_X_ge);
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
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_IsPVM_posSemidef
import Theorems.Thm_MIPRE_LIDT_LowIndDegPoly_eval_blockPoly
import Theorems.Thm_MIPRE_QLD_not_depOutside_gA_of_isGood
import Theorems.Thm_MIPRE_QLD_one_sub_two_sqrt_le_sum_snorm_sq
import Theorems.Thm_MIPRE_QLD_snorm_sq_ordComb_ordXZ_of_ne
import Theorems.Thm_MIPRE_QLD_sum_point_pad
import Theorems.Thm_MIPRE_QLD_sum_uniform_snorm_sq_ordComb_ZX_le_of_isLinAB
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_bornProb_nonneg
import Theorems.Thm_MIPRE_posSemidef_of_proj
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
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
/-- **A projection is bounded by the identity.** -/
theorem proj_le_one {P : Matrix N N ℂ} (hsa : Pᴴ = P) (hidem : P * P = P) :
    P ≤ (1 : Matrix N N ℂ) := by
  refine sub_nonneg.mp (Matrix.nonneg_iff_posSemidef.mpr ?_)
  have h : (1 : Matrix N N ℂ) - P = ((1 : Matrix N N ℂ) - P)ᴴ * ((1 : Matrix N N ℂ) - P) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hsa, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hidem]
    abel
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _
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
variable {N : Type*} [Fintype N] [DecidableEq N]
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
theorem isPVM_fibSum {G : α → Matrix N N ℂ} (h : IsPVM G) (e : α → β) : IsPVM (fibSum G e) :=
  h.coarse e
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

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable (m)
variable {m} [NeZero m]
theorem xIdx_injective : Function.Injective (xIdx m) := fun i j h => by
  apply Fin.ext; simpa using congrArg Fin.val h
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
/-- Only the `X` block of the padded point is read. -/
theorem sum_point_pad_x {M : Type*} [AddCommMonoid M] (g : Point F m → M) :
    ∑ u : Point F (4 * m), g (xBlk u)
      = (Fintype.card (Fin (2 * m) → F) * Fintype.card (Point F m)) • ∑ pX : Point F m, g pX := by
  rw [show (∑ u : Point F (4 * m), g (xBlk u))
      = ∑ u : Point F (4 * m), (fun pX (_ : Point F m) => g pX) (xBlk u) (zBlk u) from rfl,
    sum_point_pad (fun pX (_ : Point F m) => g pX),
    Finset.sum_congr rfl fun pX _ => Finset.sum_const (g pX), Finset.card_univ,
    Finset.sum_nsmul, smul_smul]
end
end MIPRE.QLD

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
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- The squared norm of `(S ⊗ D) ψ` for a projector `S`, as a Born probability. -/
theorem snorm_sq_aOp_mul_bOp (ψ : dA × dB → ℂ) {S : Matrix dA dA ℂ} (hsa : Sᴴ = S)
    (hidem : S * S = S) (D : Matrix dB dB ℂ) :
    snorm ψ ((aOp S : Matrix (dA × dB) _ ℂ) * bOp D) ^ 2 = bornProb ψ S (Dᴴ * D) := by
  rw [snorm_sq_eq_qform, aOp_bOp_conjTranspose, aOp_bOp_mul_aOp_bOp, hsa, hidem,
    ← bornProb_eq_qform]
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

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {RA RB : Type*} [Fintype RA]
  [DecidableEq RA] [Fintype RB] [DecidableEq RB]
variable {X' Z' : F → Matrix RB RB ℂ}
omit [Field F] in
/-- **The weights sum to the outcome's mass**: `∑_{a,b} ‖(S ⊗ X_a Z_b) Φ‖² = ⟨S ⊗ 1⟩`. -/
theorem sum_snorm_sq_ordXZ_eq (Φ : RA × RB → ℂ) {S : Matrix RA RA ℂ} (hsa : Sᴴ = S)
    (hidem : S * S = S) (hX : IsPVM X') (hZ : IsPVM Z') :
    ∑ p : F × F, snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (X' p.1 * Z' p.2)) ^ 2
      = bornProb Φ S 1 := by
  simp_rw [snorm_sq_aOp_mul_bOp Φ hsa hidem, ← sand_eq_gram hX hZ]
  rw [← bornProb_sum_right, sum_sand hX hZ]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {RA RB : Type*} [Fintype RA]
  [DecidableEq RA] [Fintype RB] [DecidableEq RB]
variable {X' Z' : F → Matrix RB RB ℂ}
/-- For `β = 0` the combination is a sub-sum of `X`. -/
theorem ordComb_ordXZ_bet_zero (hZ : IsPVM Z') (α c : F) :
    ptComb (ordXZ X' Z') α 0 c = fibSum X' (fun a => α * a) c := by
  rw [ptComb, fibSum]
  have hset : (univ.filter fun p : F × F => α * p.1 + 0 * p.2 = c)
      = (univ.filter fun a => α * a = c) ×ˢ univ := by
    ext p
    simp [Finset.mem_product]
  rw [hset, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [ordXZ]
  rw [← Matrix.mul_sum, hZ.sum_eq_one, Matrix.mul_one]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {RA RB : Type*} [Fintype RA]
  [DecidableEq RA] [Fintype RB] [DecidableEq RB]
variable {X' Z' : F → Matrix RB RB ℂ}
/-- **The combination is a contraction**: `‖(S ⊗ B) Φ‖² ≤ ⟨S ⊗ 1⟩` for every `(α, β, c)`. -/
theorem snorm_sq_ordComb_ordXZ_le (Φ : RA × RB → ℂ) {S : Matrix RA RA ℂ} (hsa : Sᴴ = S)
    (hidem : S * S = S) (hX : IsPVM X') (hZ : IsPVM Z') (α β c : F) :
    snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (ptComb (ordXZ X' Z') α β c)) ^ 2
      ≤ bornProb Φ S 1 := by
  by_cases hβ : β = 0
  · subst hβ
    rw [ordComb_ordXZ_bet_zero hZ, snorm_sq_aOp_mul_bOp Φ hsa hidem]
    have hP := isPVM_fibSum hX (fun a => α * a)
    rw [hP.isSelfAdjoint c, hP.idem c]
    exact bornProb_mono_right Φ (posSemidef_of_proj hsa hidem)
      (proj_le_one (hP.isSelfAdjoint c) (hP.idem c))
  · rw [snorm_sq_ordComb_ordXZ_of_ne Φ S hX hβ, ← sum_snorm_sq_ordXZ_eq Φ hsa hidem hX hZ]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun p _ _ => sq_nonneg _
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {RA RB : Type*} [Fintype RA]
  [DecidableEq RA] [Fintype RB] [DecidableEq RB] {X' Z' : F → Matrix RB RB ℂ}
omit [DecidableEq RA] in
/-- The order `Z_b X_a` along `(α, β)` is the order `X_a Z_b` with the roles exchanged. -/
theorem ptComb_ordZX_eq (X' Z' : F → Matrix RB RB ℂ) (α β c : F) :
    ptComb (ordZX X' Z') α β c = ptComb (ordXZ Z' X') β α c := by
  simp only [ptComb, ordZX, ordXZ]
  refine Finset.sum_equiv (Equiv.prodComm F F) (fun r => ?_) (fun r _ => ?_)
  · simp only [mem_filter, mem_univ, true_and, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [add_comm]
  · simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
omit [Fintype F] [DecidableEq F] in
theorem isLinAB_of_isGood {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)} (hg : IsGood g) :
    IsLinAB g := by
  intro e hpat
  by_contra hne
  rcases hg e hne with ⟨h1, h0, _⟩ | ⟨h0, h1, _⟩
  · exact hpat (Or.inl ⟨h1, h0⟩)
  · exact hpat (Or.inr ⟨h0, h1⟩)
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
omit [Fintype F] [DecidableEq F] in
theorem notMem_xSet_iff {k : Fin (4 * m)} : k ∉ xSet ↔ ∀ j, xIdx m j ≠ k := by
  rw [xSet, Finset.mem_image]
  push Not
  exact ⟨fun h j => h j (mem_univ j), fun h j _ => h j⟩
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
omit [Fintype F] [DecidableEq F] in
theorem eval_gX (hd : 1 ≤ d) {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)} (hg : IsGood g)
    (u : Point F (4 * m)) : (gX hd g).eval (xBlk u) = (gA hd g).eval u := by
  refine LowIndDegPoly.eval_blockPoly xIdx_injective (fun e he k hk => ?_) u
  by_contra hne
  exact not_depOutside_gA_of_isGood hd hg ⟨e, he, k, notMem_xSet_iff.mpr hk, hne⟩
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
omit [Fintype F] in
theorem pairOf_of_isGood (hd : 1 ≤ d) {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)}
    (hg : IsGood g) : pairOf hd g = (gX hd g, gZ hd g) := if_pos hg
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]
/-- The `x` block of a uniform padded point is uniform. -/
theorem sum_uniform_xBlk (f : Point F m → ℝ) :
    ∑ u, uniform (Point F (4 * m)) u * f (xBlk u) = ∑ x, uniform (Point F m) x * f x := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [uniform, ← Finset.mul_sum]
  rw [sum_point_pad_x, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
  push_cast
  rw [show 4 * m = 2 * m + m + m by ring, pow_add, pow_add]
  field_simp
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
theorem _root_.solution (hd : 1 ≤ d) {Φ : RA × RB → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix RA RA ℂ))
    (hX : ∀ x, IsPVM (X x)) (hZ : ∀ z, IsPVM (Z z)) {Δ δG : ℝ}
    (hprod : ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - ordComb ordZX X Z u (g.eval u))) ^ 2
      ≤ Δ)
    (hbad : ∑ g ∈ univ.filter (fun g => ¬ IsGood g), bornProb Φ (G.M () g) 1 ≤ δG) :
    1 - 2 * Real.sqrt Δ - 2 / Fintype.card F - δG
      ≤ ∑ x, uniform (Point F m) x
          * ∑ g, bornProb Φ (G.M () g) (X x ((PolyPair.proj .X (pairOf hd g)).eval x)) := by
  have hsa : ∀ g, (G.M () g)ᴴ = G.M () g := fun g => G.selfAdjoint () g
  have hidem : ∀ g, G.M () g * G.M () g = G.M () g := fun g => G.projective () g
  have hW0 : ∀ g, 0 ≤ bornProb Φ (G.M () g) 1 := fun g =>
    bornProb_nonneg Φ (posSemidef_of_proj (hsa g) (hidem g)) Matrix.PosSemidef.one
  have hq0 : (0 : ℝ) ≤ 2 / Fintype.card F := by positivity
  have h1 := one_sub_two_sqrt_le_sum_snorm_sq hΦ G (ordComb ordZX X Z) hprod
  have hswap : ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (ordComb ordZX X Z u (g.eval u))) ^ 2
      = ∑ g, ∑ u, uniform (Point F (4 * m)) u * snorm Φ
        ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (ordComb ordZX X Z u (g.eval u))) ^ 2 := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  have hg : ∀ g, ∑ u, uniform (Point F (4 * m)) u * snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (ordComb ordZX X Z u (g.eval u))) ^ 2
      ≤ 2 / Fintype.card F * bornProb Φ (G.M () g) 1
        + ∑ x, uniform (Point F m) x
          * bornProb Φ (G.M () g) (X x ((PolyPair.proj .X (pairOf hd g)).eval x))
        + (if IsGood g then (0 : ℝ) else bornProb Φ (G.M () g) 1) := by
    intro g
    have hM0 : 0 ≤ ∑ x, uniform (Point F m) x
        * bornProb Φ (G.M () g) (X x ((PolyPair.proj .X (pairOf hd g)).eval x)) :=
      Finset.sum_nonneg fun x _ => mul_nonneg (uniform_nonneg _ _)
        (bornProb_nonneg Φ (posSemidef_of_proj (hsa g) (hidem g)) ((hX x).posSemidef _))
    by_cases hgood : IsGood g
    · rw [if_pos hgood, add_zero]
      have h := sum_uniform_snorm_sq_ordComb_ZX_le_of_isLinAB hd Φ (hsa g) (hidem g) hX hZ
        (isLinAB_of_isGood hgood)
      have hre : ∀ u₀ : Point F (4 * m), bornProb Φ (G.M () g) (X (xBlk u₀) ((gA hd g).eval u₀))
          = bornProb Φ (G.M () g)
            (X (xBlk u₀) ((PolyPair.proj .X (pairOf hd g)).eval (xBlk u₀))) := fun u₀ => by
        rw [pairOf_of_isGood hd hgood, PolyPair.proj_X, eval_gX hd hgood]
      simp_rw [hre] at h
      rw [sum_uniform_xBlk (fun x => bornProb Φ (G.M () g)
        (X x ((PolyPair.proj .X (pairOf hd g)).eval x)))] at h
      exact h
    · rw [if_neg hgood]
      have hle : ∀ u : Point F (4 * m), snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
          * bOp (ordComb ordZX X Z u (g.eval u))) ^ 2 ≤ bornProb Φ (G.M () g) 1 := fun u => by
        rw [ordComb, ptComb_ordZX_eq]
        exact snorm_sq_ordComb_ordXZ_le Φ (hsa g) (hidem g) (hZ _) (hX _) _ _ _
      calc _ ≤ ∑ u, uniform (Point F (4 * m)) u * bornProb Φ (G.M () g) 1 :=
            Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hle u) (uniform_nonneg _ _)
        _ = bornProb Φ (G.M () g) 1 := by rw [← Finset.sum_mul, sum_uniform_eq_one, one_mul]
        _ ≤ _ := by nlinarith [mul_nonneg hq0 (hW0 g)]
  have hsumg := Finset.sum_le_sum fun g (_ : g ∈ univ) => hg g
  have hA : ∑ g, 2 / Fintype.card F * bornProb Φ (G.M () g) 1 = 2 / Fintype.card F := by
    rw [← Finset.mul_sum, sum_bornProb_M_one hΦ G, mul_one]
  have hB : ∑ g, ∑ x, uniform (Point F m) x
      * bornProb Φ (G.M () g) (X x ((PolyPair.proj .X (pairOf hd g)).eval x))
      = ∑ x, uniform (Point F m) x
        * ∑ g, bornProb Φ (G.M () g) (X x ((PolyPair.proj .X (pairOf hd g)).eval x)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
  have hC : ∑ g, (if IsGood g then (0 : ℝ) else bornProb Φ (G.M () g) 1)
      = ∑ g ∈ univ.filter (fun g => ¬ IsGood g), bornProb Φ (G.M () g) 1 := by
    rw [Finset.sum_filter]
    simp only [ite_not]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB, hC] at hsumg
  linarith
end MIPRE.QLD
