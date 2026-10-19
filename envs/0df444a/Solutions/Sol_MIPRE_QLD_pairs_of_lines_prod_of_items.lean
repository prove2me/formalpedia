-- Prove2me | solution 1 for MIPRE.QLD.pairs_of_lines_prod_of_items
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:42:09.735005+00:00
-- url     : https://prove2.me/submissions/5da362bb-d9ce-434b-b87d-3a4a032da3c2

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Product.lean (solution of MIPRE.QLD.pairs_of_lines_prod_of_items);
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
import Definitions.Def_MIPRE_Background_QLD_Product
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_QLD_avg_pair_eq_content_X
import Theorems.Thm_MIPRE_QLD_avg_pair_eq_content_X_collProb
import Theorems.Thm_MIPRE_QLD_avg_pair_eq_content_X_self
import Theorems.Thm_MIPRE_QLD_avg_pair_eq_content_Z
import Theorems.Thm_MIPRE_QLD_combined_points_pts
import Theorems.Thm_MIPRE_QLD_hatPOVM_consistency
import Theorems.Thm_MIPRE_QLD_pairs_of_lines_gen
import Theorems.Thm_MIPRE_QLD_sum_content_marg_line_le
import Theorems.Thm_MIPRE_QLD_sum_content_normSq_point_line_le
import Theorems.Thm_MIPRE_Weyl_isPVM_synOf
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_ancillaEmbed_isometry
import Theorems.Thm_MIPRE_avg_comp_equiv_fst
import Theorems.Thm_MIPRE_bornProb_nonneg
import Theorems.Thm_MIPRE_kron_one_mul_ancillaEmbed
import Theorems.Thm_MIPRE_kronecker_sum_right
import Theorems.Thm_MIPRE_normSq_stateVecB_extVec2_aOp
import Theorems.Thm_MIPRE_sum_bornProb
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
/-- **The squared state norm is the quadratic form of `M† M`.** -/
theorem snorm_sq_eq_qform (M : Matrix N N ℂ) : snorm v M ^ 2 = qform v (Mᴴ * M) := by
  rw [snorm, norm_evec_mulVec_sq, qform]
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
variable [DecidableEq dA]
/-- The inner product of the two factors' vectors is the blueprint's `⟨ψ| Q ⊗ R |ψ⟩`, for
self-adjoint `Q`. -/
theorem inner_stateVec_stateVecB (ψ : dA × dB → ℂ) {Q : Matrix dA dA ℂ} (hQ : Qᴴ = Q)
    (R : Matrix dB dB ℂ) :
    inner ℂ (stateVec ψ Q) (stateVecB ψ R) = star ψ ⬝ᵥ ((Q ⊗ₖ R) *ᵥ ψ) := by
  classical
  have hadj : (Q ⊗ₖ (1 : Matrix dB dB ℂ))ᴴ * ((1 : Matrix dA dA ℂ) ⊗ₖ R) = Q ⊗ₖ R := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, Matrix.one_mul, hQ]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  show ((1 : Matrix dA dA ℂ) ⊗ₖ R) *ᵥ ψ ⬝ᵥ star ((Q ⊗ₖ (1 : Matrix dB dB ℂ)) *ᵥ ψ) = _
  rw [dotProduct_comm, star_mulVec_dotProduct, hadj]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
theorem condWin_le_one (hψ : star ψ ⬝ᵥ ψ = 1) (x : X) (y : Y) :
    condWin G ψ MA MB x y ≤ 1 := by
  rw [← sum_bornProb hψ (MA x) (MB y)]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  have hb : 0 ≤ bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) :=
    bornProb_nonneg ψ ((MA x).posSemidef a) ((MB y).posSemidef b)
  by_cases h : G.D x y a b
  · rw [if_pos h, one_mul]
  · rw [if_neg h, zero_mul]
    exact hb
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
theorem condFail_nonneg (hψ : star ψ ⬝ᵥ ψ = 1) (x : X) (y : Y) :
    0 ≤ condFail G ψ MA MB x y :=
  sub_nonneg.mpr (condWin_le_one hψ x y)
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
/-- **The failure probability is the average of the conditional failures.** -/
theorem one_sub_povmValue_eq :
    1 - povmValue G ψ MA MB = ∑ x, ∑ y, G.μ x y * condFail G ψ MA MB x y := by
  have h : ∑ x, ∑ y, G.μ x y * condFail G ψ MA MB x y
      = (∑ x, ∑ y, G.μ x y) - ∑ x, ∑ y, G.μ x y * condWin G ψ MA MB x y := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by rw [condFail]; ring
  rw [h, G.μ_sum_one, povmValue]
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
omit [DecidableEq dA] in
theorem norm_stateVec_eq_snorm (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) :
    ‖stateVec ψ A‖ = snorm ψ (aOp A : Matrix (dA × dB) _ ℂ) := rfl
end
end MIPRE

namespace MIPRE
section
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder
/-- Pulling a Born-rule expectation back along a linear map `W` conjugates the observable:
`⟨Wv| M |Wv⟩ = ⟨v| Wᴴ M W |v⟩`. With `W` an isometry and `M` a projection this is how a
dilated projective measurement compresses back to the POVM it came from. -/
theorem dotProduct_mulVec_conj {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W : Matrix κ ι ℂ) (M : Matrix κ κ ℂ) (v : ι → ℂ) :
    star (W *ᵥ v) ⬝ᵥ (M *ᵥ (W *ᵥ v)) = star v ⬝ᵥ ((Wᴴ * (M * W)) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec]
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

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']
/-- **A product of projective POVMs is projective**, in the `POVM.kron` form the expansion uses. -/
theorem isPVM_povm_kron {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (P : POVM ι dA) (Q : POVM κ anc) (hP : IsPVM fun i => ((P.mats i).val))
    (hQ : IsPVM fun j => ((Q.mats j).val)) :
    IsPVM fun p => (((P.kron Q).mats p).val) :=
  isPVM_kron hP hQ
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
theorem stateSqNorm_eq_qform (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    stateSqNorm ψ M = qform ψ ((aOp (Mᴴ * M) : Matrix (dA × dB) _ ℂ)) := by
  rw [stateSqNorm, stateNorm, norm_stateVec_eq_snorm, snorm_sq_eq_qform, aOp_conjTranspose,
    ← aOp_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **Expanding a cross-party deviation.** -/
theorem xSqNorm_eq_expand (ψ : dA × dB → ℂ) {A : Matrix dA dA ℂ} (hA : Aᴴ = A)
    (B : Matrix dB dB ℂ) :
    xSqNorm ψ A B = stateSqNorm ψ A + ‖stateVecB ψ B‖ ^ 2 - 2 * bornProb ψ A B := by
  rw [xSqNorm, norm_sub_sq (𝕜 := ℂ), inner_stateVec_stateVecB ψ hA, stateSqNorm, stateNorm,
    bornProb]
  simp only [RCLike.re_to_complex]
  ring
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {Anc Bnc : Type*} [Fintype Anc] [DecidableEq Anc] [Fintype Bnc] [DecidableEq Bnc]
/-- **The Born rule on the twice-extended state is the Born rule of the two compressions.** -/
theorem bornProb_extVec2 (ψ : dA × dB → ℂ) (a₀ : Anc) (b₀ : Bnc)
    (EA : Matrix (dA × Anc) (dA × Anc) ℂ) (EB : Matrix (dB × Bnc) (dB × Bnc) ℂ) :
    bornProb (extVec2 ψ a₀ b₀) EA EB
      = bornProb ψ ((ancillaEmbed dA a₀)ᴴ * (EA * ancillaEmbed dA a₀))
          ((ancillaEmbed dB b₀)ᴴ * (EB * ancillaEmbed dB b₀)) := by
  rw [bornProb, bornProb, extVec2, dotProduct_mulVec_conj]
  congr 2
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {Anc Bnc : Type*} [Fintype Anc] [DecidableEq Anc] [Fintype Bnc] [DecidableEq Bnc]
theorem qform_aOp_extVec2 (ψ : dA × dB → ℂ) (a₀ : Anc) (b₀ : Bnc)
    (EA : Matrix (dA × Anc) (dA × Anc) ℂ) :
    qform (extVec2 ψ a₀ b₀) (aOp EA)
      = qform ψ ((aOp ((ancillaEmbed dA a₀)ᴴ * (EA * ancillaEmbed dA a₀))
          : Matrix (dA × dB) _ ℂ)) := by
  rw [show qform (extVec2 ψ a₀ b₀) (aOp EA)
      = bornProb (extVec2 ψ a₀ b₀) EA (1 : Matrix (dB × Bnc) (dB × Bnc) ℂ) from by
    rw [bornProb_eq_qform, bOp_one, Matrix.mul_one], bornProb_extVec2, Matrix.one_mul,
    ancillaEmbed_isometry, bornProb_eq_qform, bOp_one, Matrix.mul_one]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {Anc Bnc : Type*} [Fintype Anc] [DecidableEq Anc] [Fintype Bnc] [DecidableEq Bnc]
/-- An operator with an inert ancilla compresses to itself. -/
theorem compress_aOp (b₀ : Bnc) (N : Matrix dB dB ℂ) :
    (ancillaEmbed dB b₀)ᴴ * ((aOp N : Matrix (dB × Bnc) _ ℂ) * ancillaEmbed dB b₀) = N := by
  rw [aOp, kron_one_mul_ancillaEmbed,
    ← Matrix.mul_assoc ((ancillaEmbed dB b₀)ᴴ) (ancillaEmbed dB b₀) N, ancillaEmbed_isometry,
    Matrix.one_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {Anc Bnc : Type*} [Fintype Anc] [DecidableEq Anc] [Fintype Bnc] [DecidableEq Bnc]
theorem xSqNorm_extVec2_aOp (ψ : dA × dB → ℂ) (a₀ : Anc) (b₀ : Bnc) {P : Matrix dA dA ℂ}
    (hP : Pᴴ = P) (Q : Matrix dB dB ℂ) :
    xSqNorm (extVec2 ψ a₀ b₀) (aOp P : Matrix (dA × Anc) _ ℂ) (aOp Q : Matrix (dB × Bnc) _ ℂ)
      = xSqNorm ψ P Q := by
  rw [xSqNorm_eq_expand _ (by rw [aOp_conjTranspose, hP] :
      (aOp P : Matrix (dA × Anc) _ ℂ)ᴴ = aOp P) _,
    xSqNorm_eq_expand ψ hP Q, normSq_stateVecB_extVec2_aOp,
    show stateSqNorm (extVec2 ψ a₀ b₀) (aOp P : Matrix (dA × Anc) _ ℂ) = stateSqNorm ψ P from by
      rw [stateSqNorm_eq_qform, aOp_conjTranspose, ← aOp_mul, qform_aOp_extVec2, compress_aOp,
        ← stateSqNorm_eq_qform],
    show bornProb (extVec2 ψ a₀ b₀) (aOp P : Matrix (dA × Anc) _ ℂ)
          (aOp Q : Matrix (dB × Bnc) _ ℂ) = bornProb ψ P Q from by
      rw [bornProb_extVec2, compress_aOp, compress_aOp]]
end
end MIPRE

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- The coarse-grained basis measurement is projective. -/
theorem isPVM_synOfPOVM {C : Type*} [Fintype C] [DecidableEq C] (W : Bas) (φ : Anc F m → C) :
    IsPVM fun o => (((synOfPOVM W φ).mats o).val) :=
  isPVM_synOf (isWeylFamily_weylOf W) φ
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **The hatted line measurement is projective** whenever the strategy's own line measurement is.
Projectivity is closed under products and under coarse-graining, and that is all the convolution
is; the paper checks the same thing by hand. -/
theorem isPVM_hatLinePOVM {d' : Type} [Fintype d'] [DecidableEq d'] {n : ℕ}
    {hm : m ∣ Fintype.card F} {M : Question F m → POVM (Answer F m d) d'} {W : Bas} {ty : Ty}
    {base dir : Content F m → Point F m} {c : Content F m}
    (hM : IsPVM fun a => (((M (c.question hm ty)).mats a).val)) :
    IsPVM fun f => (((hatLinePOVM n hm M W ty base dir c).mats f).val) :=
  isPVM_povm_map _ (isPVM_povm_kron _ _ (isPVM_povm_map _ hM _) (isPVM_synOfPOVM W _)) _
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [Algebra (ZMod 2) F] in
theorem Content.omega_pt (c : Content F m) (W : Bas) : c.omega.pt W = c.pt W := by
  cases W <;> rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem hatPOVM_eq {d' : Type} [Fintype d'] [DecidableEq d'] (hm : m ∣ Fintype.card F)
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (c : Content F m) :
    hatPOVM hm M W c = hatPtPOVM M W (c.pt W) := by
  rw [hatPOVM, ptValPOVM, Content.omega_pt, hatPtPOVM]
  rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
/-- `lem:qld-expanded-points`'s first item, re-indexed by the point. -/
theorem hatPOVM_mats_eq {d' : Type} [Fintype d'] [DecidableEq d'] (hm : m ∣ Fintype.card F)
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (c : Content F m) (a : F) :
    (((hatPOVM hm M W c).mats a).val) = hatMats M W (c.pt W) a := by
  rw [hatPOVM_eq hm M W c]
  rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
theorem sum_content_hatMats_consistency (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA W (c.pt W) a)
          (hatMats MB W (c.pt W) a)
      ≤ 172 * ε := by
  have h := hatPOVM_consistency (MB := MB) hψ hfail W
  rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) =>
    congrArg (fun t : ℝ => (Fintype.card (Content F m) : ℝ)⁻¹ * t)
      (Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
        rw [hatPOVM_mats_eq hm MA W c a, hatPOVM_mats_eq hm MB W c a])] at h
  exact h
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ} [NeZero m]
instance : Nonempty (Content F m) := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩
end
end MIPRE.QLD

namespace MIPRE.QLD.LinePres
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {hm : m ∣ Fintype.card F} {W : Bas}
theorem isPVM_lineMats {d' : Type} [Fintype d'] [DecidableEq d'] (P : LinePres F m hm W) (d : ℕ)
    {M : Question F m → POVM (Answer F m d) d'}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (c : Content F m) :
    IsPVM (P.lineMats d M c) :=
  isPVM_hatLinePOVM (hM (c.question hm P.ty))
end
end MIPRE.QLD.LinePres

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
instance : Nonempty (LPData F m) := ⟨⟨0, 0, 0⟩⟩
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]
variable [Algebra (ZMod 2) F] {hm : m ∣ Fintype.card F}
theorem pairShift_add (w w' : Point F m) (p : LPData F m × LPData F m) :
    pairShift w' (pairShift w p) = pairShift (w + w') p := by
  rw [pairShift, pairShift, pairShift, add_assoc]
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
/-- **A quantity of the two points has the same law under a content as under a uniform pair of
points.** -/
theorem avg_content_eq_pts (H : Point F m → Point F m → ℝ) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * H c.uX c.uZ
      = ∑ x : Point F m × Point F m, (Fintype.card (Point F m × Point F m) : ℝ)⁻¹ * H x.1 x.2 :=
  avg_comp_equiv_fst contentSplitPts (fun q => H q.1 q.2)
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
/-- **`lem:qld-pairs-of-lines`, on a product of two independent line-point laws.** The instance of
`pairs_of_lines_gen` at `kX = pairCX`, `kZ = pairCZ`, `sh = pairShift`: this is the form
`lem:qld-padded-lines` needs, where the `X` line and the `Z` line are drawn independently. -/
theorem pairs_of_lines_prod (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    {QA : LPData F m × LPData F m → F × F →
      Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ}
    (hQA : ∀ p, IsPVM (QA p)) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) {δ η εc : ℝ}
    (hmargX : ∑ p : LPData F m × LPData F m,
        (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * ∑ x : F,
          xSqNorm (extHat (m := m) ψ) (∑ q : F, QA p (x, q))
            (aOp (PX.lineEvalMats d MB (pairCX p) x)) ≤ δ)
    (hmargZ : ∑ p : LPData F m × LPData F m,
        (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * ∑ b : F,
          xSqNorm (extHat (m := m) ψ) (∑ q : F, QA p (q, b))
            (aOp (PZ.lineEvalMats d MB (pairCZ p) b)) ≤ δ)
    (hselfX : ∑ p : LPData F m × LPData F m,
        (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ *
          ∑ f : LinePoly F (m * d), xSqNorm (extHat (m := m) ψ)
            (aOp (PX.lineMats d MA (pairCX p) f)) (aOp (PX.lineMats d MB (pairCX p) f)) ≤ η)
    (hcoll : ∑ p : LPData F m × LPData F m,
        (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * collProb PX d (pairCX p) ≤ εc) :
    1 - ∑ p : LPData F m × LPData F m,
        (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * ∑ r : F × F,
          bornProb (extHat (m := m) ψ) (QA p r)
            (∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
                LinePoly.eval q.1 (PX.param (pairCX p)) = r.1
                  ∧ LinePoly.eval q.2 (PZ.param (pairCZ p)) = r.2,
              pasteLine PX PZ d MB (pairCX p) (pairCZ p) q)
      ≤ δ / 2 + Real.sqrt (δ / 2) + Real.sqrt (32 * δ + 4 * Real.sqrt η + 2 * εc) :=
  pairs_of_lines_gen PX PZ pairCX pairCZ (sh := pairShift) pairShift_zero pairShift_add
    pairCX_pairShift pairCZ_pairShift hQA hψ hprojA hprojB hmargX hmargZ hselfX hcoll
end
end MIPRE.QLD

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]
variable [Algebra (ZMod 2) F] {hm : m ∣ Fintype.card F}
variable {d : ℕ} {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {ε : ℝ}
set_option maxHeartbeats 1600000 in
theorem _root_.solution (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
    (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    (hfacX : FactorsX PX) (hfacZ : FactorsZ PZ)
    (hX1 : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ f : LinePoly F (m * d),
        xSqNorm (hatVec (F := F) (m := m) ψ) (PX.lineMats d MA c f)
          (PX.lineMats d MB c f) ≤ 172 * ε)
    (hX2 : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA .X (c.pt .X) a)
          (PX.lineEvalMats d MB c a) ≤ 172 * ε)
    (hZ2 : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ b : F,
        xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA .Z (c.pt .Z) b)
          (PZ.lineEvalMats d MB c b) ≤ 172 * ε)
    {εc : ℝ} (hcoll : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
      collProb PX d c ≤ εc) :
    ∃ QA : LPData F m × LPData F m → F × F →
        Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ,
      (∀ p, IsPVM (QA p))
      ∧ (∀ p r, (ancillaEmbed (dA × Anc F m) ((0 : F), (0 : F)))ᴴ
            * (QA p r * ancillaEmbed (dA × Anc F m) ((0 : F), (0 : F)))
          = sand (hatMats MA .X p.1.pt) (hatMats MA .Z p.2.pt) r)
      ∧ 1 - ∑ p : LPData F m × LPData F m,
          (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * ∑ r : F × F,
          bornProb (extHat (m := m) ψ) (QA p r)
            (∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
                LinePoly.eval q.1 (PX.param (pairCX p)) = r.1
                  ∧ LinePoly.eval q.2 (PZ.param (pairCZ p)) = r.2,
              pasteLine PX PZ d MB (pairCX p) (pairCZ p) q)
        ≤ deltaPairs ε εc := by
  classical
  have hε0 : 0 ≤ ε := le_trans (by
    rw [one_sub_povmValue_eq]
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg ((qldGame hm).μ_nonneg x y) (condFail_nonneg hψ x y)) hfail
  obtain ⟨QA0, QB0, hPA, hPB, hkA, hkB, h1, h6, h7⟩ :=
    combined_points_pts (MA := MA) (MB := MB) hψ hfail hprojA hprojB
  refine ⟨fun p => QA0 (p.1.pt, p.2.pt), fun p => hPA _, fun p r => hkA (p.1.pt, p.2.pt) r, ?_⟩
  -- the two ordered-product bounds, read back at the content distribution
  have h6c : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ r : F × F,
      xSqNorm (extHat (m := m) ψ) (QA0 (c.uX, c.uZ) r)
        (aOp (hatMats MB .Z c.uZ r.2 * hatMats MB .X c.uX r.1))
      ≤ 4 * deltaQ ε + 115352832 * ε :=
    le_trans (le_of_eq (avg_content_eq_pts (F := F) (m := m) fun x z =>
      ∑ r : F × F, xSqNorm (extHat (m := m) ψ) (QA0 (x, z) r)
        (aOp (hatMats MB .Z z r.2 * hatMats MB .X x r.1)))) h6
  have h7c : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ r : F × F,
      xSqNorm (extHat (m := m) ψ) (QA0 (c.uX, c.uZ) r)
        (aOp (hatMats MB .X c.uX r.1 * hatMats MB .Z c.uZ r.2))
      ≤ 4 * deltaQ ε + 461411328 * ε :=
    le_trans (le_of_eq (avg_content_eq_pts (F := F) (m := m) fun x z =>
      ∑ r : F × F, xSqNorm (extHat (m := m) ψ) (QA0 (x, z) r)
        (aOp (hatMats MB .X x r.1 * hatMats MB .Z z r.2)))) h7
  -- Bob's point measurement against his own line measurement, on each side
  have hptX := sum_content_normSq_point_line_le (MA := MA) .X PX
    (sum_content_hatMats_consistency (MB := MB) hψ hfail .X) hX2
  have hptZ := sum_content_normSq_point_line_le (MA := MA) .Z PZ
    (sum_content_hatMats_consistency (MB := MB) hψ hfail .Z) hZ2
  -- the two marginal consistencies, at the content distribution
  have hmargXc := sum_content_marg_line_le (MB := MB) .X PX
    (QA := fun c : Content F m => QA0 (c.uX, c.uZ)) (fun c => hPA _) hprojB
    (κ := kappaPairs ε) (η := 2 * (172 * ε) + 2 * (172 * ε))
    (le_trans h6c (by rw [kappaPairs]; nlinarith)) hptX
  have hmargZc := sum_content_marg_line_le (MB := MB) .Z PZ
    (QA := fun c : Content F m => QA0 (c.uX, c.uZ)) (fun c => hPA _) hprojB
    (κ := kappaPairs ε) (η := 2 * (172 * ε) + 2 * (172 * ε))
    (le_trans h7c (le_of_eq (show 4 * deltaQ ε + 461411328 * ε = kappaPairs ε from by
      rw [kappaPairs]))) hptZ
  -- ... read on the product
  have hmargX : ∑ p : LPData F m × LPData F m,
      (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * ∑ a : F,
        xSqNorm (extHat (m := m) ψ) (∑ q : F, QA0 (p.1.pt, p.2.pt) (a, q))
          (aOp (PX.lineEvalMats d MB (pairCX p) a))
      ≤ 2 * (10 * kappaPairs ε) + 2 * (2 * (172 * ε) + 2 * (172 * ε)) :=
    le_trans (le_of_eq (avg_pair_eq_content_X hfacX fun x z A =>
      ∑ a : F, xSqNorm (extHat (m := m) ψ) (∑ q : F, QA0 (x, z) (a, q)) (aOp (A a)))) hmargXc
  have hmargZ : ∑ p : LPData F m × LPData F m,
      (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * ∑ b : F,
        xSqNorm (extHat (m := m) ψ) (∑ q : F, QA0 (p.1.pt, p.2.pt) (q, b))
          (aOp (PZ.lineEvalMats d MB (pairCZ p) b))
      ≤ 2 * (10 * kappaPairs ε) + 2 * (2 * (172 * ε) + 2 * (172 * ε)) :=
    le_trans (le_of_eq (avg_pair_eq_content_Z hfacZ fun x z A =>
      ∑ b : F, xSqNorm (extHat (m := m) ψ) (∑ q : F, QA0 (x, z) (q, b)) (aOp (A b)))) hmargZc
  -- the fine self-consistency, transported to the enlarged space and then to the product
  have hselfc : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
      ∑ f : LinePoly F (m * d), xSqNorm (extHat (m := m) ψ) (aOp (PX.lineMats d MA c f))
        (aOp (PX.lineMats d MB c f)) ≤ 172 * ε := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ =>
      congrArg (fun t : ℝ => (Fintype.card (Content F m) : ℝ)⁻¹ * t)
        (Finset.sum_congr rfl fun f _ => ?_))) hX1
    rw [extHat, xSqNorm_extVec2_aOp _ _ _
      ((PX.isPVM_lineMats d hprojA c).isSelfAdjoint f)]
  have hself : ∑ p : LPData F m × LPData F m,
      (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * ∑ f : LinePoly F (m * d),
        xSqNorm (extHat (m := m) ψ) (aOp (PX.lineMats d MA (pairCX p) f))
          (aOp (PX.lineMats d MB (pairCX p) f)) ≤ 172 * ε :=
    le_trans (le_of_eq (avg_pair_eq_content_X_self hfacX fun A B =>
      ∑ f : LinePoly F (m * d), xSqNorm (extHat (m := m) ψ) (aOp (A f)) (aOp (B f)))) hselfc
  have hcollp : ∑ p : LPData F m × LPData F m,
      (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * collProb PX d (pairCX p) ≤ εc :=
    le_trans (le_of_eq (avg_pair_eq_content_X_collProb hfacX)) hcoll
  exact le_trans (pairs_of_lines_prod PX PZ (fun p => hPA _) hψ hprojA hprojB
    hmargX hmargZ hself hcollp) (le_of_eq (by rw [deltaPairs, deltaPairsD]))
end MIPRE.QLD
