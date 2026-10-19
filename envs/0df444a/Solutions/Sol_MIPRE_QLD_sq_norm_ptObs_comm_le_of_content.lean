-- Prove2me | solution 1 for MIPRE.QLD.sq_norm_ptObs_comm_le_of_content
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:45:15.937176+00:00
-- url     : https://prove2.me/submissions/3d84e434-4393-4602-8ce1-59eb19e4e38f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Commutation.lean (solution of MIPRE.QLD.sq_norm_ptObs_comm_le_of_content);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
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
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_POVM_sub_mul_self_le_one
import Theorems.Thm_MIPRE_POVM_sum_mats_map_prod
import Theorems.Thm_MIPRE_POVM_sum_mats_map_prod_prime
import Theorems.Thm_MIPRE_QLD_exists_projective_of_nearProjective
import Theorems.Thm_MIPRE_QLD_one_sub_two_mul_lt_sum_stateSqNorm
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_aOp_sub
import Theorems.Thm_MIPRE_bornProb_nonneg
import Theorems.Thm_MIPRE_commutation_analysis
import Theorems.Thm_MIPRE_norm_stateVec_comm_le
import Theorems.Thm_MIPRE_obs2_commutator_eq
import Theorems.Thm_MIPRE_sq_sum_le_card_mul_sum_sq
import Theorems.Thm_MIPRE_sum_xSqNorm_le_of_two_step

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
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem stateVec_sum {ι : Type*} (ψ : dA × dB → ℂ) (s : Finset ι) (f : ι → Matrix dA dA ℂ) :
    stateVec ψ (∑ i ∈ s, f i) = ∑ i ∈ s, stateVec ψ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, stateVec_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem stateNorm_nonneg (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) : 0 ≤ stateNorm ψ M :=
  norm_nonneg _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
/-- The difference of two POVM elements is self-adjoint. -/
theorem POVM.sub_conjTranspose {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d]
    (M : POVM A d) (p q : A) :
    (((M.mats p).val - (M.mats q).val))ᴴ = ((M.mats p).val - (M.mats q).val) := by
  rw [Matrix.conjTranspose_sub, ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose,
    (M.mats p).2, (M.mats q).2]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem xSqNorm_nonneg (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    0 ≤ xSqNorm ψ A B := by rw [xSqNorm]; positivity
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
theorem xNorm_nonneg (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    0 ≤ xNorm ψ A B := norm_nonneg _
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
omit [DecidableEq dA] in
theorem norm_stateVec_eq_snorm (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) :
    ‖stateVec ψ A‖ = snorm ψ (aOp A : Matrix (dA × dB) _ ℂ) := rfl
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
omit [DecidableEq dB] in
theorem norm_stateVecB_eq_snorm (ψ : dA × dB → ℂ) (B : Matrix dB dB ℂ) :
    ‖stateVecB ψ B‖ = snorm ψ (bOp B : Matrix (dA × dB) _ ℂ) := rfl
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
theorem stateSqNorm_sub_comm (ψ : dA × dB → ℂ) (M N : Matrix dA dA ℂ) :
    stateSqNorm ψ (M - N) = stateSqNorm ψ (N - M) := by
  rw [stateSqNorm, stateSqNorm, stateNorm, stateNorm, norm_stateVec_eq_snorm,
    norm_stateVec_eq_snorm, aOp_sub, aOp_sub, snorm_sub_comm]
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
theorem norm_stateVecB_sub_comm (ψ : dA × dB → ℂ) (M N : Matrix dB dB ℂ) :
    ‖stateVecB ψ (M - N)‖ = ‖stateVecB ψ (N - M)‖ := by
  rw [norm_stateVecB_eq_snorm, norm_stateVecB_eq_snorm, bOp_sub, bOp_sub, snorm_sub_comm]
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
/-- Pushing a sum inside a deviation costs the number of terms. -/
theorem stateSqNorm_sum_le {κ : Type*} [Fintype κ] (ψ : dA × dB → ℂ) (f : κ → Matrix dA dA ℂ) :
    stateSqNorm ψ (∑ k, f k) ≤ (Fintype.card κ : ℝ) * ∑ k, stateSqNorm ψ (f k) := by
  have h1 : stateNorm ψ (∑ k, f k) ≤ ∑ k, stateNorm ψ (f k) := by
    rw [stateNorm, stateVec_sum]
    exact le_trans (norm_sum_le _ _) (le_of_eq rfl)
  calc stateSqNorm ψ (∑ k, f k) = stateNorm ψ (∑ k, f k) ^ 2 := rfl
    _ ≤ (∑ k, stateNorm ψ (f k)) ^ 2 := pow_le_pow_left₀ (stateNorm_nonneg ψ _) h1 2
    _ ≤ (Fintype.card κ : ℝ) * ∑ k, stateNorm ψ (f k) ^ 2 :=
        sq_sum_le_card_mul_sum_sq _ fun k => stateNorm_nonneg ψ _
    _ = (Fintype.card κ : ℝ) * ∑ k, stateSqNorm ψ (f k) := rfl
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
theorem obs2_conjTranspose {d : Type*} [Fintype d] [DecidableEq d] (P : POVM (ZMod 2) d) :
    (obs2 P)ᴴ = obs2 P := POVM.sub_conjTranspose P 0 1
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
theorem obs2_mul_self_le_one {d : Type*} [Fintype d] [DecidableEq d] (P : POVM (ZMod 2) d) :
    (obs2 P)ᴴ * obs2 P ≤ (1 : Matrix d d ℂ) := by
  rw [obs2_conjTranspose]
  exact POVM.sub_mul_self_le_one P 0 1
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
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
/-- **The swap exchanges the two sides of a cross-party deviation.** -/
theorem snorm_swapVec_aOp_sub_bOp (ψ : dA × dB → ℂ) (X : Matrix dB dB ℂ)
    (Y : Matrix dA dA ℂ) :
    snorm (swapVec ψ) ((aOp X : Matrix (dB × dA) (dB × dA) ℂ) - bOp Y) = xNorm ψ Y X := by
  rw [snorm, Matrix.sub_mulVec, aOp, bOp, mulVec_kronecker_swapVec, mulVec_kronecker_swapVec,
    ← swapVec_sub, norm_swapVec, xNorm_eq_snorm, snorm, Matrix.sub_mulVec, aOp, bOp,
    evec_sub, evec_sub, norm_sub_rev]
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
omit [DecidableEq dB] in
/-- The same for a single operator on Bob's factor. -/
theorem snorm_swapVec_aOp (ψ : dA × dB → ℂ) (X : Matrix dB dB ℂ) :
    snorm (swapVec ψ) (aOp X : Matrix (dB × dA) (dB × dA) ℂ) = ‖stateVecB ψ X‖ := by
  rw [snorm, aOp, mulVec_kronecker_swapVec, norm_swapVec, norm_stateVecB_eq_snorm, snorm, bOp]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {B C : Type*} [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
/-- The commutator form, with the difference inside a single `aOp`. -/
theorem commutation_analysis_aOp {ψ : dA × dB → ℂ} {A : POVM B dA} {Cm : POVM C dA}
    {P : B × C → Matrix dB dB ℂ} (hP : IsPVM P) {δ : ℝ}
    (hA : ∑ b, snorm ψ ((aOp ((A.mats b).val) : Matrix (dA × dB) (dA × dB) ℂ)
        - bOp (∑ c, P (b, c))) ^ 2 ≤ δ)
    (hC : ∑ c, snorm ψ ((aOp ((Cm.mats c).val) : Matrix (dA × dB) (dA × dB) ℂ)
        - bOp (∑ b, P (b, c))) ^ 2 ≤ δ) :
    ∑ p : B × C, snorm ψ (aOp ((A.mats p.1).val * (Cm.mats p.2).val
        - (Cm.mats p.2).val * (A.mats p.1).val) : Matrix (dA × dB) (dA × dB) ℂ) ^ 2
      ≤ 16 * δ := by
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)) (commutation_analysis hP hA hC)
  rw [aOp_sub, aOp_mul, aOp_mul]
end
end MIPRE

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem pairInconsistency_nonneg (ψ : dA × dB → ℂ) (Q : POVM A dA) (R : POVM A dB) :
    0 ≤ pairInconsistency ψ Q R := by
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  split_ifs with h
  · exact le_refl 0
  · exact bornProb_nonneg ψ (Q.posSemidef a) (R.posSemidef b)
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **Orthonormalization from consistency**, blueprint `cor:ortho-from-consistency`, with
`η_ortho(δ) = 18 δ`. The hypothesis is a positive bound on the inconsistency of `Q` with a POVM
`R` on the other factor; the file's docstring records why that is the right form and what the
paper's compactness step would add. -/
theorem exists_projective_of_consistent {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (Q : POVM A dA) (R : POVM A dB) (δ : ℝ) (hδ : 0 < δ)
    (hcons : pairInconsistency ψ Q R ≤ δ) :
    ∃ P : A → Matrix dA dA ℂ,
      (∀ a, (P a)ᴴ = P a) ∧ (∀ a, P a * P a = P a) ∧ (∑ a, P a = 1) ∧
        ∑ a, stateSqNorm ψ (((Q.mats a).val) - P a) < 18 * δ := by
  obtain ⟨P, hsa, hidem, hsum, hbound⟩ :=
    exists_projective_of_nearProjective hψ Q (2 * δ)
      (by simpa using one_sub_two_mul_lt_sum_stateSqNorm hψ Q R δ hδ hcons)
  exact ⟨P, hsa, hidem, hsum, by linarith⟩
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem ptObs_mul_self_le_one (hm : m ∣ Fintype.card F)
    (MA : Question F m → POVM (Answer F m d) dA) (W : Bas) (c : Content F m) :
    (ptObs hm MA W c)ᴴ * ptObs hm MA W c ≤ (1 : Matrix dA dA ℂ) :=
  obs2_mul_self_le_one _
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
theorem ptObsB_mul_self_le_one (hm : m ∣ Fintype.card F)
    (MB : Question F m → POVM (Answer F m d) dB) (W : Bas) (c : Content F m) :
    (ptObsB hm MB W c)ᴴ * ptObsB hm MB W c ≤ (1 : Matrix dB dB ℂ) :=
  obs2_mul_self_le_one _
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
/-- The `W`-marginal of the joint `Pair` measurement is the `Pair` measurement read in `W`
alone. -/
theorem sum_pairPOVM_X (hm : m ∣ Fintype.card F)
    (MA : Question F m → POVM (Answer F m d) dA) (c : Content F m) (o : ZMod 2) :
    ∑ o' : ZMod 2, (((pairPOVM hm MA c).mats (o, o')).val)
      = ((((MA (c.question hm .pair)).map (rdBitPair .X)).mats o).val) :=
  POVM.sum_mats_map_prod _ _ _ o
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
theorem sum_pairPOVM_Z (hm : m ∣ Fintype.card F)
    (MA : Question F m → POVM (Answer F m d) dA) (c : Content F m) (o : ZMod 2) :
    ∑ o' : ZMod 2, (((pairPOVM hm MA c).mats (o', o)).val)
      = ((((MA (c.question hm .pair)).map (rdBitPair .Z)).mats o).val) :=
  POVM.sum_mats_map_prod_prime _ _ _ o
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
theorem chainQty_nonneg (hm : m ∣ Fintype.card F) (ψ : dA × dB → ℂ)
    (MA : Question F m → POVM (Answer F m d) dA) (MB : Question F m → POVM (Answer F m d) dB)
    (W : Bas) (c : Content F m) : 0 ≤ chainQty hm ψ MA MB W c :=
  Finset.sum_nonneg fun _ _ => xSqNorm_nonneg _ _ _
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
theorem incQty_nonneg (hm : m ∣ Fintype.card F) (ψ : dA × dB → ℂ)
    (MA : Question F m → POVM (Answer F m d) dA) (MB : Question F m → POVM (Answer F m d) dB)
    (c : Content F m) : 0 ≤ incQty hm ψ MA MB c :=
  pairInconsistency_nonneg _ _ _
end
end MIPRE.QLD

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset Matrix MIPRE MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
theorem _root_.solution (hψ : star ψ ⬝ᵥ ψ = 1) (c : Content F m)
    {η : ℝ} (hη : 0 < η) :
    ‖stateVec ψ (ptObs hm MA .X c * ptObs hm MA .Z c
        - ptObs hm MA .Z c * ptObs hm MA .X c)‖ ^ 2
      ≤ 12 * xSqNorm ψ (ptObs hm MA .X c) (ptObsB hm MB .X c)
        + 12 * xSqNorm ψ (ptObs hm MA .Z c) (ptObsB hm MB .Z c)
        + 768 * (2 * (chainQty hm ψ MA MB .X c + chainQty hm ψ MA MB .Z c)
          + 72 * (incQty hm ψ MA MB c + η)) := by
  classical
  -- the projective measurement close to Alice's joint `Pair` measurement
  obtain ⟨P, hsa, hidem, hsum, hbound⟩ := exists_projective_of_consistent hψ
    (pairPOVM hm MA c) (pairPOVMB hm MB c) (incQty hm ψ MA MB c + η)
    (by have := incQty_nonneg hm ψ MA MB c; linarith)
    (by rw [incQty]; linarith)
  have hPVM : IsPVM P := ⟨hsa, hidem, hsum⟩
  rw [Fintype.sum_prod_type] at hbound
  have hinc0 := incQty_nonneg hm ψ MA MB c
  have hchX0 := chainQty_nonneg hm ψ MA MB .X c
  have hchZ0 := chainQty_nonneg hm ψ MA MB .Z c
  -- the two hypotheses of the analysis, in the cross-party form
  have hX : ∑ b : ZMod 2, xSqNorm ψ (∑ o' : ZMod 2, P (b, o'))
      (((ptPOVMB hm MB .X c).mats b).val)
      ≤ 2 * (2 * (18 * (incQty hm ψ MA MB c + η))) + 2 * chainQty hm ψ MA MB .X c := by
    refine sum_xSqNorm_le_of_two_step _
      (fun b => ((((MA (c.question hm .pair)).map (rdBitPair .X)).mats b).val)) _ ?_
      (le_of_eq rfl)
    have hstep : ∀ b : ZMod 2, stateSqNorm ψ ((∑ o' : ZMod 2, P (b, o'))
        - ((((MA (c.question hm .pair)).map (rdBitPair .X)).mats b).val))
        ≤ 2 * ∑ o' : ZMod 2, stateSqNorm ψ ((((pairPOVM hm MA c).mats (b, o')).val) - P (b, o')) := by
      intro b
      rw [← sum_pairPOVM_X hm MA c b, ← Finset.sum_sub_distrib]
      refine le_trans (stateSqNorm_sum_le ψ fun o' => P (b, o') - (((pairPOVM hm MA c).mats (b, o')).val))
        ?_
      rw [show (Fintype.card (ZMod 2) : ℝ) = 2 from by rw [ZMod.card]; norm_num]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun o' _ => ?_) (by norm_num)
      rw [stateSqNorm_sub_comm]
    refine le_trans (Finset.sum_le_sum fun b _ => hstep b) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (le_of_lt hbound) (by norm_num)
  have hZ : ∑ b : ZMod 2, xSqNorm ψ (∑ o' : ZMod 2, P (o', b))
      (((ptPOVMB hm MB .Z c).mats b).val)
      ≤ 2 * (2 * (18 * (incQty hm ψ MA MB c + η))) + 2 * chainQty hm ψ MA MB .Z c := by
    refine sum_xSqNorm_le_of_two_step _
      (fun b => ((((MA (c.question hm .pair)).map (rdBitPair .Z)).mats b).val)) _ ?_
      (le_of_eq rfl)
    have hstep : ∀ b : ZMod 2, stateSqNorm ψ ((∑ o' : ZMod 2, P (o', b))
        - ((((MA (c.question hm .pair)).map (rdBitPair .Z)).mats b).val))
        ≤ 2 * ∑ o' : ZMod 2, stateSqNorm ψ ((((pairPOVM hm MA c).mats (o', b)).val) - P (o', b)) := by
      intro b
      rw [← sum_pairPOVM_Z hm MA c b, ← Finset.sum_sub_distrib]
      refine le_trans (stateSqNorm_sum_le ψ fun o' => P (o', b) - (((pairPOVM hm MA c).mats (o', b)).val))
        ?_
      rw [show (Fintype.card (ZMod 2) : ℝ) = 2 from by rw [ZMod.card]; norm_num]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun o' _ => ?_) (by norm_num)
      rw [stateSqNorm_sub_comm]
    refine le_trans (Finset.sum_le_sum fun b _ => hstep b) ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    exact mul_le_mul_of_nonneg_left (le_of_lt hbound) (by norm_num)
  -- transport them into the swapped frame
  set δ : ℝ := 2 * (chainQty hm ψ MA MB .X c + chainQty hm ψ MA MB .Z c)
    + 72 * (incQty hm ψ MA MB c + η) with hδ
  have hXs : ∑ b : ZMod 2, snorm (swapVec ψ)
      ((aOp ((((ptPOVMB hm MB .X c).mats b).val)) : Matrix (dB × dA) (dB × dA) ℂ)
        - bOp (∑ o' : ZMod 2, P (b, o'))) ^ 2 ≤ δ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_)) (le_trans hX ?_)
    · rw [snorm_swapVec_aOp_sub_bOp, ← xSqNorm_eq_sq]
    · rw [hδ]; linarith
  have hZs : ∑ b : ZMod 2, snorm (swapVec ψ)
      ((aOp ((((ptPOVMB hm MB .Z c).mats b).val)) : Matrix (dB × dA) (dB × dA) ℂ)
        - bOp (∑ o' : ZMod 2, P (o', b))) ^ 2 ≤ δ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_)) (le_trans hZ ?_)
    · rw [snorm_swapVec_aOp_sub_bOp, ← xSqNorm_eq_sq]
    · rw [hδ]; linarith
  -- the analysis, on Bob's observables
  have hanal := commutation_analysis_aOp (ψ := swapVec ψ) (A := ptPOVMB hm MB .X c)
    (Cm := ptPOVMB hm MB .Z c) (P := P) hPVM hXs hZs
  have hone : ‖stateVecB ψ ((((ptPOVMB hm MB .X c).mats 1).val)
        * (((ptPOVMB hm MB .Z c).mats 1).val)
      - (((ptPOVMB hm MB .Z c).mats 1).val) * (((ptPOVMB hm MB .X c).mats 1).val))‖ ^ 2
      ≤ 16 * δ := by
    refine le_trans (le_of_eq ?_) (le_trans (Finset.single_le_sum
      (f := fun p : ZMod 2 × ZMod 2 => snorm (swapVec ψ)
        (aOp ((((ptPOVMB hm MB .X c).mats p.1).val) * (((ptPOVMB hm MB .Z c).mats p.2).val)
          - (((ptPOVMB hm MB .Z c).mats p.2).val) * (((ptPOVMB hm MB .X c).mats p.1).val))
          : Matrix (dB × dA) (dB × dA) ℂ) ^ 2)
      (fun p _ => by positivity) (Finset.mem_univ ((1 : ZMod 2), (1 : ZMod 2)))) hanal)
    rw [snorm_swapVec_aOp]
  -- the observables, by the exact expansion
  have hobs : ‖stateVecB ψ (ptObsB hm MB .X c * ptObsB hm MB .Z c
      - ptObsB hm MB .Z c * ptObsB hm MB .X c)‖ ^ 2 ≤ 256 * δ := by
    rw [ptObsB, ptObsB, obs2_commutator_eq, stateVecB_smul, norm_smul,
      show ‖(4 : ℂ)‖ = 4 from by norm_num, mul_pow]
    have : (4 : ℝ) ^ 2 = 16 := by norm_num
    rw [this]
    calc (16 : ℝ) * ‖stateVecB ψ _‖ ^ 2 ≤ 16 * (16 * δ) :=
          mul_le_mul_of_nonneg_left hone (by norm_num)
      _ = 256 * δ := by ring
  -- transfer to Alice's observables
  have htr := norm_stateVec_comm_le (ψ := ψ) (ptObs hm MA .X c) (ptObs hm MA .Z c)
    (ptObsB hm MB .X c) (ptObsB hm MB .Z c)
    (ptObs_mul_self_le_one hm MA .X c) (ptObs_mul_self_le_one hm MA .Z c)
    (ptObsB_mul_self_le_one hm MB .X c) (ptObsB_mul_self_le_one hm MB .Z c)
  rw [norm_stateVecB_sub_comm] at htr
  have hu := xNorm_nonneg ψ (ptObs hm MA .X c) (ptObsB hm MB .X c)
  have hv := xNorm_nonneg ψ (ptObs hm MA .Z c) (ptObsB hm MB .Z c)
  have ht := norm_nonneg (stateVecB ψ (ptObsB hm MB .X c * ptObsB hm MB .Z c
    - ptObsB hm MB .Z c * ptObsB hm MB .X c))
  have h0 := norm_nonneg (stateVec ψ (ptObs hm MA .X c * ptObs hm MA .Z c
    - ptObs hm MA .Z c * ptObs hm MA .X c))
  rw [xSqNorm_eq_sq, xSqNorm_eq_sq, hδ] at *
  nlinarith [sq_nonneg (xNorm ψ (ptObs hm MA .X c) (ptObsB hm MB .X c)
      - xNorm ψ (ptObs hm MA .Z c) (ptObsB hm MB .Z c)),
    sq_nonneg (2 * xNorm ψ (ptObs hm MA .X c) (ptObsB hm MB .X c)
      - ‖stateVecB ψ (ptObsB hm MB .X c * ptObsB hm MB .Z c
        - ptObsB hm MB .Z c * ptObsB hm MB .X c)‖),
    sq_nonneg (2 * xNorm ψ (ptObs hm MA .Z c) (ptObsB hm MB .Z c)
      - ‖stateVecB ψ (ptObsB hm MB .X c * ptObsB hm MB .Z c
        - ptObsB hm MB .Z c * ptObsB hm MB .X c)‖)]
end MIPRE.QLD
