-- Prove2me | solution 1 for MIPRE.QLD.padded_lines_consistency
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:44:49.053986+00:00
-- url     : https://prove2.me/submissions/4c7dfb1f-fcc7-42e9-9777-1b5e09abd56a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/PaddedLines.lean (solution of MIPRE.QLD.padded_lines_consistency);
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
import Definitions.Def_MIPRE_Background_QLD_Combine
import Definitions.Def_MIPRE_Background_QLD_Legalize
import Definitions.Def_MIPRE_Background_QLD_PaddedLines
import Theorems.Thm_MIPRE_IsPVM_aOp
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_IsPVM_posSemidef
import Theorems.Thm_MIPRE_QLD_avgSubAB_le_of_forall
import Theorems.Thm_MIPRE_QLD_avgSub_le_mul_avgAll
import Theorems.Thm_MIPRE_QLD_hatVec_unit
import Theorems.Thm_MIPRE_QLD_pairs_of_lines_prod_of_items
import Theorems.Thm_MIPRE_QLD_sumSubAB_eq
import Theorems.Thm_MIPRE_QLD_sum_pasteLine
import Theorems.Thm_MIPRE_Weyl_isPVM_synOf
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_bornProb_nonneg
import Theorems.Thm_MIPRE_extVec2_unit
import Theorems.Thm_MIPRE_kronecker_sum_right
import Theorems.Thm_MIPRE_sum_kronecker_left

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
theorem sum_quadForm {N ι : Type*} [Fintype N] (ψ : N → ℂ) (s : Finset ι)
    (f : ι → Matrix N N ℂ) :
    star ψ ⬝ᵥ ((∑ i ∈ s, f i) *ᵥ ψ) = ∑ i ∈ s, star ψ ⬝ᵥ ((f i) *ᵥ ψ) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Matrix.add_mulVec, dotProduct_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']
theorem bornProb_sum_sum {ι : Type*} (ψ : dA × dB → ℂ) (s t : Finset ι)
    (A : ι → Matrix dA dA ℂ) (B : ι → Matrix dB dB ℂ) :
    bornProb ψ (∑ i ∈ s, A i) (∑ j ∈ t, B j)
      = ∑ i ∈ s, ∑ j ∈ t, bornProb ψ (A i) (B j) := by
  classical
  simp only [bornProb]
  rw [sum_kronecker_left, sum_quadForm ψ _ _, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kronecker_sum_right, sum_quadForm ψ _ _, Complex.re_sum]
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
/-- A sum whose summand depends on the index only through its image splits into the fibres. -/
theorem sum_fiber {α β M : Type*} [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid M]
    (e : α → β) (f : β → α → M) :
    ∑ g : α, f (e g) g = ∑ b : β, ∑ g ∈ univ.filter fun g => e g = b, f b g := by
  classical
  conv_lhs => rw [← Finset.sum_fiberwise (univ : Finset α) e fun g => f (e g) g]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun g hg => by
    rw [(Finset.mem_filter.mp hg).2]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 K : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K]
variable {R : R1 → Matrix dB dB ℂ} {G : K → Matrix dB dB ℂ}
/-- The other sandwich --- the one the pasted POVM is built from --- is also a Gram operator. -/
theorem sandOpG_posSemidef (hR : IsPVM R) (hG : IsPVM G) (a : R1) (g : K) :
    (G g * R a * G g).PosSemidef := by
  have h : G g * R a * G g = (R a * G g)ᴴ * (R a * G g) := by
    calc G g * R a * G g = G g * (R a * R a) * G g := by rw [hR.idem]
      _ = (R a * G g)ᴴ * (R a * G g) := by
          rw [Matrix.conjTranspose_mul, hR.isSelfAdjoint, hG.isSelfAdjoint]; noncomm_ring
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _
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
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem sumAll_eq_sum (h : LPData F m → ℝ) : sumAll h = ∑ c : LPData F m, h c := by
  rw [← Equiv.sum_comp (lpEquiv F m).symm h, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun pt _ => by rw [Fintype.sum_prod_type]; rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem card_lpData : Fintype.card (LPData F m) = Fintype.card F ^ (2 * m + 1) := by
  rw [Fintype.card_congr (lpEquiv F m), Fintype.card_prod, Fintype.card_prod,
    Fintype.card_pi_const]
  ring
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
/-- **`avgAll` is the uniform average over the data**, which is the form
`pairs_of_lines_prod` is stated in. -/
theorem avgAll_eq_uniform (h : LPData F m → ℝ) :
    avgAll h = ∑ c : LPData F m, (Fintype.card (LPData F m) : ℝ)⁻¹ * h c := by
  rw [avgAll, sumAll_eq_sum, card_lpData, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by push_cast; ring
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
/-- The product form. -/
theorem avgAll_prod_eq_uniform (g : LPData F m → LPData F m → ℝ) :
    avgAll (fun cX => avgAll (fun cZ => g cX cZ))
      = ∑ p : LPData F m × LPData F m, (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹
          * g p.1 p.2 := by
  rw [avgAll_eq_uniform, Fintype.sum_prod_type, Fintype.card_prod]
  refine Finset.sum_congr rfl fun cX _ => ?_
  rw [avgAll_eq_uniform, Finset.mul_sum]
  refine Finset.sum_congr rfl fun cZ _ => ?_
  push_cast
  ring
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
/-- The constant `1` averages to `1`. -/
theorem avgAll_one : avgAll (fun _ : LPData F m => (1 : ℝ)) = 1 := by
  rw [avgAll_eq_uniform, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem avgAll_sub (f g : LPData F m → ℝ) :
    avgAll (fun c => f c - g c) = avgAll f - avgAll g := by
  rw [avgAll, avgAll, avgAll, sumAll_eq_sum, sumAll_eq_sum, sumAll_eq_sum,
    Finset.sum_sub_distrib, mul_sub]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem sumSub_mono (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) (s : F)
    {g g' : LPData F m → LPData F m → ℝ} (hle : ∀ cX cZ, g cX cZ ≤ g' cX cZ) :
    sumSub hm4 hm t s g ≤ sumSub hm4 hm t s g' :=
  Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ =>
    Finset.sum_le_sum fun _ _ => hle _ _
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem avgSub_mono (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) (s : F)
    {g g' : LPData F m → LPData F m → ℝ} (hle : ∀ cX cZ, g cX cZ ≤ g' cX cZ) :
    avgSub hm4 hm t s g ≤ avgSub hm4 hm t s g' :=
  mul_le_mul_of_nonneg_left (sumSub_mono hm4 hm t s hle) (by positivity)
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem sumSub_one (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) (s : F) :
    sumSub hm4 hm t s (fun _ _ => (1 : ℝ)) = (Fintype.card F : ℝ) ^ (10 * m + 2) := by
  simp only [sumSub, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Fintype.card_prod, Fintype.card_pi_const, Fintype.card_pi_const]
  push_cast
  ring
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem sumSubAt_sub (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty)
    (s : F) (pt : Point F (4 * m)) (h h' : LPData F m → LPData F m → ℝ) :
    sumSubAt hm4 hm t s pt (fun cX cZ => h cX cZ - h' cX cZ)
      = sumSubAt hm4 hm t s pt h - sumSubAt hm4 hm t s pt h' := by
  simp only [sumSubAt]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun raw _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun eX _ => ?_
  rw [← Finset.sum_sub_distrib]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem sumSubAB_sub (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) (s : F)
    (g g' : F → F → LPData F m → LPData F m → ℝ) :
    sumSubAB hm4 hm t s (fun a b cX cZ => g a b cX cZ - g' a b cX cZ)
      = sumSubAB hm4 hm t s g - sumSubAB hm4 hm t s g' := by
  simp only [sumSubAB]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun pt _ => sumSubAt_sub hm4 hm t s pt _ _
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem avgSubAB_sub (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) (s : F)
    (g g' : F → F → LPData F m → LPData F m → ℝ) :
    avgSubAB hm4 hm t s (fun a b cX cZ => g a b cX cZ - g' a b cX cZ)
      = avgSubAB hm4 hm t s g - avgSubAB hm4 hm t s g' := by
  rw [avgSubAB, avgSubAB, avgSubAB, sumSubAB_sub, mul_sub]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem avgSubAB_one (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) (s : F) :
    avgSubAB hm4 hm t s (fun _ _ _ _ => (1 : ℝ)) = 1 := by
  have hcard : (Fintype.card (F × F) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hpow : ((Fintype.card F : ℝ) ^ (10 * m + 2)) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have h := sumSubAB_eq hm4 hm t s (fun _ _ _ _ => (1 : ℝ))
  rw [Finset.sum_congr rfl fun p (_ : p ∈ (univ : Finset (F × F))) =>
    sumSub_one hm4 hm t s, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [avgSubAB, mul_left_cancel₀ hcard h, inv_mul_cancel₀ hpow]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dB : Type} [Fintype dB] [DecidableEq dB] {hm : m ∣ Fintype.card F}
  {M : Question F m → POVM (Answer F m d) dB}
theorem posSemidef_pasteLine (hM : ∀ q, IsPVM fun a => (((M q).mats a).val))
    (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (cX cZ : Content F m)
    (q : LinePoly F (m * d) × LinePoly F (m * d)) :
    (pasteLine PX PZ d M cX cZ q
      : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ).PosSemidef := by
  rw [pasteLine, aOp_mul, aOp_mul]
  exact sandOpG_posSemidef (IsPVM.aOp (PZ.isPVM_lineMats d hM cZ))
    (IsPVM.aOp (PX.isPVM_lineMats d hM cX)) q.2 q.1
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dB : Type} [Fintype dB] [DecidableEq dB] {hm : m ∣ Fintype.card F}
  {M : Question F m → POVM (Answer F m d) dB}
/-- **Coarse-graining a fibre sum again**: summing the fibres of `g` over a set of values is summing
over the preimage of that set. -/
theorem sum_filter_fiber {α β N : Type*} [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid N]
    (g : α → β) (p : β → Prop) [DecidablePred p] (T : α → N) :
    ∑ b ∈ univ.filter p, ∑ a ∈ univ.filter fun a => g a = b, T a
      = ∑ a ∈ univ.filter fun a => p (g a), T a := by
  classical
  refine Eq.trans (Finset.sum_congr rfl fun b hb => ?_)
    (Finset.sum_fiberwise_of_maps_to (s := univ.filter fun a => p (g a)) (t := univ.filter p)
      (fun a ha => Finset.mem_filter.mpr ⟨mem_univ _, (Finset.mem_filter.mp ha).2⟩) T)
  refine Finset.sum_congr ?_ fun _ _ => rfl
  rw [Finset.filter_filter]
  refine Finset.filter_congr fun a _ => ?_
  exact ⟨fun h => ⟨by rw [h]; exact (Finset.mem_filter.mp hb).2, h⟩, fun h => h.2⟩
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **Coarse-graining both sides the same way can only increase agreement.** The `POVM`-structure
version is `MIPRE.sum_bornProb_le_map`; here the families are bare, which is the shape the pasted
line measurement comes in. -/
theorem sum_bornProb_le_fibre {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (ψ : dA × dB → ℂ) (P : ι → Matrix dA dA ℂ) (Q : ι → Matrix dB dB ℂ)
    (hP : ∀ i, (P i).PosSemidef) (hQ : ∀ i, (Q i).PosSemidef) (f : ι → κ) :
    ∑ i, bornProb ψ (P i) (Q i)
      ≤ ∑ k : κ, bornProb ψ (∑ i ∈ univ.filter fun i => f i = k, P i)
          (∑ i ∈ univ.filter fun i => f i = k, Q i) := by
  classical
  refine le_trans (le_of_eq (sum_fiber f fun _ i => bornProb ψ (P i) (Q i)))
    (Finset.sum_le_sum fun k _ => ?_)
  rw [bornProb_sum_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  exact Finset.single_le_sum (f := fun j => bornProb ψ (P i) (Q j))
    (fun j _ => bornProb_nonneg ψ (hP i) (hQ j)) hi
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **A Born sum on the diagonal of two POVMs is at most one.** -/
theorem sum_bornProb_diag_le_one {ι : Type*} [Fintype ι] {ψ : dA × dB → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (P : ι → Matrix dA dA ℂ) (Q : ι → Matrix dB dB ℂ)
    (hP : ∀ i, (P i).PosSemidef) (hQ : ∀ i, (Q i).PosSemidef)
    (hPs : ∑ i, P i = 1) (hQs : ∑ i, Q i = 1) :
    ∑ i, bornProb ψ (P i) (Q i) ≤ 1 := by
  classical
  have h1 : bornProb ψ (1 : Matrix dA dA ℂ) (1 : Matrix dB dB ℂ) = 1 := by
    rw [bornProb, Matrix.one_kronecker_one, Matrix.one_mulVec, hψ, Complex.one_re]
  refine le_trans ?_ (le_of_eq h1)
  rw [← hPs, ← hQs, bornProb_sum_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Finset.single_le_sum (f := fun j => bornProb ψ (P i) (Q j))
    (fun j _ => bornProb_nonneg ψ (hP i) (hQ j)) (mem_univ i)
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dB : Type} [Fintype dB] [DecidableEq dB] {hm : m ∣ Fintype.card F}
theorem pasteFib_eq (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (d : ℕ)
    (M : Question F m → POVM (Answer F m d) dB) (cX cZ : Content F m) (r : F × F) :
    pasteFib PX PZ d M cX cZ r
      = ∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
          pasteEval PX PZ cX cZ q = r, pasteLine PX PZ d M cX cZ q := by
  classical
  refine Finset.sum_congr (Finset.filter_congr fun q _ => ?_) fun _ _ => rfl
  rw [pasteEval, Prod.ext_iff]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dB : Type} [Fintype dB] [DecidableEq dB] {hm : m ∣ Fintype.card F}
theorem posSemidef_pasteFib {M : Question F m → POVM (Answer F m d) dB}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (PX : LinePres F m hm .X)
    (PZ : LinePres F m hm .Z) (cX cZ : Content F m) (r : F × F) :
    (pasteFib PX PZ d M cX cZ r).PosSemidef :=
  Finset.sum_induction _ _ (fun _ _ h1 h2 => h1.add h2) Matrix.PosSemidef.zero
    fun q _ => posSemidef_pasteLine hM PX PZ cX cZ q
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dB : Type} [Fintype dB] [DecidableEq dB] {hm : m ∣ Fintype.card F}
theorem sum_pasteFib {M : Question F m → POVM (Answer F m d) dB}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (PX : LinePres F m hm .X)
    (PZ : LinePres F m hm .Z) (cX cZ : Content F m) :
    ∑ r : F × F, pasteFib PX PZ d M cX cZ r = 1 := by
  classical
  rw [Finset.sum_congr rfl fun r (_ : r ∈ (univ : Finset (F × F))) =>
    pasteFib_eq PX PZ d M cX cZ r,
    ← sum_fiber (fun q : LinePoly F (m * d) × LinePoly F (m * d) => pasteEval PX PZ cX cZ q)
      fun _ q => pasteLine PX PZ d M cX cZ q]
  exact sum_pasteLine hM PX PZ cX cZ
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dB : Type} [Fintype dB] [DecidableEq dB] {hm : m ∣ Fintype.card F}
/-- **The line side is a coarse-graining of the fibre family**, along the same linear form. This is
what lets the two be compared by `sum_bornProb_le_fibre`. -/
theorem lineComb_eq_sum_pasteFib (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (d : ℕ)
    (M : Question F m → POVM (Answer F m d) dB) (cX cZ : Content F m) (a b : F) (v : F) :
    lineComb PX PZ d M cX cZ a b v
      = ∑ r ∈ univ.filter fun r : F × F => a * r.1 + b * r.2 = v,
        pasteFib PX PZ d M cX cZ r := by
  classical
  rw [Finset.sum_congr rfl fun r (_ : r ∈ univ.filter fun r : F × F => a * r.1 + b * r.2 = v) =>
    pasteFib_eq PX PZ d M cX cZ r,
    sum_filter_fiber (fun q : LinePoly F (m * d) × LinePoly F (m * d) => pasteEval PX PZ cX cZ q)
      (fun r : F × F => a * r.1 + b * r.2 = v) fun q => pasteLine PX PZ d M cX cZ q]
  rfl
end
end MIPRE.QLD

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
set_option maxHeartbeats 1600000 in
theorem _root_.solution (hm4 : 4 * m ∣ Fintype.card F) (hψ : star ψ ⬝ᵥ ψ = 1)
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
      collProb PX d c ≤ εc) (ty : CL.Ty) (s : F) :
    ∃ QA : LPData F m × LPData F m → F × F →
        Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ,
      (∀ p, IsPVM (QA p))
      ∧ (∀ p r, (ancillaEmbed (dA × Anc F m) ((0 : F), (0 : F)))ᴴ
            * (QA p r * ancillaEmbed (dA × Anc F m) ((0 : F), (0 : F)))
          = sand (hatMats MA .X p.1.pt) (hatMats MA .Z p.2.pt) r)
      ∧ 1 - avgSubAB hm4 hm ty s (fun a b cX cZ =>
            ∑ v : F, bornProb (extHat (m := m) ψ) (ptComb (QA (cX, cZ)) a b v)
              (lineComb PX PZ d MB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) a b v))
        ≤ (m : ℝ) * (m : ℝ) * deltaPairs ε εc := by
  classical
  obtain ⟨QA, hPA, hkA, hbound⟩ := pairs_of_lines_prod_of_items hψ hfail hprojA hprojB PX PZ
    hfacX hfacZ hX1 hX2 hZ2 hcoll
  refine ⟨QA, hPA, hkA, ?_⟩
  have hunit : star (extHat (m := m) ψ) ⬝ᵥ (extHat (m := m) ψ) = 1 :=
    extVec2_unit (hatVec_unit hψ) ((0 : F), (0 : F)) ((0 : F), (0 : F))
  -- the product-law bound on the fine agreement, `pasteFib` being the filter sum by definition
  have hfineb : 1 - avgAll (fun cX : LPData F m => avgAll fun cZ : LPData F m =>
        ∑ r : F × F, bornProb (extHat (m := m) ψ) (QA (cX, cZ) r)
          (pasteFib PX PZ d MB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) r))
      ≤ deltaPairs ε εc := by
    rw [avgAll_prod_eq_uniform]
    exact hbound
  -- every fine agreement is at most one
  have hQpsd : ∀ (p : LPData F m × LPData F m) (r : F × F), (QA p r).PosSemidef :=
    fun p r => (hPA p).posSemidef r
  have hTpsd : ∀ (p : LPData F m × LPData F m) (r : F × F),
      (pasteFib PX PZ d MB (pairCX p) (pairCZ p) r).PosSemidef :=
    fun p r => posSemidef_pasteFib hprojB PX PZ (pairCX p) (pairCZ p) r
  have hTsum : ∀ p : LPData F m × LPData F m,
      ∑ r : F × F, pasteFib PX PZ d MB (pairCX p) (pairCZ p) r = 1 :=
    fun p => sum_pasteFib hprojB PX PZ (pairCX p) (pairCZ p)
  have hfine1 : ∀ p : LPData F m × LPData F m,
      (∑ r : F × F, bornProb (extHat (m := m) ψ) (QA p r)
        (pasteFib PX PZ d MB (pairCX p) (pairCZ p) r)) ≤ 1 := fun p =>
    sum_bornProb_diag_le_one (ι := F × F) hunit (QA p)
      (pasteFib PX PZ d MB (pairCX p) (pairCZ p))
      (hQpsd p) (hTpsd p) (hPA p).sum_eq_one (hTsum p)
  -- coarse-graining only increases agreement
  have hcoarse : ∀ (a b : F) (p : LPData F m × LPData F m),
      (∑ r : F × F, bornProb (extHat (m := m) ψ) (QA p r)
          (pasteFib PX PZ d MB (pairCX p) (pairCZ p) r))
        ≤ ∑ v : F, bornProb (extHat (m := m) ψ) (ptComb (QA p) a b v)
            (lineComb PX PZ d MB (pairCX p) (pairCZ p) a b v) := by
    intro a b p
    refine le_trans (sum_bornProb_le_fibre (ι := F × F) (κ := F) (extHat (m := m) ψ) (QA p)
      (pasteFib PX PZ d MB (pairCX p) (pairCZ p)) (fun r => (hPA p).posSemidef r)
      (fun r => posSemidef_pasteFib hprojB PX PZ _ _ r)
      (fun r : F × F => a * r.1 + b * r.2)) (le_of_eq (Finset.sum_congr rfl fun v _ => ?_))
    rw [ptComb, lineComb_eq_sum_pasteFib]
  -- the deficit of the fine agreement, on the product law
  have hinner : ∀ cX : LPData F m,
      avgAll (fun cZ : LPData F m => 1 - ∑ r : F × F,
          bornProb (extHat (m := m) ψ) (QA (cX, cZ) r)
            (pasteFib PX PZ d MB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) r))
        = 1 - avgAll (fun cZ : LPData F m => ∑ r : F × F,
          bornProb (extHat (m := m) ψ) (QA (cX, cZ) r)
            (pasteFib PX PZ d MB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) r)) := fun cX => by
    rw [avgAll_sub (fun _ : LPData F m => (1 : ℝ)), avgAll_one]
  have houter : avgAll (fun cX : LPData F m => avgAll fun cZ : LPData F m =>
        1 - ∑ r : F × F, bornProb (extHat (m := m) ψ) (QA (cX, cZ) r)
          (pasteFib PX PZ d MB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) r))
      = 1 - avgAll (fun cX : LPData F m => avgAll fun cZ : LPData F m =>
        ∑ r : F × F, bornProb (extHat (m := m) ψ) (QA (cX, cZ) r)
          (pasteFib PX PZ d MB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) r)) := by
    rw [congrArg avgAll (funext hinner), avgAll_sub (fun _ : LPData F m => (1 : ℝ)), avgAll_one]
  -- the padded law, at each fixed `(alpha, beta)`
  have hstep : ∀ a b : F, avgSub hm4 hm ty s (fun cX cZ =>
        1 - ∑ v : F, bornProb (extHat (m := m) ψ) (ptComb (QA (cX, cZ)) a b v)
          (lineComb PX PZ d MB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) a b v))
      ≤ (m : ℝ) * (m : ℝ) * deltaPairs ε εc := by
    intro a b
    refine le_trans (avgSub_mono hm4 hm ty s (g' := fun cX cZ =>
      1 - ∑ r : F × F, bornProb (extHat (m := m) ψ) (QA (cX, cZ) r)
        (pasteFib PX PZ d MB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) r)) fun cX cZ => by
      have h := hcoarse a b (cX, cZ)
      linarith) ?_
    refine le_trans (avgSub_le_mul_avgAll hm4 hm ty s fun cX cZ => by
      have h := hfine1 (cX, cZ)
      linarith) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [houter]
    linarith [hfineb]
  -- and back to the joint law
  have hsub := avgSubAB_sub hm4 hm ty s (fun _ _ _ _ => (1 : ℝ))
    (fun (a b : F) (cX cZ : LPData F m) => ∑ v : F,
      bornProb (extHat (m := m) ψ) (ptComb (QA (cX, cZ)) a b v)
        (lineComb PX PZ d MB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) a b v))
  rw [avgSubAB_one] at hsub
  have hle := avgSubAB_le_of_forall hm4 hm ty s hstep
  linarith [hsub, hle]
end MIPRE.QLD
