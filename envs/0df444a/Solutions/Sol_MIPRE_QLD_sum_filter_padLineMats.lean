-- Prove2me | solution 1 for MIPRE.QLD.sum_filter_padLineMats
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:28:07.103128+00:00
-- url     : https://prove2.me/submissions/f16ab6b3-271c-4130-a17f-3e6153d0dd9f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Combine.lean (solution of MIPRE.QLD.sum_filter_padLineMats);
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
import Theorems.Thm_MIPRE_QLD_rep_add_lineParam_smul
import Theorems.Thm_MIPRE_QLD_xBlk_dir_sub
import Theorems.Thm_MIPRE_QLD_zBlk_dir_sub

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
theorem natDegree_toPoly_le (f : LinePoly F n) : (toPoly f).natDegree ≤ n := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  exact le_trans (Polynomial.natDegree_monomial_le (f i)) (Nat.lt_succ_iff.mp i.isLt)
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
theorem eval_toPoly (f : LinePoly F n) (t : F) :
    (toPoly f).eval t = LinePoly.eval f t := by
  rw [toPoly, Polynomial.eval_finsetSum, LinePoly.eval]
  exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.eval_monomial]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
/-- **Shifting a point along the direction moves its parameter by the shift.** -/
theorem lineParam_add_smul {w : Point F m} (hw : ∃ j, w j ≠ 0) (u₀ x : Point F m) (t : F) :
    MIPRE.LIDT.CL.lineParam u₀ w (x + t • w) = MIPRE.LIDT.CL.lineParam u₀ w x + t := by
  simp only [MIPRE.LIDT.CL.lineParam, dif_pos hw]
  set j := Fin.find (fun j => w j ≠ 0) hw with hj
  have hwj : w j ≠ 0 := Fin.find_spec hw
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable (m)
variable {m} [NeZero m]
/-- Moving along the padded line moves the `X` block along the `X` block of the direction. This
is the identity that makes the combining map of `lem:qld-padded-lines` well defined. -/
theorem xBlk_add_smul (u v : Point F (4 * m)) (t : F) :
    xBlk (u + t • v) = xBlk u + t • xBlk v := rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable (m)
variable {m} [NeZero m]
theorem zBlk_add_smul (u v : Point F (4 * m)) (t : F) :
    zBlk (u + t • v) = zBlk u + t • zBlk v := rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
theorem eval_affPoly (a : F × F) (t : F) : (affPoly a).eval t = affEval a t := by
  rw [affPoly, affEval, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
theorem natDegree_affPoly_le (a : F × F) : (affPoly a).natDegree ≤ 1 := by
  rw [affPoly]
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  rw [max_le_iff]
  exact ⟨le_trans (le_of_eq (Polynomial.natDegree_C a.1)) (Nat.zero_le 1),
    le_trans (Polynomial.natDegree_C_mul_le a.2 Polynomial.X)
      (le_of_eq Polynomial.natDegree_X)⟩
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
theorem eval_ofPoly {p : Polynomial F} (hp : p.natDegree ≤ n) (t : F) :
    LinePoly.eval (ofPoly n p) t = p.eval t := by
  rw [LinePoly.eval, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp),
    ← Fin.sum_univ_eq_sum_range (fun i => p.coeff i * t ^ i) (n + 1)]
  rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
theorem natDegree_comp_affPoly_le {k : ℕ} (a : F × F) {f : LinePoly F n}
    (hf : (toPoly f).natDegree ≤ k) : ((toPoly f).comp (affPoly a)).natDegree ≤ k :=
  le_trans Polynomial.natDegree_comp_le
    (le_trans (Nat.mul_le_mul hf (natDegree_affPoly_le a)) (le_of_eq (mul_one k)))
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
theorem natDegree_combinePoly_le (aAff bAff xAff zAff : F × F) (fX fZ : LinePoly F n) :
    (combinePoly aAff bAff xAff zAff fX fZ).natDegree ≤ n + 1 := by
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  rw [max_le_iff]
  constructor
  · refine le_trans (Polynomial.natDegree_mul_le) ?_
    exact le_trans (Nat.add_le_add (natDegree_affPoly_le aAff)
      (natDegree_comp_affPoly_le xAff (natDegree_toPoly_le fX))) (by omega)
  · refine le_trans (Polynomial.natDegree_mul_le) ?_
    exact le_trans (Nat.add_le_add (natDegree_affPoly_le bAff)
      (natDegree_comp_affPoly_le zAff (natDegree_toPoly_le fZ))) (by omega)
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
/-- **The defining property of the combining map**: at the padded parameter `t` its value is
`alpha(t) f_X(x(t)) + beta(t) f_Z(z(t))`. -/
theorem eval_combine (aAff bAff xAff zAff : F × F) (fX fZ : LinePoly F n) (t : F) :
    LinePoly.eval (combine aAff bAff xAff zAff fX fZ) t
      = affEval aAff t * LinePoly.eval fX (affEval xAff t)
        + affEval bAff t * LinePoly.eval fZ (affEval zAff t) := by
  rw [combine, eval_ofPoly (natDegree_combinePoly_le aAff bAff xAff zAff fX fZ), combinePoly,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_comp, eval_affPoly, eval_affPoly, eval_affPoly, eval_affPoly, eval_toPoly,
    eval_toPoly]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
  [NeZero m]
/-- A degenerate line assigns every point the parameter zero. -/
theorem lineParam_dir_zero (u₀ y : Point F m) : CL.lineParam u₀ (0 : Point F m) y = 0 := by
  rw [CL.lineParam, dif_neg]
  exact fun h => h.choose_spec rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
  [NeZero m]
/-- The base point has parameter zero. -/
theorem lineParam_self (u₀ w : Point F m) : CL.lineParam u₀ w u₀ = 0 := by
  rw [CL.lineParam]
  split
  · rw [sub_self, zero_div]
  · rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
  [NeZero m]
/-- **The shifted block lies on the subline at the affine parameter.** -/
theorem on_line_affEval {W w : Point F m} (h : w = W ∨ w = 0) (x : Point F m) (tau : F) :
    x + tau • w = CL.rep W x + affEval (subAff W w x) tau • W := by
  have hx : CL.rep W x + (CL.lineParam (CL.rep W x) W x) • W = x := rep_add_lineParam_smul W x
  have haff : affEval (subAff W w x) tau
      = CL.lineParam (CL.rep W x) W x + (if w = W ∧ W ≠ 0 then 1 else 0) * tau := rfl
  by_cases hc : w = W ∧ W ≠ 0
  · rw [haff, if_pos hc, one_mul, add_smul, ← add_assoc, hx, hc.1]
  · rw [haff, if_neg hc, zero_mul, add_zero, hx]
    rcases h with h | h
    · rw [h, show W = 0 from by by_contra hW; exact hc ⟨h, hW⟩, smul_zero, add_zero]
    · rw [h, smul_zero, add_zero]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
  [NeZero m]
/-- **The parameter of the shifted block on the subline is affine in the padded parameter.** -/
theorem lineParam_affEval {W w : Point F m} (h : w = W ∨ w = 0) (x : Point F m) (tau : F) :
    CL.lineParam (CL.rep W x) W (x + tau • w) = affEval (subAff W w x) tau := by
  rw [on_line_affEval h x tau]
  by_cases hW : ∃ j, W j ≠ 0
  · rw [lineParam_add_smul hW, lineParam_self, zero_add]
  · have hW0 : W = 0 := by
      funext j
      by_contra hj
      exact hW ⟨j, hj⟩
    rw [hW0, lineParam_dir_zero, affEval, subAff]
    show (0 : F) = CL.lineParam (CL.rep (0 : Point F m) x) 0 x + _ * tau
    rw [lineParam_dir_zero, zero_add, if_neg (fun hc => hc.2 rfl), zero_mul]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
/-- The direction a data presents does not depend on its point. -/
theorem LPData.dir_congr (hm : m ∣ Fintype.card F) (ty : CL.Ty) {c c' : LPData F m}
    (hs : c.s = c'.s) (hr : c.raw = c'.raw) : c.dir hm ty = c'.dir hm ty := by
  cases ty
  · rw [LPData.dir_point, LPData.dir_point]
  · rw [LPData.dir_aline, LPData.dir_aline, hs]
  · rw [LPData.dir_dline, LPData.dir_dline, hs, hr]
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
/-- **The subline data is unchanged by the padded shift except in its point**, because the seed and
the raw direction it reads are. -/
theorem subX_padShift (ty : CL.Ty) (tau : F) (P : LPData F (4 * m)) (e : F × Point F m) :
    subX hm4 hm (padShift hm4 ty tau P) e
      = { subX hm4 hm P e with pt := xBlk (padShift hm4 ty tau P).pt } := by
  simp only [subX, padShift_s]
  rcases h : padCase (chi hm4 P.s) with i | i | _ | _ <;> rfl
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
theorem subZ_padShift (ty ty' : CL.Ty) (tau : F) (P : LPData F (4 * m)) (e : F × Point F m) :
    subZ hm4 hm ty' (padShift hm4 ty tau P) e
      = { subZ hm4 hm ty' P e with pt := zBlk (padShift hm4 ty tau P).pt } := by
  simp only [subZ, padShift_s]
  rcases h : padCase (chi hm4 P.s) with i | i | _ | _ <;> cases ty' <;> rfl
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
theorem subX_padShift_dir (ty ty' : CL.Ty) (tau : F) (P : LPData F (4 * m))
    (e : F × Point F m) :
    (subX hm4 hm (padShift hm4 ty tau P) e).dir hm ty' = (subX hm4 hm P e).dir hm ty' := by
  refine LPData.dir_congr hm ty' ?_ ?_ <;> rw [subX_padShift]
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
theorem subZ_padShift_dir (ty ty' : CL.Ty) (tau : F) (P : LPData F (4 * m))
    (e : F × Point F m) :
    (subZ hm4 hm ty' (padShift hm4 ty tau P) e).dir hm ty'
      = (subZ hm4 hm ty' P e).dir hm ty' := by
  refine LPData.dir_congr hm ty' ?_ ?_ <;> rw [subZ_padShift]
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
/-- **The subline's base point is unchanged by the padded shift**, which is where the containment
of `lem:qld-sublines` is used: the block either moves along the subline or does not move. -/
theorem rep_xBlk_padShift (ty : CL.Ty) (tau : F) (P : LPData F (4 * m)) (e : F × Point F m) :
    CL.rep ((subX hm4 hm P e).dir hm ty) (xBlk (padShift hm4 ty tau P).pt)
      = CL.rep ((subX hm4 hm P e).dir hm ty) (xBlk P.pt) := by
  rw [padShift_pt, xBlk_add_smul]
  rcases xBlk_dir_sub hm4 hm ty P e with h | h
  · rw [h, rep_add_smul]
  · rw [h, smul_zero, add_zero]
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
theorem rep_zBlk_padShift (ty : CL.Ty) (tau : F) (P : LPData F (4 * m)) (e : F × Point F m) :
    CL.rep ((subZ hm4 hm ty P e).dir hm ty) (zBlk (padShift hm4 ty tau P).pt)
      = CL.rep ((subZ hm4 hm ty P e).dir hm ty) (zBlk P.pt) := by
  rw [padShift_pt, zBlk_add_smul]
  rcases zBlk_dir_sub hm4 hm ty P e with h | h
  · rw [h, rep_add_smul]
  · rw [h, smul_zero, add_zero]
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
theorem affEval_aAffOf (ty : CL.Ty) (P : LPData F (4 * m)) (tau : F) :
    affEval (aAffOf hm4 ty P) tau = alph (padShift hm4 ty tau P).pt := by
  show alph P.pt + alph (P.dir hm4 ty) * tau = alph (P.pt + tau • P.dir hm4 ty)
  rw [alph_add, alph_smul]
  ring
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
theorem affEval_bAffOf (ty : CL.Ty) (P : LPData F (4 * m)) (tau : F) :
    affEval (bAffOf hm4 ty P) tau = bet (padShift hm4 ty tau P).pt := by
  show bet P.pt + bet (P.dir hm4 ty) * tau = bet (P.pt + tau • P.dir hm4 ty)
  rw [bet_add, bet_smul]
  ring
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
/-- **The `X` subline parameter of the shifted point is `xAffOf` at the padded parameter.** -/
theorem param_subX_padShift (ty : CL.Ty) (PX : LinePres F m hm .X)
    (hbase : ∀ c : Content F m, PX.base c = CL.rep (PX.dir c) (c.pt .X))
    (hdir : ∀ (D : LPData F m) (u : Point F m), PX.dir (ofLPX D u) = D.dir hm ty)
    (P : LPData F (4 * m)) (e : F × Point F m) (u : Point F m) (tau : F) :
    PX.param (ofLPX (subX hm4 hm (padShift hm4 ty tau P) e) u)
      = affEval (xAffOf hm4 hm ty P e) tau := by
  rw [LinePres.param, hbase, hdir, subX_padShift_dir]
  show CL.lineParam (CL.rep ((subX hm4 hm P e).dir hm ty)
      (subX hm4 hm (padShift hm4 ty tau P) e).pt)
      ((subX hm4 hm P e).dir hm ty) (subX hm4 hm (padShift hm4 ty tau P) e).pt = _
  rw [subX_pt, rep_xBlk_padShift, padShift_pt, xBlk_add_smul, xAffOf]
  exact lineParam_affEval (xBlk_dir_sub hm4 hm ty P e) (xBlk P.pt) tau
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
/-- **The `Z` subline parameter of the shifted point is `zAffOf` at the padded parameter.** -/
theorem param_subZ_padShift (ty : CL.Ty) (PZ : LinePres F m hm .Z)
    (hbase : ∀ c : Content F m, PZ.base c = CL.rep (PZ.dir c) (c.pt .Z))
    (hdir : ∀ (D : LPData F m) (u : Point F m), PZ.dir (ofLPZ D u) = D.dir hm ty)
    (P : LPData F (4 * m)) (e : F × Point F m) (u : Point F m) (tau : F) :
    PZ.param (ofLPZ (subZ hm4 hm ty (padShift hm4 ty tau P) e) u)
      = affEval (zAffOf hm4 hm ty P e) tau := by
  rw [LinePres.param, hbase, hdir, subZ_padShift_dir]
  show CL.lineParam (CL.rep ((subZ hm4 hm ty P e).dir hm ty)
      (subZ hm4 hm ty (padShift hm4 ty tau P) e).pt)
      ((subZ hm4 hm ty P e).dir hm ty) (subZ hm4 hm ty (padShift hm4 ty tau P) e).pt = _
  rw [subZ_pt, rep_zBlk_padShift, padShift_pt, zBlk_add_smul, zAffOf]
  exact lineParam_affEval (zBlk_dir_sub hm4 hm ty P e) (zBlk P.pt) tau
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
/-- **The paper's defining property of the combining map**: at the padded parameter `tau` the
combined polynomial takes the value `alpha * f_X(x) + beta * f_Z(z)` at the corresponding point of
the padded line, `x` and `z` being read on their own sublines. -/
theorem eval_padCombine (ty : CL.Ty) (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    (hbaseX : ∀ c : Content F m, PX.base c = CL.rep (PX.dir c) (c.pt .X))
    (hdirX : ∀ (D : LPData F m) (u : Point F m), PX.dir (ofLPX D u) = D.dir hm ty)
    (hbaseZ : ∀ c : Content F m, PZ.base c = CL.rep (PZ.dir c) (c.pt .Z))
    (hdirZ : ∀ (D : LPData F m) (u : Point F m), PZ.dir (ofLPZ D u) = D.dir hm ty)
    (P : LPData F (4 * m)) (eX eZ : F × Point F m)
    (q : LinePoly F (m * d) × LinePoly F (m * d)) (uZ uX : Point F m) (tau : F) :
    LinePoly.eval (padCombine hm4 hm ty d P eX eZ q) tau
      = alph (padShift hm4 ty tau P).pt
          * LinePoly.eval q.1 (PX.param (ofLPX (subX hm4 hm (padShift hm4 ty tau P) eX) uZ))
        + bet (padShift hm4 ty tau P).pt
          * LinePoly.eval q.2 (PZ.param (ofLPZ (subZ hm4 hm ty (padShift hm4 ty tau P) eZ) uX)) := by
  rw [padCombine, eval_combine, affEval_aAffOf, affEval_bAffOf,
    param_subX_padShift hm4 hm ty PX hbaseX hdirX P eX uZ tau,
    param_subZ_padShift hm4 hm ty PZ hbaseZ hdirZ P eZ uX tau]
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dB : Type} [Fintype dB] [DecidableEq dB] {hm : m ∣ Fintype.card F}
  {M : Question F m → POVM (Answer F m d) dB}
theorem _root_.solution (hm4 : 4 * m ∣ Fintype.card F) (ty : CL.Ty)
    (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    (hbaseX : ∀ c : Content F m, PX.base c = CL.rep (PX.dir c) (c.pt .X))
    (hdirX : ∀ (D : LPData F m) (u : Point F m), PX.dir (ofLPX D u) = D.dir hm ty)
    (hbaseZ : ∀ c : Content F m, PZ.base c = CL.rep (PZ.dir c) (c.pt .Z))
    (hdirZ : ∀ (D : LPData F m) (u : Point F m), PZ.dir (ofLPZ D u) = D.dir hm ty)
    (P : LPData F (4 * m)) (tau a : F) :
    ∑ f ∈ univ.filter fun f : LinePoly F (m * d + 1) => LinePoly.eval f tau = a,
        padLineMats hm4 ty PX PZ M P f
      = ((Fintype.card (SubRand F m) : ℝ))⁻¹ • ∑ e : SubRand F m,
          ∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
              alph (padShift hm4 ty tau P).pt
                    * LinePoly.eval q.1
                        (PX.param (pairCX (subPair hm4 hm ty (padShift hm4 ty tau P) e)))
                  + bet (padShift hm4 ty tau P).pt
                    * LinePoly.eval q.2
                        (PZ.param (pairCZ (subPair hm4 hm ty (padShift hm4 ty tau P) e))) = a,
            pasteLine PX PZ d M (pairCX (subPair hm4 hm ty P e))
              (pairCZ (subPair hm4 hm ty P e)) q := by
  classical
  simp only [padLineMats]
  rw [← Finset.smul_sum, Finset.sum_comm]
  refine congrArg (fun A => ((Fintype.card (SubRand F m) : ℝ))⁻¹ • A)
    (Finset.sum_congr rfl fun e _ => ?_)
  rw [sum_filter_fiber (fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
    padCombine hm4 hm ty d P e.1 e.2 q) (fun f => LinePoly.eval f tau = a)]
  refine Finset.sum_congr (Finset.filter_congr fun q _ => ?_) fun _ _ => rfl
  rw [eval_padCombine hm4 hm ty PX PZ hbaseX hdirX hbaseZ hdirZ P e.1 e.2 q
    (subZ hm4 hm ty (padShift hm4 ty tau P) e.2).pt
    (subX hm4 hm (padShift hm4 ty tau P) e.1).pt tau]
  exact Iff.rfl
end MIPRE.QLD
