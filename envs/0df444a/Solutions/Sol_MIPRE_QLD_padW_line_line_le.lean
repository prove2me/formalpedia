-- Prove2me | solution 1 for MIPRE.QLD.padW_line_line_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:38:39.561537+00:00
-- url     : https://prove2.me/submissions/c2780724-dc7f-47ce-8f1f-83cf6f7f4569

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/PaddedValue.lean (solution of MIPRE.QLD.padW_line_line_le);
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
import Theorems.Thm_MIPRE_QLD_hatVec_unit
import Theorems.Thm_MIPRE_QLD_one_sub_agreeSum_lineEval_lineEval_le
import Theorems.Thm_MIPRE_QLD_one_sub_sum_bornProb_le_avg_eval
import Theorems.Thm_MIPRE_QLD_sum_avg_evDef_le
import Theorems.Thm_MIPRE_QLD_sum_deg_le
import Theorems.Thm_MIPRE_condFail_le_one_sub_sum_bornProb_diag
import Theorems.Thm_MIPRE_extVec2_unit
import Theorems.Thm_MIPRE_sum_bornProb_le_map

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A] {d : Type*} [Fintype d] [DecidableEq d]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq A] in
/-- An outcome outside the range of the relabelling carries the zero operator. -/
theorem POVM.map_mats_eq_zero_of_forall_ne {B : Type*} [Fintype B] [DecidableEq B] (f : A → B)
    (M : POVM A d) {b : B} (h : ∀ a, f a ≠ b) : ((M.map f).mats b).val = 0 := by
  rw [POVM.map_mats]
  exact Finset.sum_eq_zero fun a ha => absurd (Finset.mem_filter.mp ha).2 (h a)
end
end MIPRE

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA : Type} [Fintype dA] [DecidableEq dA] {hm : m ∣ Fintype.card F}
variable (hm4 : 4 * m ∣ Fintype.card F)
variable (hm)
omit [DecidableEq F] [Algebra (ZMod 2) F] in
theorem lineQ_aline (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m)) :
    lineQ hm4 .aline u s raw = .aline (CL.rep (lineDir hm4 .aline s raw) u) s := rfl
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
theorem lineQ_dline (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m)) :
    lineQ hm4 .dline u s raw
      = .dline (CL.rep (lineDir hm4 .dline s raw) u) s (lineDir hm4 .dline s raw) := rfl
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
theorem padStrat_lineQ (ty : CL.Ty) (hty : ty ≠ .point) {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) :
    padStrat hm hm4 hM (lineQ hm4 ty u s raw)
      = (lineMeas hm hm4 ty hM (CL.rep (lineDir hm4 ty s raw) u) s (rawSet hm4 ty s raw)).map
          (lineAns ty) := by
  cases ty
  · exact absurd rfl hty
  · rfl
  · rfl
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
theorem exists_of_padStrat_lineQ_mats_ne_zero (ty : CL.Ty) (hty : ty ≠ .point)
    {M : Question F m → POVM (Answer F m d) dA} (hM : ∀ q, IsPVM fun a => (((M q).mats a).val))
    (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m)) {a : CL.Answer F (4 * m) d 1}
    (h : ((padStrat hm hm4 hM (lineQ hm4 ty u s raw)).mats a).val ≠ 0) :
    ∃ f, a = lineAns ty f := by
  rw [padStrat_lineQ hm hm4 ty hty] at h
  by_contra hne
  exact h (POVM.map_mats_eq_zero_of_forall_ne _ _ fun f hf => hne ⟨f, hf.symm⟩)
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
variable {dB : Type} [Fintype dB] [DecidableEq dB]
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  (hMA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hMB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
  (Ψ : ((dA × Anc F m) × (F × F)) × ((dB × Anc F m) × (F × F)) → ℂ)
omit [Algebra (ZMod 2) F] in
theorem accepts_lineQ_lineQ_self (ty : CL.Ty) (hty : ty ≠ .point) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) (f : LinePoly F (m * d + 1)) :
    CL.accepts hm4 (lineQ hm4 ty u s raw) (lineQ hm4 ty u s raw) (lineAns ty f) (lineAns ty f)
      = true := by
  cases ty
  · exact absurd rfl hty
  · simp [lineQ_aline, lineAns, alineAns, CL.accepts, CL.Question.fmtOk, CL.subtests]
  · simp [lineQ_dline, lineAns, dlineAns, CL.accepts, CL.Question.fmtOk, CL.subtests]
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
variable {dB : Type} [Fintype dB] [DecidableEq dB]
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  (hMA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hMB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
  (Ψ : ((dA × Anc F m) × (F × F)) × ((dB × Anc F m) × (F × F)) → ℂ)
/-- **Identical lines**: the conditional failure is at most the disagreement of the two line
measurements, outcome polynomial by outcome polynomial. -/
theorem condFail_lineQ_lineQ_le (ty : CL.Ty) (hty : ty ≠ .point) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) :
    condFail (clGame (d := d) (ldc := 1) hm4) Ψ (padStrat hm hm4 hMA) (padStrat hm hm4 hMB)
        (lineQ hm4 ty u s raw) (lineQ hm4 ty u s raw)
      ≤ 1 - ∑ f, bornProb Ψ
          (((lineMeas hm hm4 ty hMA (CL.rep (lineDir hm4 ty s raw) u) s (rawSet hm4 ty s raw)).mats
            f).val)
          (((lineMeas hm hm4 ty hMB (CL.rep (lineDir hm4 ty s raw) u) s (rawSet hm4 ty s raw)).mats
            f).val) := by
  refine le_trans (condFail_le_one_sub_sum_bornProb_diag fun a ha _ => ?_) ?_
  · obtain ⟨f, rfl⟩ := exists_of_padStrat_lineQ_mats_ne_zero hm hm4 ty hty hMA u s raw ha
    exact accepts_lineQ_lineQ_self hm4 ty hty u s raw f
  · rw [padStrat_lineQ hm hm4 ty hty hMA, padStrat_lineQ hm hm4 ty hty hMB]
    have := sum_bornProb_le_map Ψ
      (lineMeas hm hm4 ty hMA (CL.rep (lineDir hm4 ty s raw) u) s (rawSet hm4 ty s raw))
      (lineMeas hm hm4 ty hMB (CL.rep (lineDir hm4 ty s raw) u) s (rawSet hm4 ty s raw))
      (lineAns ty)
    linarith
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
/-- The disagreement of the two line measurements read at the sample's point is the disagreement of
the evaluated families. -/
theorem evDef_lineTau (ty : CL.Ty) (x : Amb F m) :
    evDef Ψ (lineFam hm hm4 ty hMA x) (lineFam hm hm4 ty hMB x) (lineTau hm4 ty x.1 x.2.1 x.2.2)
      = 1 - ∑ a : F, bornProb Ψ (((lineEvalFam hm hm4 ty hMA x).mats a).val)
          (((lineEvalFam hm hm4 ty hMB x).mats a).val) := rfl
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
/-- A sum over the ambient sample, as a sum over the seed, the raw direction and the point. -/
theorem sum_amb_eq (g : Amb F m → ℝ) :
    ∑ x : Amb F m, g x = ∑ s : F, ∑ raw : Point F (4 * m), ∑ u : Point F (4 * m), g (u, s, raw) :=
        by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_comm
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
theorem uniform_amb_nonneg (x : Amb F m) : 0 ≤ uniform (Amb F m) x :=
  inv_nonneg.mpr (Nat.cast_nonneg _)
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
theorem sum_uniform_amb : ∑ x : Amb F m, uniform (Amb F m) x = 1 := by
  simp only [uniform, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
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
omit [Algebra (ZMod 2) F] [NeZero m] in
/-- The disagreement of two families, as the uniform average of the per-sample disagreements. -/
theorem one_sub_agreeSum_uniform_eq (M : Amb F m → POVM F ((dA × Anc F m) × (F × F)))
    (N : Amb F m → POVM F ((dB × Anc F m) × (F × F))) :
    1 - agreeSum (uniform (Amb F m)) Ψ M N
      = ∑ x : Amb F m, uniform (Amb F m) x
          * (1 - ∑ a : F, bornProb Ψ (((M x).mats a).val) (((N x).mats a).val)) := by
  rw [agreeSum]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, sum_uniform_amb]
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
  {ε : ℝ}
variable {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
  (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
  (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
include hψ hfail in
theorem _root_.solution (hε : 0 ≤ ε) (hd : 1 ≤ d) (ty : CL.Ty) (hty : ty ≠ .point) :
    padW hm hm4 ψ hprojA hprojB ty ty
      ≤ 11 * ((m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹)
            + deltaQ ε)
        + ((m : ℝ) * d + 1) / Fintype.card F + (Fintype.card F : ℝ)⁻¹ := by
  set Ψ := extHat (F := F) (m := m) ψ with hΨdef
  have hΨ : star Ψ ⬝ᵥ Ψ = 1 := extVec2_unit (hatVec_unit hψ) _ _
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcA : (Fintype.card (Amb F m) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hP0 : (0 : ℝ) ≤ Fintype.card (Point F (4 * m)) := Nat.cast_nonneg _
  have hcAinv : (0 : ℝ) ≤ (Fintype.card (Amb F m) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  -- the per-sample bound, by polynomial separation
  have h1 : ∀ x : Amb F m,
      condFail (clGame (d := d) (ldc := 1) hm4) Ψ (padStrat hm hm4 hprojA) (padStrat hm hm4 hprojB)
          (lineQ hm4 ty x.1 x.2.1 x.2.2) (lineQ hm4 ty x.1 x.2.1 x.2.2)
        ≤ (Fintype.card F : ℝ)⁻¹ * ∑ t : F,
            evDef Ψ (lineFam hm hm4 ty hprojA x) (lineFam hm hm4 ty hprojB x) t
          + ((m : ℝ) * d + 1) / Fintype.card F := by
    intro x
    refine le_trans (condFail_lineQ_lineQ_le hm hm4 hprojA hprojB Ψ ty hty x.1 x.2.1 x.2.2) ?_
    have h := one_sub_sum_bornProb_le_avg_eval hΨ (lineFam hm hm4 ty hprojA x)
      (lineFam hm hm4 ty hprojB x)
    push_cast at h
    exact h
  -- the degenerate lines
  have hdeg : (Fintype.card (Amb F m) : ℝ)⁻¹ * ((Fintype.card (Point F (4 * m)) : ℝ)
      * ∑ s : F, ∑ raw : Point F (4 * m), (if lineDir hm4 ty s raw = 0 then (1 : ℝ) else 0))
      ≤ (Fintype.card F : ℝ)⁻¹ := by
    have hc : (Fintype.card (Amb F m) : ℝ)⁻¹
        * ((Fintype.card (Point F (4 * m)) : ℝ) * (Fintype.card (Point F (4 * m)) : ℝ))
        = (Fintype.card F : ℝ)⁻¹ := by
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
      field_simp
    rw [← hc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sum_deg_le hm4 ty hty) hP0)
      (inv_nonneg.mpr (Nat.cast_nonneg _))
  calc padW hm hm4 ψ hprojA hprojB ty ty
      ≤ ∑ x : Amb F m, uniform (Amb F m) x * ((Fintype.card F : ℝ)⁻¹ * ∑ t : F,
            evDef Ψ (lineFam hm hm4 ty hprojA x) (lineFam hm hm4 ty hprojB x) t
          + ((m : ℝ) * d + 1) / Fintype.card F) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h1 x) (uniform_amb_nonneg x)
    _ = (Fintype.card (Amb F m) : ℝ)⁻¹ * ∑ x : Amb F m, ((Fintype.card F : ℝ)⁻¹ * ∑ t : F,
            evDef Ψ (lineFam hm hm4 ty hprojA x) (lineFam hm hm4 ty hprojB x) t)
          + ((m : ℝ) * d + 1) / Fintype.card F := by
        simp only [uniform, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcA, one_mul]
    _ ≤ (Fintype.card (Amb F m) : ℝ)⁻¹ * (∑ x : Amb F m,
            evDef Ψ (lineFam hm hm4 ty hprojA x) (lineFam hm hm4 ty hprojB x)
              (lineTau hm4 ty x.1 x.2.1 x.2.2)
          + (Fintype.card (Point F (4 * m)) : ℝ)
            * ∑ s : F, ∑ raw : Point F (4 * m), (if lineDir hm4 ty s raw = 0 then (1 : ℝ) else 0))
          + ((m : ℝ) * d + 1) / Fintype.card F := by
        refine add_le_add (mul_le_mul_of_nonneg_left ?_ hcAinv) le_rfl
        rw [sum_amb_eq, sum_amb_eq]
        conv_rhs => simp only [Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun s _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun raw _ => ?_
        rw [mul_ite, mul_one, mul_zero]
        exact sum_avg_evDef_le hm hm4 hprojA hprojB Ψ hΨ ty s raw
    _ ≤ (Fintype.card (Amb F m) : ℝ)⁻¹ * ∑ x : Amb F m,
            evDef Ψ (lineFam hm hm4 ty hprojA x) (lineFam hm hm4 ty hprojB x)
              (lineTau hm4 ty x.1 x.2.1 x.2.2)
          + (Fintype.card F : ℝ)⁻¹ + ((m : ℝ) * d + 1) / Fintype.card F := by
        rw [mul_add]
        linarith
    _ = (1 - agreeSum (uniform (Amb F m)) Ψ (lineEvalFam hm hm4 ty hprojA)
          (lineEvalFam hm hm4 ty hprojB))
          + (Fintype.card F : ℝ)⁻¹ + ((m : ℝ) * d + 1) / Fintype.card F := by
        rw [one_sub_agreeSum_uniform_eq]
        simp only [uniform, ← Finset.mul_sum, evDef_lineTau]
    _ ≤ 11 * ((m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹)
            + deltaQ ε)
        + ((m : ℝ) * d + 1) / Fintype.card F + (Fintype.card F : ℝ)⁻¹ := by
        have := one_sub_agreeSum_lineEval_lineEval_le hm hm4 hprojA hprojB hψ hfail hε hd ty hty
        linarith
end MIPRE.QLD
