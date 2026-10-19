-- Prove2me | solution 1 for MIPRE.QLD.avgSub_le_mul_avgAll
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:31:45.741795+00:00
-- url     : https://prove2.me/submissions/9a1bbd57-89be-4800-b35e-60ca560f6976

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Padded.lean (solution of MIPRE.QLD.avgSub_le_mul_avgAll);
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
import Theorems.Thm_MIPRE_QLD_sumSub_free
import Theorems.Thm_MIPRE_QLD_sumSub_xc
import Theorems.Thm_MIPRE_QLD_sumSub_xc_dline
import Theorems.Thm_MIPRE_QLD_sumSub_zc

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
theorem sum_prod_eq {M : Type*} [AddCommMonoid M] {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → M) : ∑ a, ∑ b, f a b = ∑ p : α × β, f p.1 p.2 := by
  rw [← Finset.univ_product_univ, Finset.sum_product]
end
end MIPRE

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
/-- **The unrestricted law is the sum of the `m` restricted ones.** This is the "mixture" of
`lem:qld-sublines`' second property: a branch that leaves a side free gives that side the
unrestricted law, which is the uniform mixture of the `D_{ty,i}`. -/
theorem sumAll_eq_sum_sumRestr (hm : m ∣ Fintype.card F) {M : Type*} [AddCommMonoid M]
    (h : LPData F m → M) : sumAll h = ∑ i : Fin m, sumRestr hm i h := by
  rw [sumAll, show (∑ i : Fin m, sumRestr hm i h)
      = ∑ pt : Point F m, ∑ i : Fin m, ∑ o : Fin (Fintype.card F / m), ∑ raw : Point F m,
          h ⟨pt, (seedEquiv hm).symm (i, o), raw⟩ from Finset.sum_comm]
  refine Finset.sum_congr rfl fun pt _ => ?_
  rw [← Equiv.sum_comp (seedEquiv hm).symm (fun s : F => ∑ raw : Point F m, h ⟨pt, s, raw⟩)]
  exact (MIPRE.sum_prod_eq (fun (i : Fin m) (o : Fin (Fintype.card F / m)) =>
    ∑ raw : Point F m, h ⟨pt, (seedEquiv hm).symm (i, o), raw⟩)).symm
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem sumAll_const_mul (c : ℝ) (h : LPData F m → ℝ) :
    sumAll (fun cX => c * h cX) = c * sumAll h := by
  simp only [sumAll, Finset.mul_sum]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem sumRestr_const_mul (hm : m ∣ Fintype.card F) (i : Fin m) (c : ℝ)
    (h : LPData F m → ℝ) : sumRestr hm i (fun cZ => c * h cZ) = c * sumRestr hm i h := by
  simp only [sumRestr, Finset.mul_sum]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
/-- The block size as a real division, which is what clearing the denominators needs. -/
theorem cast_card_div (hm : m ∣ Fintype.card F) :
    ((Fintype.card F / m : ℕ) : ℝ) = (Fintype.card F : ℝ) / (m : ℝ) :=
  eq_div_of_mul_eq (Nat.cast_ne_zero.mpr (NeZero.ne m))
    (by rw [← Nat.cast_mul, mul_comm, mul_card_div hm])
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
/-- **Neither side forced**: the padded average is the product of the two unrestricted averages. -/
theorem avgSub_free (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) {s : F}
    (h : padCase (chi hm4 s) = .ab ∨ padCase (chi hm4 s) = .dum)
    (g : LPData F m → LPData F m → ℝ) :
    avgSub hm4 hm t s g = avgAll (fun cX => avgAll (fun cZ => g cX cZ)) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [avgSub, avgAll]
  rw [sumSub_free hm4 hm t h g, sumAll_const_mul, nsmul_eq_mul, Fintype.card_pi_const,
    Fintype.card_pi_const]
  push_cast
  field_simp
  ring
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
/-- **The `Z` side forced**: the padded average is the product of the unrestricted `X` average and
the restricted `Z` average at index `i`. -/
theorem avgSub_zc (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) {s : F}
    {i : Fin m} (h : padCase (chi hm4 s) = .zc i) (g : LPData F m → LPData F m → ℝ) :
    avgSub hm4 hm t s g = avgAll (fun cX => avgRestr hm i (fun cZ => g cX cZ)) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  simp only [avgSub, avgAll, avgRestr]
  rw [sumSub_zc hm4 hm t h g, sumAll_const_mul, nsmul_eq_mul, Fintype.card_pi_const,
    Fintype.card_pi_const, cast_card_div hm]
  push_cast
  field_simp
  ring
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
/-- **The `X` side forced, the `Z` side free.** -/
theorem avgSub_xc (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) {t : CL.Ty} {s : F}
    {i : Fin m} (h : padCase (chi hm4 s) = .xc i) (ht : t ≠ .dline)
    (g : LPData F m → LPData F m → ℝ) :
    avgSub hm4 hm t s g = avgRestr hm i (fun cX => avgAll (fun cZ => g cX cZ)) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  simp only [avgSub, avgAll, avgRestr]
  rw [sumSub_xc hm4 hm h ht g, sumRestr_const_mul, nsmul_eq_mul, Fintype.card_pi_const,
    Fintype.card_pi_const, cast_card_div hm]
  push_cast
  field_simp
  ring
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
/-- **Both sides forced**, the `Z` side at index `0`. -/
theorem avgSub_xc_dline (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) {s : F}
    {i : Fin m} (h : padCase (chi hm4 s) = .xc i) (g : LPData F m → LPData F m → ℝ) :
    avgSub hm4 hm .dline s g
      = avgRestr hm i (fun cX => avgRestr hm 0 (fun cZ => g cX cZ)) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  simp only [avgSub, avgAll, avgRestr]
  rw [sumSub_xc_dline hm4 hm h g, sumRestr_const_mul, nsmul_eq_mul, Fintype.card_pi_const,
    Fintype.card_pi_const, cast_card_div hm]
  push_cast
  field_simp
  ring
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem sumAll_nonneg {h : LPData F m → ℝ} (hpos : ∀ c, 0 ≤ h c) : 0 ≤ sumAll h :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hpos _
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem sumAll_mono {h h' : LPData F m → ℝ} (hle : ∀ c, h c ≤ h' c) : sumAll h ≤ sumAll h' :=
  Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ =>
    Finset.sum_le_sum fun _ _ => hle _
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem sumRestr_nonneg (hm : m ∣ Fintype.card F) (i : Fin m) {h : LPData F m → ℝ}
    (hpos : ∀ c, 0 ≤ h c) : 0 ≤ sumRestr hm i h :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hpos _
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem avgAll_nonneg {h : LPData F m → ℝ} (hpos : ∀ c, 0 ≤ h c) : 0 ≤ avgAll h :=
  mul_nonneg (by positivity) (sumAll_nonneg hpos)
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem avgAll_mono {h h' : LPData F m → ℝ} (hle : ∀ c, h c ≤ h' c) : avgAll h ≤ avgAll h' :=
  mul_le_mul_of_nonneg_left (sumAll_mono hle) (by positivity)
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem avgRestr_nonneg (hm : m ∣ Fintype.card F) (i : Fin m) {h : LPData F m → ℝ}
    (hpos : ∀ c, 0 ≤ h c) : 0 ≤ avgRestr hm i h :=
  mul_nonneg (by positivity) (sumRestr_nonneg hm i hpos)
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem avgAll_const_mul (k : ℝ) (h : LPData F m → ℝ) :
    avgAll (fun c => k * h c) = k * avgAll h := by
  rw [avgAll, avgAll, sumAll_const_mul]
  ring
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
/-- **The restricted laws average to the unrestricted one.** -/
theorem sum_avgRestr (hm : m ∣ Fintype.card F) (h : LPData F m → ℝ) :
    ∑ i : Fin m, avgRestr hm i h = (m : ℝ) * avgAll h := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  simp only [avgRestr, avgAll]
  rw [← Finset.mul_sum, ← sumAll_eq_sum_sumRestr hm h, cast_card_div hm]
  field_simp
  ring
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
/-- **A bound on the unrestricted law bounds each restricted one, at `m` times the error.** -/
theorem avgRestr_le_mul_avgAll (hm : m ∣ Fintype.card F) (i : Fin m) {h : LPData F m → ℝ}
    (hpos : ∀ c, 0 ≤ h c) : avgRestr hm i h ≤ (m : ℝ) * avgAll h := by
  rw [← sum_avgRestr hm h]
  exact Finset.single_le_sum (f := fun j : Fin m => avgRestr hm j h)
    (fun j _ => avgRestr_nonneg hm j hpos) (mem_univ i)
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
/-- **The product form**, at `m^2` times the error: the shape the pasting lemma's hypotheses are in,
each side's line drawn from its own restricted law. -/
theorem avgRestr_prod_le_mul_avgAll (hm : m ∣ Fintype.card F) {g : LPData F m → LPData F m → ℝ}
    (hpos : ∀ cX cZ, 0 ≤ g cX cZ) (i j : Fin m) :
    avgRestr hm i (fun cX => avgRestr hm j (fun cZ => g cX cZ))
      ≤ (m : ℝ) * (m : ℝ) * avgAll (fun cX => avgAll (fun cZ => g cX cZ)) := by
  refine le_trans (avgRestr_le_mul_avgAll hm i
    (fun cX => avgRestr_nonneg hm j (hpos cX))) ?_
  refine le_trans (mul_le_mul_of_nonneg_left (avgAll_mono
    (fun cX => avgRestr_le_mul_avgAll hm j (hpos cX))) (Nat.cast_nonneg m)) ?_
  rw [avgAll_const_mul]
  ring_nf
  exact le_refl _
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem avgAll_prod_nonneg {g : LPData F m → LPData F m → ℝ} (hpos : ∀ cX cZ, 0 ≤ g cX cZ) :
    0 ≤ avgAll (fun cX => avgAll (fun cZ => g cX cZ)) :=
  avgAll_nonneg fun cX => avgAll_nonneg (hpos cX)
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
/-- The `Z` side restricted, the `X` side free. -/
theorem avgAll_avgRestr_le (hm : m ∣ Fintype.card F) {g : LPData F m → LPData F m → ℝ}
    (hpos : ∀ cX cZ, 0 ≤ g cX cZ) (j : Fin m) :
    avgAll (fun cX => avgRestr hm j (fun cZ => g cX cZ))
      ≤ (m : ℝ) * avgAll (fun cX => avgAll (fun cZ => g cX cZ)) := by
  refine le_trans (avgAll_mono fun cX => avgRestr_le_mul_avgAll hm j (hpos cX)) ?_
  rw [avgAll_const_mul]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
/-- The `X` side restricted, the `Z` side free. -/
theorem avgRestr_avgAll_le (hm : m ∣ Fintype.card F) {g : LPData F m → LPData F m → ℝ}
    (hpos : ∀ cX cZ, 0 ≤ g cX cZ) (i : Fin m) :
    avgRestr hm i (fun cX => avgAll (fun cZ => g cX cZ))
      ≤ (m : ℝ) * avgAll (fun cX => avgAll (fun cZ => g cX cZ)) :=
  avgRestr_le_mul_avgAll hm i fun cX => avgAll_nonneg (hpos cX)
end
end MIPRE.QLD

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset MIPRE.LIDT MIPRE.LIDT.CL
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
theorem _root_.solution (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty)
    (s : F) {g : LPData F m → LPData F m → ℝ} (hpos : ∀ cX cZ, 0 ≤ g cX cZ) :
    avgSub hm4 hm t s g
      ≤ (m : ℝ) * (m : ℝ) * avgAll (fun cX => avgAll (fun cZ => g cX cZ)) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hprod := avgAll_prod_nonneg hpos
  have hmm : (m : ℝ) ≤ (m : ℝ) * (m : ℝ) := by nlinarith [hm1]
  have h1mm : (1 : ℝ) ≤ (m : ℝ) * (m : ℝ) := le_trans hm1 hmm
  rcases h : padCase (chi hm4 s) with i | i | _ | _
  · -- the `X` block: the `X` side is restricted, and on a diagonal line so is the `Z` side
    cases t with
    | dline =>
        rw [avgSub_xc_dline hm4 hm h g]
        exact avgRestr_prod_le_mul_avgAll hm hpos i 0
    | point =>
        rw [avgSub_xc hm4 hm h (by simp) g]
        exact le_trans (avgRestr_avgAll_le hm hpos i) (mul_le_mul_of_nonneg_right hmm hprod)
    | aline =>
        rw [avgSub_xc hm4 hm h (by simp) g]
        exact le_trans (avgRestr_avgAll_le hm hpos i) (mul_le_mul_of_nonneg_right hmm hprod)
  · -- the `Z` block: only the `Z` side is restricted
    rw [avgSub_zc hm4 hm t h g]
    exact le_trans (avgAll_avgRestr_le hm hpos i) (mul_le_mul_of_nonneg_right hmm hprod)
  all_goals
    -- `alpha`, `beta` or a dummy coordinate: neither side is restricted
    rw [avgSub_free hm4 hm t (by simp [h]) g]
    exact le_mul_of_one_le_left hprod h1mm
end MIPRE.QLD
