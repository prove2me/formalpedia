-- Prove2me | solution 1 for MIPRE.QLD.padStrat_value
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:40:27.087954+00:00
-- url     : https://prove2.me/submissions/9ae204db-df2a-40d5-b50e-3ec5a42734a6

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/PaddedValue.lean (solution of MIPRE.QLD.padStrat_value);
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
import Theorems.Thm_MIPRE_LIDT_CL_one_sub_povmValue_clGame
import Theorems.Thm_MIPRE_POVM_map_map
import Theorems.Thm_MIPRE_POVM_sum_val
import Theorems.Thm_MIPRE_QLD_agreeSum_lineEvalFam_ptFam
import Theorems.Thm_MIPRE_QLD_agreeSum_ptFam_lineEvalFam
import Theorems.Thm_MIPRE_QLD_eval_padLine
import Theorems.Thm_MIPRE_QLD_hatLinePOVM_consistency
import Theorems.Thm_MIPRE_QLD_hatLinePOVM_point_consistency
import Theorems.Thm_MIPRE_QLD_hatVec_unit
import Theorems.Thm_MIPRE_QLD_one_sub_agreeSum_pt_pt_le
import Theorems.Thm_MIPRE_QLD_one_sub_inv_card_mul_sum_le
import Theorems.Thm_MIPRE_QLD_padStrat_lineQ_map_rdEval
import Theorems.Thm_MIPRE_QLD_padW_line_line_le
import Theorems.Thm_MIPRE_QLD_padded_lines_consistency
import Theorems.Thm_MIPRE_QLD_padded_lines_consistency_swap
import Theorems.Thm_MIPRE_QLD_povmValue_swapped_le
import Theorems.Thm_MIPRE_QLD_rep_add_lineParam_smul
import Theorems.Thm_MIPRE_QLD_sum_content_collProb_dPres
import Theorems.Thm_MIPRE_QLD_swapVec_unit
import Theorems.Thm_MIPRE_ancillaEmbed_isometry
import Theorems.Thm_MIPRE_condFail_le_one_sub_sum_bornProb_map
import Theorems.Thm_MIPRE_extVec2_unit
import Theorems.Thm_MIPRE_kron_one_mul_ancillaEmbed

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
section
open ComplexOrder Matrix
variable {n : Type*} [Fintype n]
variable {X A d : Type*} [Fintype X] [Fintype A] [Fintype d] [DecidableEq d]
/-- **A POVM is determined by its operators.** The remaining fields are propositions. -/
theorem POVM.ext' {M N : POVM A d} (h : ∀ a, (((M.mats a)).val) = (((N.mats a)).val)) : M = N := by
  have hm : M.mats = N.mats := funext fun a => Subtype.ext (h a)
  obtain ⟨mM, hM1, hM2⟩ := M
  obtain ⟨mN, hN1, hN2⟩ := N
  simp only at hm
  subst hm
  rfl
end
end MIPRE

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
/-- **Exchanging the two parties of the expanded state exchanges both factors.** -/
theorem swapVec_expVec (ψ : dA × dB → ℂ) (e : anc × anc' → ℂ) :
    swapVec (expVec ψ e) = expVec (swapVec ψ) (swapVec e) := rfl
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
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A] {d : Type*} [Fintype d] [DecidableEq d]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Relabelling along the identity does nothing. -/
theorem POVM.map_id (M : POVM A d) : M.map (fun a => a) = M :=
  POVM.ext' fun b => by
    rw [POVM.map_mats, Finset.sum_filter, Finset.sum_ite_eq' univ b fun a => (M.mats a).val]
    simp
end
end MIPRE

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

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {X Y A B C : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq C] {ψ : dA × dB → ℂ} {x : X} {y : Y}
/-- Forgetting the outcome altogether gives the identity operator. -/
theorem POVM.map_const_mats {A : Type*} [Fintype A] (P : POVM A dA) :
    ((P.map fun _ => ()).mats ()).val = 1 := by
  rw [POVM.map_mats, Finset.filter_true_of_mem fun _ _ => rfl, POVM.sum_val]
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

namespace MIPRE.LIDT.CL
section
open Finset MIPRE
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ}
theorem card_ty : Fintype.card Ty = 3 := rfl
end
end MIPRE.LIDT.CL

namespace MIPRE.LIDT.CL
section
open Finset MIPRE
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ}
omit [Field F] [DecidableEq F] in
theorem card_sample :
    Fintype.card (Sample F m) = 9 * Fintype.card (Point F m × F × Point F m) := by
  rw [Fintype.card_congr (sampleEquiv F m), Fintype.card_prod, Fintype.card_prod, card_ty]
end
end MIPRE.LIDT.CL

namespace MIPRE.LIDT.CL
section
open Finset MIPRE
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ}
omit [Field F] [DecidableEq F] in
/-- A sum over samples, as a sum over the two types and the ambient triple. -/
theorem sum_sample_eq {M : Type*} [AddCommMonoid M] (f : Sample F m → M) :
    ∑ sm, f sm
      = ∑ tA : Ty, ∑ tB : Ty, ∑ x : Point F m × F × Point F m,
          f ⟨tA, tB, x.1, x.2.1, x.2.2⟩ := by
  rw [Fintype.sum_equiv (sampleEquiv F m) f (fun p => f ((sampleEquiv F m).symm p))
    (fun sm => by rw [Equiv.symm_apply_apply]), Fintype.sum_prod_type, Fintype.sum_prod_type]
  rfl
end
end MIPRE.LIDT.CL

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem adj_point_aline (W : Bas) : adj (.point W) (.aline W) = true := by cases W <;> rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem adj_point_dline (W : Bas) : adj (.point W) (.dline W) = true := by cases W <;> rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
/-- The three components of an acceptance. -/
theorem of_accepts {x y : Question F m} {a b : Answer F m d}
    (h : accepts hm x y a b = true) :
    x.fmtOk a = true ∧ y.fmtOk b = true ∧ subtests hm x y a b = true := by
  rw [accepts, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem eq_val_of_fmtOk {W : Bas} {y : Point F m} {a : Answer F m d}
    (h : (Question.point W y).fmtOk a = true) : ∃ a', a = .val a' := by
  cases a <;> first | exact ⟨_, rfl⟩ | simp [Question.fmtOk] at h
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem eq_apoly_of_fmtOk {W : Bas} {u₀ : Point F m} {s : F} {a : Answer F m d}
    (h : (Question.aline W u₀ s).fmtOk a = true) : ∃ p, a = .apoly p := by
  cases a <;> first | exact ⟨_, rfl⟩ | simp [Question.fmtOk] at h
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem eq_dpoly_of_fmtOk {W : Bas} {u₀ : Point F m} {s : F} {w : Point F m} {a : Answer F m d}
    (h : (Question.dline W u₀ s w).fmtOk a = true) : ∃ p, a = .dpoly p := by
  cases a <;> first | exact ⟨_, rfl⟩ | simp [Question.fmtOk] at h
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
omit [Algebra (ZMod 2) F] [NeZero m] in
/-- The parameter agreement a line-against-point acceptance yields. -/
theorem eval_eq_of_lowDeg {n : ℕ} {u₀ w y : Point F m} {p : LinePoly F n} {a : F}
    (h : lowDeg u₀ w y p a = true) : p.eval (MIPRE.LIDT.CL.lineParam u₀ w y) = a :=
  (of_decide_eq_true h).2 0
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
omit [Algebra (ZMod 2) F] in
theorem d_le_mul : d ≤ m * d :=
  Nat.le_mul_of_pos_left d (Nat.pos_of_ne_zero (NeZero.ne m))
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
theorem m_le_mul (hd : 1 ≤ d) : m ≤ m * d :=
  Nat.le_mul_of_pos_right m hd
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **The axis-parallel line subtest, as the hypothesis the general estimate needs**: the line
answer, padded to degree `m d` and evaluated at the parameter of the sampled point, is the point
answer. This is item 2a of `lem:qld-win` with the padding added. -/
theorem hsub_aline {hm : m ∣ Fintype.card F} (W : Bas) (c : Content F m) (a b : Answer F m d)
    (h : accepts hm (c.question hm (.point W)) (c.question hm (.aline W)) a b = true) :
    rdVal a = (rdLine (m * d) b).eval
      (MIPRE.LIDT.CL.lineParam (abaseOf hm W c) (dirOf hm c) (c.pt W)) := by
  obtain ⟨hfa, hfb, hs⟩ := of_accepts h
  obtain ⟨a', rfl⟩ := eq_val_of_fmtOk hfa
  obtain ⟨p, rfl⟩ := eq_apoly_of_fmtOk hfb
  have hs' : lowDeg (MIPRE.LIDT.CL.rep (dirOf hm c) (c.pt W)) (dirOf hm c) (c.pt W) p a'
      = true := by
    simpa [subtests, Question.ty, Content.question, pairTest, dirOf] using hs
  rw [rdVal, rdLine, eval_padLine d_le_mul, abaseOf]
  exact (eval_eq_of_lowDeg hs').symm
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **The diagonal line subtest**, the same way: item 2b of `lem:qld-win`. -/
theorem hsub_dline {hm : m ∣ Fintype.card F} (W : Bas) (c : Content F m) (a b : Answer F m d)
    (h : accepts hm (c.question hm (.point W)) (c.question hm (.dline W)) a b = true) :
    rdVal a = (rdLine (m * d) b).eval
      (MIPRE.LIDT.CL.lineParam (dbaseOf hm W c) (ddirOf hm c) (c.pt W)) := by
  obtain ⟨hfa, hfb, hs⟩ := of_accepts h
  obtain ⟨a', rfl⟩ := eq_val_of_fmtOk hfa
  obtain ⟨p, rfl⟩ := eq_dpoly_of_fmtOk hfb
  have hs' : lowDeg (MIPRE.LIDT.CL.rep (ddirOf hm c) (c.pt W)) (ddirOf hm c) (c.pt W) p a'
      = true := by
    simpa [subtests, Question.ty, Content.question, pairTest, ddirOf] using hs
  rw [rdVal, rdLine, eval_padLine le_rfl, dbaseOf]
  exact (eval_eq_of_lowDeg hs').symm
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **`lem:qld-expanded-lines` for the axis-parallel line type.** The hatted line measurement has
outcomes the polynomials of degree at most `m d` on the line; it is self-consistent over the
line--point distribution at `172 eps`, and consistent with the expanded point measurements of
`lem:qld-expanded-points` at `172 eps` --- in the form that compares the *evaluation* of the line
polynomial at the sampled point, which at the Born level is also the form that compares the
outcomes. Projectivity is `isPVM_hatLinePOVM`, given a projective strategy. -/
theorem expanded_lines_aline (hd : 1 ≤ d) {ψ : dA × dB → ℂ} {hm : m ∣ Fintype.card F}
    {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
    {ε : ℝ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    (∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ f : LinePoly F (m * d), xSqNorm (hatVec (F := F) (m := m) ψ)
          (((hatLinePOVM (m * d) hm MA W (.aline W) (abaseOf hm W) (dirOf hm) c).mats f).val)
          (((hatLinePOVM (m * d) hm MB W (.aline W) (abaseOf hm W) (dirOf hm) c).mats f).val)
        ≤ 172 * ε)
      ∧ ∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
          ∑ a : F, xSqNorm (hatVec (F := F) (m := m) ψ) (((hatPOVM hm MA W c).mats a).val)
            ((((hatLinePOVM (m * d) hm MB W (.aline W) (abaseOf hm W) (dirOf hm) c).map
                (fun f => LinePoly.eval f
                  (MIPRE.LIDT.CL.lineParam (abaseOf hm W c) (dirOf hm c) (c.pt W)))).mats a).val)
          ≤ 172 * ε :=
  ⟨hatLinePOVM_consistency (MB := MB) hψ hfail W (.aline W) (abaseOf hm W) (dirOf hm),
    hatLinePOVM_point_consistency (MB := MB) (m_le_mul hd) hψ hfail W (.aline W)
      (adj_point_aline W) (abaseOf hm W) (dirOf hm)
      (fun c => rep_add_lineParam_smul (dirOf hm c) (c.pt W)) (hsub_aline W)⟩
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **`lem:qld-expanded-lines` for the diagonal line type**, the same two items. -/
theorem expanded_lines_dline (hd : 1 ≤ d) {ψ : dA × dB → ℂ} {hm : m ∣ Fintype.card F}
    {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
    {ε : ℝ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    (∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ f : LinePoly F (m * d), xSqNorm (hatVec (F := F) (m := m) ψ)
          (((hatLinePOVM (m * d) hm MA W (.dline W) (dbaseOf hm W) (ddirOf hm) c).mats f).val)
          (((hatLinePOVM (m * d) hm MB W (.dline W) (dbaseOf hm W) (ddirOf hm) c).mats f).val)
        ≤ 172 * ε)
      ∧ ∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
          ∑ a : F, xSqNorm (hatVec (F := F) (m := m) ψ) (((hatPOVM hm MA W c).mats a).val)
            ((((hatLinePOVM (m * d) hm MB W (.dline W) (dbaseOf hm W) (ddirOf hm) c).map
                (fun f => LinePoly.eval f
                  (MIPRE.LIDT.CL.lineParam (dbaseOf hm W c) (ddirOf hm c) (c.pt W)))).mats a).val)
          ≤ 172 * ε :=
  ⟨hatLinePOVM_consistency (MB := MB) hψ hfail W (.dline W) (dbaseOf hm W) (ddirOf hm),
    hatLinePOVM_point_consistency (MB := MB) (m_le_mul hd) hψ hfail W (.dline W)
      (adj_point_dline W) (dbaseOf hm W) (ddirOf hm)
      (fun c => rep_add_lineParam_smul (ddirOf hm c) (c.pt W)) (hsub_dline W)⟩
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ}
variable [Algebra (ZMod 2) F] [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- The expanded state's two halves are exchanged by the swap. -/
theorem hatVec_swapVec (ψ : dA × dB → ℂ) :
    hatVec (F := F) (m := m) (swapVec ψ) = swapVec (hatVec (F := F) (m := m) ψ) := by
  rw [hatVec, hatVec, swapVec_expVec, swapVec_epr]
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
theorem sum_uniform_content : ∑ _c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ = 1 := by
  have hpos : 0 < Fintype.card (Content F m) :=
    Fintype.card_pos_iff.mpr ⟨⟨0, 0, 0, 0, 0, 0⟩⟩
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hpos.ne')
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {hm : m ∣ Fintype.card F} {W : Bas}
/-- **The axis-parallel direction is never degenerate**: it is a standard basis vector. -/
theorem aPres_dir_ne_zero (hm : m ∣ Fintype.card F) (W : Bas) (c : Content F m) :
    ∃ j, (aPres hm W).dir c j ≠ 0 := by
  refine ⟨MIPRE.LIDT.CL.chi hm c.s, ?_⟩
  show (dirOf hm c) (MIPRE.LIDT.CL.chi hm c.s) ≠ 0
  rw [dirOf, Pi.single_eq_same]
  exact one_ne_zero
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ} {ε : ℝ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
/-- **The axis-parallel collision probability is `m d / q`**, the direction being a standard basis
vector and so never degenerate. -/
theorem sum_content_collProb_aPres (hm : m ∣ Fintype.card F) (W : Bas) (d : ℕ) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * collProb (aPres hm W) d c
      = (m * d : ℝ) / (Fintype.card F : ℝ) := by
  rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => show
      (Fintype.card (Content F m) : ℝ)⁻¹ * collProb (aPres hm W) d c
        = (Fintype.card (Content F m) : ℝ)⁻¹ * ((m * d : ℝ) / (Fintype.card F : ℝ)) from by
    rw [collProb, if_pos (aPres_dir_ne_zero hm W c)], ← Finset.sum_mul, sum_uniform_content,
    one_mul]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ} {ε : ℝ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
/-- The two items for an axis-parallel presentation. -/
theorem aPres_items (hd : 1 ≤ d) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ f : LinePoly F (m * d),
        xSqNorm (hatVec (F := F) (m := m) ψ) ((aPres hm W).lineMats d MA c f)
          ((aPres hm W).lineMats d MB c f) ≤ 172 * ε)
      ∧ ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
          xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA W (c.pt W) a)
            ((aPres hm W).lineEvalMats d MB c a) ≤ 172 * ε := by
  obtain ⟨h1, h2⟩ := expanded_lines_aline (MB := MB) hd hψ hfail W
  refine ⟨h1, le_trans (le_of_eq (Finset.sum_congr rfl fun c _ =>
    congrArg (fun t : ℝ => (Fintype.card (Content F m) : ℝ)⁻¹ * t)
      (Finset.sum_congr rfl fun a _ => ?_))) h2⟩
  rw [← hatPOVM_mats_eq hm MA W c a]
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
  {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ} {ε : ℝ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
/-- The two items for a diagonal presentation. -/
theorem dPres_items (hd : 1 ≤ d) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ f : LinePoly F (m * d),
        xSqNorm (hatVec (F := F) (m := m) ψ) ((dPres hm W).lineMats d MA c f)
          ((dPres hm W).lineMats d MB c f) ≤ 172 * ε)
      ∧ ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
          xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA W (c.pt W) a)
            ((dPres hm W).lineEvalMats d MB c a) ≤ 172 * ε := by
  obtain ⟨h1, h2⟩ := expanded_lines_dline (MB := MB) hd hψ hfail W
  refine ⟨h1, le_trans (le_of_eq (Finset.sum_congr rfl fun c _ =>
    congrArg (fun t : ℝ => (Fintype.card (Content F m) : ℝ)⁻¹ * t)
      (Finset.sum_congr rfl fun a _ => ?_))) h2⟩
  rw [← hatPOVM_mats_eq hm MA W c a]
  rfl
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
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **Swapping the state exchanges the two arguments of the cross-party deviation.** -/
theorem xSqNorm_swapVec (ψ : dA × dB → ℂ) (X : Matrix dB dB ℂ) (Y : Matrix dA dA ℂ) :
    xSqNorm (swapVec ψ) X Y = xSqNorm ψ Y X := by
  rw [xSqNorm_eq_snorm_sq, snorm_swapVec_aOp_sub_bOp, xSqNorm_eq_sq]
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
theorem padStrat_point {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u : Point F (4 * m)) :
    padStrat hm hm4 hM (.point u) = (padPt hM u).map fun a => .values fun _ => a := rfl
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
theorem exists_of_padStrat_point_mats_ne_zero {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u : Point F (4 * m))
    {a : CL.Answer F (4 * m) d 1} (h : ((padStrat hm hm4 hM (.point u)).mats a).val ≠ 0) :
    ∃ c : F, a = .values fun _ => c := by
  by_contra hne
  exact h (POVM.map_mats_eq_zero_of_forall_ne _ _ fun c hc => hne ⟨c, hc.symm⟩)
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
/-- The strategy's point answer, read back as a field element, is the padded point measurement. -/
theorem padStrat_point_map_toValue {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u : Point F (4 * m)) :
    (padStrat hm hm4 hM (.point u)).map CL.Answer.toValue = padPt hM u := by
  rw [padStrat_point, POVM.map_map]
  exact POVM.map_id _
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
/-- A line answer read at the parameter of the sampled point, against the point answer there: the
decider accepts. -/
theorem accepts_lineQ_point (ty : CL.Ty) (hty : ty ≠ .point) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) (f : LinePoly F (m * d + 1)) (c : F)
    (h : rdEval (lineTau hm4 ty u s raw) (lineAns ty f) = c) :
    CL.accepts hm4 (lineQ hm4 ty u s raw) (.point u) (lineAns ty f) (CL.Answer.values fun _ => c) =
    true := by
  have hon : ∃ t, u = CL.rep (lineDir hm4 ty s raw) u + t • lineDir hm4 ty s raw :=
    ⟨lineTau hm4 ty u s raw, (rep_add_lineParam_smul _ u).symm⟩
  cases ty
  · exact absurd rfl hty
  · simp only [lineQ_aline, lineAns, alineAns, CL.accepts, CL.Question.fmtOk, CL.subtests,
      Bool.true_and, CL.lineVsPoint, decide_eq_true_eq]
    exact ⟨hon, fun _ => h⟩
  · simp only [lineQ_dline, lineAns, dlineAns, CL.accepts, CL.Question.fmtOk, CL.subtests,
      Bool.true_and, CL.lineVsPoint, decide_eq_true_eq]
    exact ⟨hon, fun _ => h⟩
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
/-- The same with the players exchanged. -/
theorem accepts_point_lineQ (ty : CL.Ty) (hty : ty ≠ .point) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) (f : LinePoly F (m * d + 1)) (c : F)
    (h : c = rdEval (lineTau hm4 ty u s raw) (lineAns ty f)) :
    CL.accepts hm4 (.point u) (lineQ hm4 ty u s raw) (CL.Answer.values fun _ => c) (lineAns ty f) =
    true := by
  have hon : ∃ t, u = CL.rep (lineDir hm4 ty s raw) u + t • lineDir hm4 ty s raw :=
    ⟨lineTau hm4 ty u s raw, (rep_add_lineParam_smul _ u).symm⟩
  cases ty
  · exact absurd rfl hty
  · simp only [lineQ_aline, lineAns, alineAns, CL.accepts, CL.Question.fmtOk, CL.subtests,
      Bool.true_and, CL.lineVsPoint, decide_eq_true_eq]
    exact ⟨hon, fun _ => h.symm⟩
  · simp only [lineQ_dline, lineAns, dlineAns, CL.accepts, CL.Question.fmtOk, CL.subtests,
      Bool.true_and, CL.lineVsPoint, decide_eq_true_eq]
    exact ⟨hon, fun _ => h.symm⟩
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
theorem accepts_point_self (u : Point F (4 * m)) (a : Fin 1 → F) :
    CL.accepts (d := d) hm4 (.point u) (.point u) (CL.Answer.values a) (CL.Answer.values a)
      = true := by
  simp [CL.accepts, CL.Question.fmtOk, CL.subtests]
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
/-- **Alice's line against Bob's point**: the conditional failure is at most the disagreement of
Alice's line measurement read at the sample's point with Bob's padded point measurement. -/
theorem condFail_lineQ_point_le (ty : CL.Ty) (hty : ty ≠ .point) (hd : 1 ≤ d)
    (hlegA : LegalSupport MA) (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m)) :
    condFail (clGame (d := d) (ldc := 1) hm4) Ψ (padStrat hm hm4 hMA) (padStrat hm hm4 hMB)
        (lineQ hm4 ty u s raw) (.point u)
      ≤ 1 - ∑ a, bornProb Ψ
          ((((lineMeas hm hm4 ty hMA (CL.rep (lineDir hm4 ty s raw) u) s (rawSet hm4 ty s raw)).map
            fun f => LinePoly.eval f (lineTau hm4 ty u s raw)).mats a).val)
          (((padPt hMB u).mats a).val) := by
  rw [← padStrat_lineQ_map_rdEval hm hm4 ty hty hd hMA hlegA u s raw,
    ← padStrat_point_map_toValue hm hm4 hMB u]
  refine condFail_le_one_sub_sum_bornProb_map _ _ fun a b ha hb hab => ?_
  obtain ⟨f, rfl⟩ := exists_of_padStrat_lineQ_mats_ne_zero hm hm4 ty hty hMA u s raw ha
  obtain ⟨c, rfl⟩ := exists_of_padStrat_point_mats_ne_zero hm hm4 hMB u hb
  exact accepts_lineQ_point hm4 ty hty u s raw f c hab
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
/-- **Alice's point against Bob's line.** -/
theorem condFail_point_lineQ_le (ty : CL.Ty) (hty : ty ≠ .point) (hd : 1 ≤ d)
    (hlegB : LegalSupport MB) (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m)) :
    condFail (clGame (d := d) (ldc := 1) hm4) Ψ (padStrat hm hm4 hMA) (padStrat hm hm4 hMB)
        (.point u) (lineQ hm4 ty u s raw)
      ≤ 1 - ∑ a, bornProb Ψ (((padPt hMA u).mats a).val)
          ((((lineMeas hm hm4 ty hMB (CL.rep (lineDir hm4 ty s raw) u) s (rawSet hm4 ty s raw)).map
            fun f => LinePoly.eval f (lineTau hm4 ty u s raw)).mats a).val) := by
  rw [← padStrat_lineQ_map_rdEval hm hm4 ty hty hd hMB hlegB u s raw,
    ← padStrat_point_map_toValue hm hm4 hMA u]
  refine condFail_le_one_sub_sum_bornProb_map _ _ fun a b ha hb hab => ?_
  obtain ⟨c, rfl⟩ := exists_of_padStrat_point_mats_ne_zero hm hm4 hMA u ha
  obtain ⟨f, rfl⟩ := exists_of_padStrat_lineQ_mats_ne_zero hm hm4 ty hty hMB u s raw hb
  exact accepts_point_lineQ hm4 ty hty u s raw f c hab
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
/-- **Identical points**: the conditional failure is at most the disagreement of the two padded
point measurements. -/
theorem condFail_point_point_le (u : Point F (4 * m)) :
    condFail (clGame (d := d) (ldc := 1) hm4) Ψ (padStrat hm hm4 hMA) (padStrat hm hm4 hMB)
        (.point u) (.point u)
      ≤ 1 - ∑ a, bornProb Ψ (((padPt hMA u).mats a).val) (((padPt hMB u).mats a).val) := by
  rw [← padStrat_point_map_toValue hm hm4 hMA u, ← padStrat_point_map_toValue hm hm4 hMB u]
  refine condFail_le_one_sub_sum_bornProb_map _ _ fun a b ha hb hab => ?_
  obtain ⟨c, rfl⟩ := exists_of_padStrat_point_mats_ne_zero hm hm4 hMA u ha
  obtain ⟨c', rfl⟩ := exists_of_padStrat_point_mats_ne_zero hm hm4 hMB u hb
  have hc : c = c' := hab
  subst hc
  exact accepts_point_self (d := d) hm4 u _
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
/-- **The two cross type pairs are always accepted**: the strategy answers in the right format, and
the decider checks nothing else. -/
theorem condFail_aline_dline_le (hΨ : star Ψ ⬝ᵥ Ψ = 1) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) (u' : Point F (4 * m)) (s' : F) (raw' : Point F (4 * m)) :
    condFail (clGame (d := d) (ldc := 1) hm4) Ψ (padStrat hm hm4 hMA) (padStrat hm hm4 hMB)
        (lineQ hm4 .aline u s raw) (lineQ hm4 .dline u' s' raw') ≤ 0 := by
  refine le_trans (condFail_le_one_sub_sum_bornProb_map (fun _ => ()) (fun _ => ())
    fun a b ha hb _ => ?_) ?_
  · obtain ⟨f, rfl⟩ := exists_of_padStrat_lineQ_mats_ne_zero hm hm4 .aline (by decide) hMA u s raw
      ha
    obtain ⟨g, rfl⟩ := exists_of_padStrat_lineQ_mats_ne_zero hm hm4 .dline (by decide) hMB u' s'
        raw' hb
    rfl
  · rw [Fintype.sum_unique, POVM.map_const_mats, POVM.map_const_mats, bornProb_one_one hΨ]
    norm_num
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
theorem condFail_dline_aline_le (hΨ : star Ψ ⬝ᵥ Ψ = 1) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) (u' : Point F (4 * m)) (s' : F) (raw' : Point F (4 * m)) :
    condFail (clGame (d := d) (ldc := 1) hm4) Ψ (padStrat hm hm4 hMA) (padStrat hm hm4 hMB)
        (lineQ hm4 .dline u s raw) (lineQ hm4 .aline u' s' raw') ≤ 0 := by
  refine le_trans (condFail_le_one_sub_sum_bornProb_map (fun _ => ()) (fun _ => ())
    fun a b ha hb _ => ?_) ?_
  · obtain ⟨f, rfl⟩ := exists_of_padStrat_lineQ_mats_ne_zero hm hm4 .dline (by decide) hMA u s raw
      ha
    obtain ⟨g, rfl⟩ := exists_of_padStrat_lineQ_mats_ne_zero hm hm4 .aline (by decide) hMB u' s'
        raw' hb
    rfl
  · rw [Fintype.sum_unique, POVM.map_const_mats, POVM.map_const_mats, bornProb_one_one hΨ]
    norm_num
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
/-- A dilated point measurement on Bob's side, coarse-grained, against anything on Alice's: only
its compression matters. -/
theorem bornProb_extHat_ptComb_right {x z : Point F m}
    (QB : F × F → Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ)
    (hk : ∀ r, (ancillaEmbed (dB × Anc F m) ((0 : F), (0 : F)))ᴴ
        * (QB r * ancillaEmbed (dB × Anc F m) ((0 : F), (0 : F)))
      = sand (hatMats MB .X x) (hatMats MB .Z z) r)
    (E : Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ) (a b v : F) :
    bornProb (extHat (F := F) (m := m) ψ) E (ptComb QB a b v)
      = bornProb (extHat (F := F) (m := m) ψ) E
          (aOp (ptComb (sand (hatMats MB .X x) (hatMats MB .Z z)) a b v)) := by
  rw [extHat, bornProb_extVec2, bornProb_extVec2, compress_aOp]
  congr 1
  rw [ptComb, Matrix.sum_mul, Matrix.mul_sum, ptComb]
  exact Finset.sum_congr rfl fun r _ => hk r
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
/-- The same on Alice's side. -/
theorem bornProb_extHat_ptComb_left {x z : Point F m}
    (QA : F × F → Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ)
    (hk : ∀ r, (ancillaEmbed (dA × Anc F m) ((0 : F), (0 : F)))ᴴ
        * (QA r * ancillaEmbed (dA × Anc F m) ((0 : F), (0 : F)))
      = sand (hatMats MA .X x) (hatMats MA .Z z) r)
    (G : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ) (a b v : F) :
    bornProb (extHat (F := F) (m := m) ψ) (ptComb QA a b v) G
      = bornProb (extHat (F := F) (m := m) ψ)
          (aOp (ptComb (sand (hatMats MA .X x) (hatMats MA .Z z)) a b v)) G := by
  rw [extHat, bornProb_extVec2, bornProb_extVec2, compress_aOp]
  congr 1
  rw [ptComb, Matrix.sum_mul, Matrix.mul_sum, ptComb]
  exact Finset.sum_congr rfl fun r _ => hk r
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
/-- The two items of `lem:qld-expanded-lines` for the presentation of a line type. -/
theorem presOf_items (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (hd :
    1 ≤ d) (ty : CL.Ty) (W : Bas) :
    (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ f : LinePoly F (m * d),
        xSqNorm (hatVec (F := F) (m := m) ψ) ((presOf hm ty W).lineMats d MA c f)
          ((presOf hm ty W).lineMats d MB c f) ≤ 172 * ε)
      ∧ ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
          xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA W (c.pt W) a)
            ((presOf hm ty W).lineEvalMats d MB c a) ≤ 172 * ε := by
  cases ty
  · exact aPres_items (MB := MB) hd hψ hfail W
  · exact aPres_items (MB := MB) hd hψ hfail W
  · exact dPres_items (MB := MB) hd hψ hfail W
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
/-- The second item with the players exchanged: Alice's line read at the point against Bob's
point measurement. -/
theorem presOf_items_swap (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hd : 1 ≤ d) (ty : CL.Ty) (W : Bas) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        xSqNorm (hatVec (F := F) (m := m) ψ) ((presOf hm ty W).lineEvalMats d MA c a)
          (hatMats MB W (c.pt W) a) ≤ 172 * ε := by
  have h := (presOf_items hm (MA := MB) (MB := MA) (ψ := swapVec ψ) (swapVec_unit hψ)
    (povmValue_swapped_le hfail) hd ty W).2
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ =>
    congrArg (fun t : ℝ => (Fintype.card (Content F m) : ℝ)⁻¹ * t)
      (Finset.sum_congr rfl fun a _ => ?_))) h
  rw [hatVec_swapVec, xSqNorm_swapVec]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
/-- The collision probability of the `X` presentation of a line type is at most `md/q + 1/q`. -/
theorem presOf_coll (ty : CL.Ty) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * collProb (presOf hm ty .X) d c
      ≤ (m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹ := by
  cases ty
  · rw [show presOf hm .point .X = aPres hm .X from rfl, sum_content_collProb_aPres]
    exact le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))
  · rw [show presOf hm .aline .X = aPres hm .X from rfl, sum_content_collProb_aPres]
    exact le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))
  · exact sum_content_collProb_dPres hm .X d
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
/-- **Alice's line against Bob's point, at a fixed seed**: `lem:qld-padded-lines` in the other
register version, with the dilated point measurement replaced by the strategy's sandwich. -/
theorem one_sub_avgSubAB_padGL_le (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA
    MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d) (ty : CL.Ty) (s : F) :
    1 - avgSubAB hm4 hm ty s (padGL hm (extHat (F := F) (m := m) ψ) MA MB ty)
      ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) := by
  obtain ⟨QB, -, hkB, hb⟩ := padded_lines_consistency_swap hm4 hψ hfail hprojA hprojB
    (presOf hm ty .X) (presOf hm ty .Z) (factorsX_presOf hm ty) (factorsZ_presOf hm ty)
    (presOf_items hm hψ hfail hd ty .X).1 (presOf_items_swap hm hψ hfail hd ty .X)
    (presOf_items_swap hm hψ hfail hd ty .Z) (presOf_coll hm ty) ty s
  refine le_trans (le_of_eq (congrArg (fun t : ℝ => 1 - t)
    (congrArg (avgSubAB hm4 hm ty s) ?_))) hb
  funext a b cX cZ
  refine Finset.sum_congr rfl fun v _ => ?_
  exact (bornProb_extHat_ptComb_right (QB (cX, cZ)) (hkB (cX, cZ)) _ a b v).symm
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
/-- **Alice's point against Bob's line, at a fixed seed.** -/
theorem one_sub_avgSubAB_padGR_le (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA
    MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d) (ty : CL.Ty) (s : F) :
    1 - avgSubAB hm4 hm ty s (padGR hm (extHat (F := F) (m := m) ψ) MA MB ty)
      ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) := by
  obtain ⟨QA, -, hkA, hb⟩ := padded_lines_consistency hm4 hψ hfail hprojA hprojB
    (presOf hm ty .X) (presOf hm ty .Z) (factorsX_presOf hm ty) (factorsZ_presOf hm ty)
    (presOf_items hm hψ hfail hd ty .X).1 (presOf_items hm hψ hfail hd ty .X).2
    (presOf_items hm hψ hfail hd ty .Z).2 (presOf_coll hm ty) ty s
  refine le_trans (le_of_eq (congrArg (fun t : ℝ => 1 - t)
    (congrArg (avgSubAB hm4 hm ty s) ?_))) hb
  funext a b cX cZ
  refine Finset.sum_congr rfl fun v _ => ?_
  exact (bornProb_extHat_ptComb_left (QA (cX, cZ)) (hkA (cX, cZ)) _ a b v).symm
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
/-- **The line-point subtests, Alice's line**: the agreement of Alice's line measurement read at
the sample's point with Bob's padded point measurement, averaged over the ambient sample. -/
theorem one_sub_agreeSum_lineEval_pt_le (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm)
    ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d) (ty : CL.Ty)
    (hty : ty ≠ .point) :
    1 - agreeSum (uniform (Amb F m)) (extHat (F := F) (m := m) ψ) (lineEvalFam hm hm4 ty hprojA)
        (ptFam hprojB)
      ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) := by
  rw [agreeSum_lineEvalFam_ptFam hm hm4 hprojA hprojB _ ty hty]
  exact one_sub_inv_card_mul_sum_le fun s =>
    one_sub_avgSubAB_padGL_le hm hm4 hψ hfail hprojA hprojB hd ty s
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
/-- **The line-point subtests, Bob's line.** -/
theorem one_sub_agreeSum_pt_lineEval_le (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm)
    ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d) (ty : CL.Ty)
    (hty : ty ≠ .point) :
    1 - agreeSum (uniform (Amb F m)) (extHat (F := F) (m := m) ψ) (ptFam hprojA)
        (lineEvalFam hm hm4 ty hprojB)
      ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) := by
  rw [agreeSum_ptFam_lineEvalFam hm hm4 hprojA hprojB _ ty hty]
  exact one_sub_inv_card_mul_sum_le fun s =>
    one_sub_avgSubAB_padGR_le hm hm4 hψ hfail hprojA hprojB hd ty s
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

namespace MIPRE.QLD
noncomputable section
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
theorem padW_point_point_le : padW hm hm4 ψ hprojA hprojB .point .point ≤ deltaQ ε := by
  have h := one_sub_agreeSum_pt_pt_le hm hψ hfail hprojA hprojB
  rw [one_sub_agreeSum_uniform_eq] at h
  refine le_trans (Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left ?_ (uniform_amb_nonneg x)) h
  exact condFail_point_point_le hm hm4 hprojA hprojB _ x.1
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
  {ε : ℝ}
variable {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
  (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
  (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
include hψ hfail in
theorem padW_line_point_le (hd : 1 ≤ d) (hlegA : LegalSupport MA) (ty : CL.Ty) (hty : ty ≠ .point) :
    padW hm hm4 ψ hprojA hprojB ty .point
      ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) := by
  have h := one_sub_agreeSum_lineEval_pt_le hm hm4 hψ hfail hprojA hprojB hd ty hty
  rw [one_sub_agreeSum_uniform_eq] at h
  refine le_trans (Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left ?_ (uniform_amb_nonneg x)) h
  exact condFail_lineQ_point_le hm hm4 hprojA hprojB _ ty hty hd hlegA x.1 x.2.1 x.2.2
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
  {ε : ℝ}
variable {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
  (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
  (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
include hψ hfail in
theorem padW_point_line_le (hd : 1 ≤ d) (hlegB : LegalSupport MB) (ty : CL.Ty) (hty : ty ≠ .point) :
    padW hm hm4 ψ hprojA hprojB .point ty
      ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) := by
  have h := one_sub_agreeSum_pt_lineEval_le hm hm4 hψ hfail hprojA hprojB hd ty hty
  rw [one_sub_agreeSum_uniform_eq] at h
  refine le_trans (Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left ?_ (uniform_amb_nonneg x)) h
  exact condFail_point_lineQ_le hm hm4 hprojA hprojB _ ty hty hd hlegB x.1 x.2.1 x.2.2
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
  {ε : ℝ}
variable {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
  (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
  (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
include hψ in
theorem padW_aline_dline_le : padW hm hm4 ψ hprojA hprojB .aline .dline ≤ 0 := by
  have hΨ : star (extHat (F := F) (m := m) ψ) ⬝ᵥ extHat (F := F) (m := m) ψ = 1 :=
    extVec2_unit (hatVec_unit hψ) _ _
  refine le_trans (Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
    (condFail_aline_dline_le hm hm4 hprojA hprojB _ hΨ x.1 x.2.1 x.2.2 x.1 x.2.1 x.2.2)
    (uniform_amb_nonneg x)) ?_
  simp
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
  {ε : ℝ}
variable {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
  (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
  (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
include hψ in
theorem padW_dline_aline_le : padW hm hm4 ψ hprojA hprojB .dline .aline ≤ 0 := by
  have hΨ : star (extHat (F := F) (m := m) ψ) ⬝ᵥ extHat (F := F) (m := m) ψ = 1 :=
    extVec2_unit (hatVec_unit hψ) _ _
  refine le_trans (Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
    (condFail_dline_aline_le hm hm4 hprojA hprojB _ hΨ x.1 x.2.1 x.2.2 x.1 x.2.1 x.2.2)
    (uniform_amb_nonneg x)) ?_
  simp
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
  {ε : ℝ}
variable {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
  (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
  (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
omit [DecidableEq F] [Algebra (ZMod 2) F] in
theorem Sample.question_fst_eq_lineQ (tA tB : CL.Ty) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) :
    (⟨tA, tB, u, s, raw⟩ : CL.Sample F (4 * m)).question hm4 tA = lineQ hm4 tA u s raw := by
  cases tA <;> rfl
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
  {ε : ℝ}
variable {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
  (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
  (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
omit [DecidableEq F] [Algebra (ZMod 2) F] in
theorem Sample.question_snd_eq_lineQ (tA tB : CL.Ty) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) :
    (⟨tA, tB, u, s, raw⟩ : CL.Sample F (4 * m)).question hm4 tB = lineQ hm4 tB u s raw := by
  cases tB <;> rfl
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
  {ε : ℝ}
variable {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
  (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
  (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- A sum over the three question types. -/
theorem sum_ty (f : CL.Ty → ℝ) : ∑ t, f t = f .point + f .aline + f .dline := by
  show ∑ t ∈ ({CL.Ty.point, CL.Ty.aline, CL.Ty.dline} : Finset CL.Ty), f t = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
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
  {ε : ℝ}
variable {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
  (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
  (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
/-- **The failure probability of the padded strategy is the average over the nine ordered type
pairs of their failure weights.** -/
theorem one_sub_povmValue_padStrat_eq :
    1 - povmValue (clGame (d := d) (ldc := 1) hm4) (extHat (F := F) (m := m) ψ)
        (padStrat hm hm4 hprojA) (padStrat hm hm4 hprojB)
      = (9 : ℝ)⁻¹ * ∑ tA : CL.Ty, ∑ tB : CL.Ty, padW hm hm4 ψ hprojA hprojB tA tB := by
  rw [one_sub_povmValue_clGame hm4, sum_sample_eq, card_sample]
  simp only [Sample.question_fst_eq_lineQ, Sample.question_snd_eq_lineQ, padW, uniform,
    Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun tA _ => Finset.sum_congr rfl fun tB _ =>
    Finset.sum_congr rfl fun x _ => ?_
  rw [mul_inv, mul_assoc]
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
theorem _root_.solution (hε : 0 ≤ ε) (hlegA : LegalSupport MA) (hlegB : LegalSupport MB)
    (hd : 1 ≤ d) :
    1 - povmValue (clGame (d := d) (ldc := 1) hm4) (extHat (F := F) (m := m) ψ)
        (padStrat hm hm4 hprojA) (padStrat hm hm4 hprojB)
      ≤ 5 * ((m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹))
        + 4 * deltaQ ε + ((m : ℝ) * d + 1) / Fintype.card F := by
  rw [one_sub_povmValue_padStrat_eq hm hm4 hprojA hprojB, sum_ty, sum_ty, sum_ty, sum_ty]
  have hpp := padW_point_point_le hm hm4 hψ hfail hprojA hprojB
  have hap := padW_line_point_le hm hm4 hψ hfail hprojA hprojB hd hlegA .aline (by decide)
  have hdp := padW_line_point_le hm hm4 hψ hfail hprojA hprojB hd hlegA .dline (by decide)
  have hpa := padW_point_line_le hm hm4 hψ hfail hprojA hprojB hd hlegB .aline (by decide)
  have hpd := padW_point_line_le hm hm4 hψ hfail hprojA hprojB hd hlegB .dline (by decide)
  have haa := padW_line_line_le hm hm4 hψ hfail hprojA hprojB hε hd .aline (by decide)
  have hdd := padW_line_line_le hm hm4 hψ hfail hprojA hprojB hε hd .dline (by decide)
  have had := padW_aline_dline_le hm hm4 hψ hprojA hprojB
  have hda := padW_dline_aline_le hm hm4 hψ hprojA hprojB
  have hQ0 : 0 ≤ deltaQ ε := by
    unfold deltaQ
    positivity
  have hP0 : 0 ≤ (m : ℝ) * m
      * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) := by
    unfold deltaPairs deltaPairsD kappaPairs deltaQ
    positivity
  have hR0 : 0 ≤ ((m : ℝ) * d + 1) / Fintype.card F := by positivity
  have hq1 : (Fintype.card F : ℝ)⁻¹ ≤ ((m : ℝ) * d + 1) / Fintype.card F := by
    rw [div_eq_mul_inv]
    exact le_mul_of_one_le_left (inv_nonneg.mpr (Nat.cast_nonneg _))
      (le_add_of_nonneg_left (by positivity))
  linarith
end MIPRE.QLD
