-- Prove2me | solution 1 for MIPRE.QLD.pairs_of_lines_gen
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:28:03.992896+00:00
-- url     : https://prove2.me/submissions/52cb1075-6404-447c-908e-30096935c82d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Lines.lean (solution of MIPRE.QLD.pairs_of_lines_gen);
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
import Theorems.Thm_MIPRE_IsPVM_aOp
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_QLD_card_collide_le
import Theorems.Thm_MIPRE_QLD_hatVec_unit
import Theorems.Thm_MIPRE_QLD_pasteJ_eq_pasteLine
import Theorems.Thm_MIPRE_QLD_sum_shift_gen
import Theorems.Thm_MIPRE_Weyl_isPVM_synOf
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_extVec2_unit
import Theorems.Thm_MIPRE_kronecker_sum_right
import Theorems.Thm_MIPRE_one_sub_sum_bornProb_pasteJ_le
import Theorems.Thm_MIPRE_sum_collisionTerm_le
import Theorems.Thm_MIPRE_sum_kronecker_left

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem norm_evec_eq_one_of_unit {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) : ‖evec ψ‖ = 1 := by
  have h : ‖evec ψ‖ ^ 2 = 1 := by rw [norm_evec_sq, hψ, Complex.one_re]
  nlinarith [norm_nonneg (evec ψ), h]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
/-- The question distribution of the pasting lemma: a weight on the part both measurements see,
times the uniform distribution on the probe that separates the second family's outcomes. -/
theorem sum_prod_uniform {Z Y : Type*} [Fintype Z] [Fintype Y] [Nonempty Y] (ν : Z → ℝ)
    (f : Z → ℝ) :
    ∑ i : Z × Y, (ν i.1 * (Fintype.card Y : ℝ)⁻¹) * f i.1 = ∑ z : Z, ν z * f z := by
  classical
  have hY : (Fintype.card Y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
/-- The product question distribution is a distribution. -/
theorem sum_prod_uniform_one {Z Y : Type*} [Fintype Z] [Fintype Y] [Nonempty Y] {ν : Z → ℝ}
    (hν : ∑ z, ν z = 1) :
    ∑ i : Z × Y, ν i.1 * (Fintype.card Y : ℝ)⁻¹ = 1 := by
  have h := sum_prod_uniform (Y := Y) ν fun _ => 1
  simp only [mul_one] at h
  rw [h, hν]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
/-- **A projective family stays projective under a relabelling of its outcomes by a bijection.** -/
theorem IsPVM.comp_equiv {N ι κ : Type*} [Fintype N] [DecidableEq N] [Fintype ι] [Fintype κ]
    {P : ι → Matrix N N ℂ} (h : IsPVM P) (e : κ ≃ ι) : IsPVM fun k => P (e k) where
  isSelfAdjoint k := h.isSelfAdjoint (e k)
  idem k := h.idem (e k)
  sum_eq_one := by
    rw [← h.sum_eq_one]
    exact Fintype.sum_bijective e e.bijective _ _ fun k => rfl
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
  [NeZero m]
theorem Content.shiftAlong_eq (W : Bas) (dir : Content F m → Point F m) (t : F)
    (c : Content F m) :
    Content.shiftAlong W dir t c = Content.shiftPt W (t • dir c) c := rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
/-- **The line measurement depends on the content only through the line.** -/
theorem hatLinePOVM_congr {d' : Type} [Fintype d'] [DecidableEq d'] {n : ℕ}
    (hm : m ∣ Fintype.card F) (M : Question F m → POVM (Answer F m d) d') (W : Bas) (ty : Ty)
    (base dir : Content F m → Point F m) {c c' : Content F m}
    (hq : c.question hm ty = c'.question hm ty) (hb : base c = base c') (hd : dir c = dir c') :
    hatLinePOVM n hm M W ty base dir c = hatLinePOVM n hm M W ty base dir c' := by
  rw [hatLinePOVM, hatLinePOVM, lineAnsPOVM, lineAnsPOVM, hq, hb, hd]
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

namespace MIPRE.QLD.LinePres
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {hm : m ∣ Fintype.card F} {W : Bas}
theorem isPVM_lineEvalMats {d' : Type} [Fintype d'] [DecidableEq d'] (P : LinePres F m hm W) (d : ℕ)
    {M : Question F m → POVM (Answer F m d) d'}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (c : Content F m) :
    IsPVM (P.lineEvalMats d M c) :=
  isPVM_povm_map _ (isPVM_hatLinePOVM (hM (c.question hm P.ty))) _
end
end MIPRE.QLD.LinePres

namespace MIPRE.QLD.LinePres
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {hm : m ∣ Fintype.card F} {W : Bas}
/-- The coarse-graining, as a fibre sum --- the shape the pasting lemma states its hypotheses
in. -/
theorem lineEvalMats_eq_fibSum {d' : Type} [Fintype d'] [DecidableEq d'] (P : LinePres F m hm W)
    (d : ℕ) (M : Question F m → POVM (Answer F m d) d') (c : Content F m) (a : F) :
    P.lineEvalMats d M c a = fibSum (P.lineMats d M c) (fun f => LinePoly.eval f (P.param c)) a :=
  AddSubmonoidClass.coe_finsetSum _ _
end
end MIPRE.QLD.LinePres

namespace MIPRE.QLD.LinePres
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {hm : m ∣ Fintype.card F} {W : Bas}
/-- **The line measurement is invariant under the shift**, the presentation's three invariances
being exactly what the measurement reads. -/
theorem lineMats_shiftAlong {d' : Type} [Fintype d'] [DecidableEq d'] (P : LinePres F m hm W) (d : ℕ)
    (M : Question F m → POVM (Answer F m d) d') (c : Content F m) (t : F) :
    P.lineMats d M (Content.shiftAlong W P.dir t c) = P.lineMats d M c :=
  congrArg (fun Q : POVM (LinePoly F (m * d)) (d' × Anc F m) => fun f => ((Q.mats f).val))
    (hatLinePOVM_congr hm M W P.ty P.base P.dir (P.question_shift c t) (P.base_shift c t)
      (P.dir_shift _ _))
end
end MIPRE.QLD.LinePres

namespace MIPRE.QLD.LinePres
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {hm : m ∣ Fintype.card F} {W : Bas}
theorem param_shiftPt_other (P : LinePres F m hm W) (c : Content F m) (w : Point F m) :
    P.param (Content.shiftPt W.other w c) = P.param c := by
  rw [param, param, P.base_shift_other, P.dir_shift_other, Content.shiftPt_other_pt]
end
end MIPRE.QLD.LinePres

namespace MIPRE.QLD.LinePres
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {hm : m ∣ Fintype.card F} {W : Bas}
theorem lineEvalMats_shiftPt_other {d' : Type} [Fintype d'] [DecidableEq d'] (P : LinePres F m hm W)
    (d : ℕ) (M : Question F m → POVM (Answer F m d) d') (c : Content F m) (w : Point F m) :
    P.lineEvalMats d M (Content.shiftPt W.other w c) = P.lineEvalMats d M c := by
  have hQ : hatLinePOVM (m * d) hm M W P.ty P.base P.dir (Content.shiftPt W.other w c)
      = hatLinePOVM (m * d) hm M W P.ty P.base P.dir c :=
    hatLinePOVM_congr hm M W P.ty P.base P.dir (P.question_shift_other c w)
      (P.base_shift_other c w) (P.dir_shift_other c w)
  have hp : P.param (Content.shiftPt W.other w c) = P.param c := P.param_shiftPt_other c w
  show (fun a => ((((hatLinePOVM (m * d) hm M W P.ty P.base P.dir
      (Content.shiftPt W.other w c)).map
        fun f => LinePoly.eval f (P.param (Content.shiftPt W.other w c))).mats a).val)) = _
  rw [hQ, hp]
  rfl
end
end MIPRE.QLD.LinePres

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {hm : m ∣ Fintype.card F} {W : Bas}
theorem collProb_nonneg (P : LinePres F m hm W) (d : ℕ) (c : Content F m) :
    0 ≤ collProb P d c := by
  rw [collProb]
  split
  · positivity
  · exact zero_le_one
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
theorem fibSum_aOp {ι κ N N' : Type*} [Fintype ι] [DecidableEq κ] [Fintype N] [DecidableEq N]
    [Fintype N'] [DecidableEq N'] (M : ι → Matrix N N ℂ) (e : ι → κ) (k : κ) :
    fibSum (fun i => (aOp (M i) : Matrix (N × N') (N × N') ℂ)) e k
      = aOp (fibSum M e k) := by
  rw [fibSum, fibSum, aOp_sum]
end
end MIPRE.QLD

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ} {ε : ℝ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
set_option maxHeartbeats 1600000 in
theorem _root_.solution {ι : Type*} [Fintype ι] [Nonempty ι]
    (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (kX kZ : ι → Content F m)
    {sh : Point F m → ι → ι} (hzero : ∀ a, sh 0 a = a)
    (hadd : ∀ (w w' : Point F m) (a : ι), sh w' (sh w a) = sh (w + w') a)
    (hkX : ∀ (w : Point F m) (a : ι), kX (sh w a) = Content.shiftPt .X w (kX a))
    (hkZ : ∀ (w : Point F m) (a : ι), kZ (sh w a) = Content.shiftPt .X w (kZ a))
    {QA : ι → F × F → Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ}
    (hQA : ∀ a, IsPVM (QA a)) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) {δ η εc : ℝ}
    (hmargX : ∑ a : ι, (Fintype.card ι : ℝ)⁻¹ * ∑ x : F,
        xSqNorm (extHat (m := m) ψ) (∑ q : F, QA a (x, q))
          (aOp (PX.lineEvalMats d MB (kX a) x)) ≤ δ)
    (hmargZ : ∑ a : ι, (Fintype.card ι : ℝ)⁻¹ * ∑ b : F,
        xSqNorm (extHat (m := m) ψ) (∑ q : F, QA a (q, b))
          (aOp (PZ.lineEvalMats d MB (kZ a) b)) ≤ δ)
    (hselfX : ∑ a : ι, (Fintype.card ι : ℝ)⁻¹ *
        ∑ f : LinePoly F (m * d), xSqNorm (extHat (m := m) ψ) (aOp (PX.lineMats d MA (kX a) f))
          (aOp (PX.lineMats d MB (kX a) f)) ≤ η)
    (hcoll : ∑ a : ι, (Fintype.card ι : ℝ)⁻¹ * collProb PX d (kX a) ≤ εc) :
    1 - ∑ a : ι, (Fintype.card ι : ℝ)⁻¹ * ∑ p : F × F,
        bornProb (extHat (m := m) ψ) (QA a p)
          (∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
              LinePoly.eval q.1 (PX.param (kX a)) = p.1
                ∧ LinePoly.eval q.2 (PZ.param (kZ a)) = p.2,
            pasteLine PX PZ d MB (kX a) (kZ a) q)
      ≤ δ / 2 + Real.sqrt (δ / 2) + Real.sqrt (32 * δ + 4 * Real.sqrt η + 2 * εc) := by
  classical
  have hunit : ‖evec (extHat (m := m) ψ)‖ = 1 :=
    norm_evec_eq_one_of_unit
      (extVec2_unit (hatVec_unit hψ) ((0 : F), (0 : F)) ((0 : F), (0 : F)))
  have hι1 : ∑ _a : ι, (Fintype.card ι : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  have hw0 : ∀ _i : ι × F, (0 : ℝ) ≤ (Fintype.card ι : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹ :=
    fun _ => by positivity
  have hw1 : ∑ _i : ι × F, (Fintype.card ι : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹ = 1 :=
    sum_prod_uniform_one (Y := F) hι1
  -- the shift, as the two contents see it
  have hdirI : ∀ (a : ι) (w : Point F m), PX.dir (kX (sh w a)) = PX.dir (kX a) := fun a w => by
    rw [hkX, PX.dir_shift]
  have hshX : ∀ (a : ι) (t : F),
      kX (sh (t • PX.dir (kX a)) a) = Content.shiftAlong .X PX.dir t (kX a) := fun a t => by
    rw [hkX, Content.shiftAlong_eq]
  -- the four families, and their projectivity
  have hA : ∀ i : ι × F, IsPVM fun r : F × F =>
      QA (sh (i.2 • PX.dir (kX i.1)) i.1) (r.2, r.1) := fun i =>
    (hQA _).comp_equiv (Equiv.prodComm F F)
  have hR : ∀ i : ι × F, IsPVM fun b : F =>
      (aOp (PZ.lineEvalMats d MB (kZ i.1) b)
        : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ) := fun i =>
    IsPVM.aOp (PZ.isPVM_lineEvalMats d hprojB (kZ i.1))
  have hG : ∀ i : ι × F, IsPVM fun f : LinePoly F (m * d) =>
      (aOp (PX.lineMats d MB (kX i.1) f)
        : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ) := fun i =>
    IsPVM.aOp (PX.isPVM_lineMats d hprojB (kX i.1))
  have hGa : ∀ i : ι × F, IsPVM fun f : LinePoly F (m * d) =>
      (aOp (PX.lineMats d MA (kX i.1) f)
        : Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ) := fun i =>
    IsPVM.aOp (PX.isPVM_lineMats d hprojA (kX i.1))
  -- the `Z`-side marginal hypothesis
  have hP1 : ∑ i : ι × F,
        ((Fintype.card ι : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) * ∑ b : F,
          xSqNorm (extHat (m := m) ψ)
            (∑ x : F, QA (sh (i.2 • PX.dir (kX i.1)) i.1) (x, b))
            (aOp (PZ.lineEvalMats d MB (kZ i.1) b)) ≤ δ := by
    refine le_trans (le_of_eq ?_) hmargZ
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_)
      (sum_shift_gen (dir := fun a => PX.dir (kX a)) hzero hadd hdirI fun a => ∑ b : F,
        xSqNorm (extHat (m := m) ψ) (∑ x : F, QA a (x, b))
          (aOp (PZ.lineEvalMats d MB (kZ a) b)))
    refine congrArg (fun t : ℝ => ((Fintype.card ι : ℝ)⁻¹
      * (Fintype.card F : ℝ)⁻¹) * t) (Finset.sum_congr rfl fun b _ => ?_)
    rw [hkZ,
      show PZ.lineEvalMats d MB (Content.shiftPt .X (i.2 • PX.dir (kX i.1)) (kZ i.1))
          = PZ.lineEvalMats d MB (kZ i.1) from
        PZ.lineEvalMats_shiftPt_other d MB (kZ i.1) (i.2 • PX.dir (kX i.1))]
  -- the `X`-side marginal hypothesis
  have hP2 : ∑ i : ι × F,
        ((Fintype.card ι : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) * ∑ x : F,
          xSqNorm (extHat (m := m) ψ)
            (∑ b : F, QA (sh (i.2 • PX.dir (kX i.1)) i.1) (x, b))
            (fibSum (fun f : LinePoly F (m * d) =>
              (aOp (PX.lineMats d MB (kX i.1) f)
                : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ))
              (fun f => LinePoly.eval f
                (PX.param (kX (sh (i.2 • PX.dir (kX i.1)) i.1)))) x) ≤ δ := by
    refine le_trans (le_of_eq ?_) hmargX
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_)
      (sum_shift_gen (dir := fun a => PX.dir (kX a)) hzero hadd hdirI fun a => ∑ x : F,
        xSqNorm (extHat (m := m) ψ) (∑ q : F, QA a (x, q))
          (aOp (PX.lineEvalMats d MB (kX a) x)))
    refine congrArg (fun t : ℝ => ((Fintype.card ι : ℝ)⁻¹
      * (Fintype.card F : ℝ)⁻¹) * t) (Finset.sum_congr rfl fun x _ => ?_)
    rw [fibSum_aOp, hshX i.1 i.2, ← PX.lineMats_shiftAlong d MB (kX i.1) i.2,
      ← PX.lineEvalMats_eq_fibSum d MB (Content.shiftAlong .X PX.dir i.2 (kX i.1)) x]
  -- the fine self-consistency
  have hP4 : ∑ i : ι × F,
        ((Fintype.card ι : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
          ∑ f : LinePoly F (m * d), xSqNorm (extHat (m := m) ψ)
            (aOp (PX.lineMats d MA (kX i.1) f)) (aOp (PX.lineMats d MB (kX i.1) f)) ≤ η := by
    refine le_trans (le_of_eq ?_) hselfX
    exact sum_prod_uniform (Y := F) (fun _ => (Fintype.card ι : ℝ)⁻¹)
      fun a => ∑ f : LinePoly F (m * d), xSqNorm (extHat (m := m) ψ)
        (aOp (PX.lineMats d MA (kX a) f)) (aOp (PX.lineMats d MB (kX a) f))
  have hR' : ∀ a : ι, IsPVM fun b : F =>
      (aOp (PZ.lineEvalMats d MB (kZ a) b)
        : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ) := fun a =>
    IsPVM.aOp (PZ.isPVM_lineEvalMats d hprojB (kZ a))
  have hG' : ∀ a : ι, IsPVM fun f : LinePoly F (m * d) =>
      (aOp (PX.lineMats d MB (kX a) f)
        : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ) := fun a =>
    IsPVM.aOp (PX.isPVM_lineMats d hprojB (kX a))
  have hGa' : ∀ a : ι, IsPVM fun f : LinePoly F (m * d) =>
      (aOp (PX.lineMats d MA (kX a) f)
        : Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ) := fun a =>
    IsPVM.aOp (PX.isPVM_lineMats d hprojA (kX a))
  have hCT : ∑ i : ι × F,
        ((Fintype.card ι : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
          collisionTerm (extHat (m := m) ψ)
            (fun b : F => (aOp (PZ.lineEvalMats d MB (kZ i.1) b)
              : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ))
            (fun f : LinePoly F (m * d) => (aOp (PX.lineMats d MB (kX i.1) f)
              : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ))
            (fun f : LinePoly F (m * d) => (aOp (PX.lineMats d MA (kX i.1) f)
              : Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ))
            (fun f => LinePoly.eval f
              (PX.param (kX (sh (i.2 • PX.dir (kX i.1)) i.1)))) ≤ εc := by
    refine le_trans (sum_collisionTerm_le (Y := F) (Z := ι)
      (ν := fun _ : ι => (Fintype.card ι : ℝ)⁻¹)
      (R := fun a : ι => fun b : F => (aOp (PZ.lineEvalMats d MB (kZ a) b)
        : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ))
      (G := fun a : ι => fun f : LinePoly F (m * d) => (aOp (PX.lineMats d MB (kX a) f)
        : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ))
      (Ga := fun a : ι => fun f : LinePoly F (m * d) => (aOp (PX.lineMats d MA (kX a) f)
        : Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ))
      (εz := fun a : ι => collProb PX d (kX a)) hunit (fun _ => by positivity) hR' hG' hGa'
      (fun (a : ι) (t : F) (f : LinePoly F (m * d)) =>
        LinePoly.eval f (PX.param (kX (sh (t • PX.dir (kX a)) a))))
      (fun a => collProb_nonneg PX d (kX a))
      (fun a f f' hne => by
        simp only [hshX]
        exact card_collide_le PX d (kX a) hne)) hcoll
  -- the pasting lemma
  have key := one_sub_sum_bornProb_pasteJ_le (ψ := extHat (m := m) ψ) hunit hw0 hw1
    (A := fun i : ι × F => fun r : F × F =>
      QA (sh (i.2 • PX.dir (kX i.1)) i.1) (r.2, r.1))
    (R := fun i : ι × F => fun b : F =>
      (aOp (PZ.lineEvalMats d MB (kZ i.1) b)
        : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ))
    (G := fun i : ι × F => fun f : LinePoly F (m * d) =>
      (aOp (PX.lineMats d MB (kX i.1) f)
        : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ))
    (Ga := fun i : ι × F => fun f : LinePoly F (m * d) =>
      (aOp (PX.lineMats d MA (kX i.1) f)
        : Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ))
    (fun i => fun f => LinePoly.eval f (PX.param (kX (sh (i.2 • PX.dir (kX i.1)) i.1))))
    hA hR hG hGa hP1 hP2 hP4 hCT
  -- and the conclusion, read back at the question distribution
  refine le_trans (le_of_eq (congrArg (fun t : ℝ => 1 - t) ?_)) key
  refine Eq.trans (sum_shift_gen (dir := fun a => PX.dir (kX a))
      hzero hadd hdirI (fun a => ∑ p : F × F,
      bornProb (extHat (m := m) ψ) (QA a p)
        (∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
            LinePoly.eval q.1 (PX.param (kX a)) = p.1
              ∧ LinePoly.eval q.2 (PZ.param (kZ a)) = p.2,
          pasteLine PX PZ d MB (kX a) (kZ a) q))).symm
    (Finset.sum_congr rfl fun i _ => congrArg (fun t : ℝ => ((Fintype.card ι : ℝ)⁻¹
      * (Fintype.card F : ℝ)⁻¹) * t) ?_)
  refine (Fintype.sum_equiv (Equiv.prodComm F F) _ _ fun p => ?_).symm
  rw [show (fun b : F => (aOp (PZ.lineEvalMats d MB (kZ i.1) b)
        : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ))
      = (fun b : F => (aOp (PZ.lineEvalMats d MB
          (kZ (sh (i.2 • PX.dir (kX i.1)) i.1)) b)
        : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ)) from by
    funext b
    rw [hkZ,
      show PZ.lineEvalMats d MB (Content.shiftPt .X (i.2 • PX.dir (kX i.1)) (kZ i.1))
          = PZ.lineEvalMats d MB (kZ i.1) from
        PZ.lineEvalMats_shiftPt_other d MB (kZ i.1) (i.2 • PX.dir (kX i.1))],
    show (fun f : LinePoly F (m * d) => (aOp (PX.lineMats d MB (kX i.1) f)
        : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ))
      = (fun f : LinePoly F (m * d) => (aOp (PX.lineMats d MB
          (kX (sh (i.2 • PX.dir (kX i.1)) i.1)) f)
        : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ)) from by
    funext f
    rw [hshX i.1 i.2, PX.lineMats_shiftAlong d MB (kX i.1) i.2],
    pasteJ_eq_pasteLine]
  rfl
end MIPRE.QLD
