-- Prove2me | solution 1 for MIPRE.QLD.MirrorSimul.sum_snorm_sq_aliceConjPauli_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:28:06.961171+00:00
-- url     : https://prove2.me/submissions/d5d36b3d-3bfb-4380-86e7-e77a20f2289a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/SwapItemTwo.lean (solution of MIPRE.QLD.MirrorSimul.sum_snorm_sq_aliceConjPauli_le);
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
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
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
import Definitions.Def_MIPRE_Background_QLD_PauliBasis
import Definitions.Def_MIPRE_Background_QLD_Multilinear
import Definitions.Def_MIPRE_Background_QLD_ExactPauli
import Definitions.Def_MIPRE_Background_QLD_SwapUnitary
import Definitions.Def_MIPRE_Background_QLD_MTilde
import Definitions.Def_MIPRE_Background_QLD_Pulling
import Definitions.Def_MIPRE_Background_QLD_SwapMeasure
import Definitions.Def_MIPRE_Background_QLD_ChainProbe
import Definitions.Def_MIPRE_Background_QLD_TwoPairs
import Definitions.Def_MIPRE_Background_QLD_Mirror
import Definitions.Def_MIPRE_Background_QLD_SwapState
import Definitions.Def_MIPRE_Background_QLD_Chain
import Definitions.Def_MIPRE_Background_QLD_ChainAssembly
import Definitions.Def_MIPRE_Background_QLD_SelfCons
import Definitions.Def_MIPRE_Background_QLD_SwapItemOne
import Definitions.Def_MIPRE_Background_QLD_SwapItemTwo
import Theorems.Thm_MIPRE_IsPVM_aOp
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_LowDegree_degreeOf_ind_le
import Theorems.Thm_MIPRE_POVM_map_map
import Theorems.Thm_MIPRE_QLD_MirrorSimul_sum_bornProb_fibre_ge
import Theorems.Thm_MIPRE_QLD_sTensor_conjTranspose
import Theorems.Thm_MIPRE_QLD_sTensor_mul
import Theorems.Thm_MIPRE_QLD_sTensor_one
import Theorems.Thm_MIPRE_QLD_sum_snorm_sq_sub_eq_two_sub
import Theorems.Thm_MIPRE_QLD_sum_uniform_bornProb_fibre_le
import Theorems.Thm_MIPRE_QLD_toMv_coeffTable
import Theorems.Thm_MIPRE_QLD_uOf_conj_wX
import Theorems.Thm_MIPRE_Weyl_proj_mul_proj
import Theorems.Thm_MIPRE_Weyl_sum_proj
import Theorems.Thm_MIPRE_Weyl_wX_mul_wZ
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_sgn_add
import Theorems.Thm_MIPRE_star_sgn

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree
noncomputable section
open Finset MvPolynomial
variable {F : Type*} [CommRing F] {m : ℕ}
theorem degreeOf_ldEnc_le [Nontrivial F] (a : (Fin m → Bool) → F) (i : Fin m) :
    (ldEnc a).degreeOf i ≤ 1 := by
  rw [ldEnc]
  refine (MvPolynomial.degreeOf_sum_le i univ (fun y => C (a y) * ind y)).trans ?_
  refine Finset.sup_le fun y _ => ?_
  exact (MvPolynomial.degreeOf_mul_le i _ _).trans (by simpa using degreeOf_ind_le (F := F) y i)
end
end MIPRE.LowDegree

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_mul (X Y : Matrix HB HB ℂ) :
    bOp (X * Y) = (bOp X : Matrix (HA × HB) _ ℂ) * bOp Y := by
  rw [bOp, bOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
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
theorem bOp_conjTranspose (X : Matrix HB HB ℂ) :
    (bOp X : Matrix (HA × HB) _ ℂ)ᴴ = bOp (Xᴴ) := by
  rw [bOp, bOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
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

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*} [Fintype n]
theorem trDot_comm (a b : n → F) : trDot a b = trDot b a := by
  rw [trDot, trDot, Finset.sum_congr rfl fun l _ => mul_comm (a l) (b l)]
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*} [Fintype n]
theorem trDot_add_right (a b b' : n → F) : trDot a (b + b') = trDot a b + trDot a b' := by
  rw [trDot_comm, trDot_add_left, trDot_comm b a, trDot_comm b' a]
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- The defining Fourier average, as a rewrite. -/
theorem proj_def (w : (n → F) → Matrix (n → F) (n → F) ℂ) (e : n → F) :
    proj w e = (Fintype.card (n → F) : ℂ)⁻¹ • ∑ a : n → F, sgn (trDot a e) • w a := rfl
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
/-- The projectors are self-adjoint. -/
theorem proj_conjTranspose (hw : IsWeylFamily w) (e : n → F) : (proj w e)ᴴ = proj w e := by
  classical
  rw [proj_def w e, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
    Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
      rw [Matrix.conjTranspose_smul, hw.selfAdjoint a, star_sgn]]
  congr 1
  simp
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
theorem dotF_comm (a b : n → F) : dotF a b = dotF b a :=
  Finset.sum_congr rfl fun l _ => mul_comm (a l) (b l)
end
end MIPRE.Weyl

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
theorem inner_evec (u w : N → ℂ) : (inner ℂ (evec u) (evec w) : ℂ) = star u ⬝ᵥ w := by
  rw [evec, evec, EuclideanSpace.inner_toLp_toLp, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
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
variable {R1 R2 : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
theorem IsPVM.bOp {ι : Type*} [Fintype ι] {Q : ι → Matrix dB dB ℂ} (h : IsPVM Q) :
    IsPVM fun i => (bOp (Q i) : Matrix (dA × dB) (dA × dB) ℂ) where
  isSelfAdjoint i := by rw [bOp_conjTranspose, h.isSelfAdjoint]
  idem i := by rw [← bOp_mul, h.idem]
  sum_eq_one := by rw [← bOp_sum, h.sum_eq_one, bOp_one]
end
end MIPRE

namespace MIPRE.LIDT
noncomputable section
open Finset MvPolynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ}
omit [Fintype F] [DecidableEq F] in
theorem LowIndDegPoly.eval_toMv (g : LowIndDegPoly (F := F) (m := n) (d := d)) (u : Point F n) :
    MvPolynomial.eval u g.toMv = g.eval u := by
  simp only [LowIndDegPoly.toMv, map_sum, MvPolynomial.eval_monomial, LowIndDegPoly.eval]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finsupp.prod_fintype _ _ fun i => pow_zero _]
  rfl
end
end MIPRE.LIDT

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **The pairing with `ind_m(u)` is the encoding evaluated at `u`**, which is what identifies the
ancilla's point measurement as a coarse-graining of its basis measurement along `g_h(u)`. -/
theorem dotF_indVec (h : Anc F m) (u : Point F m) :
    dotF h (indVec u) = MvPolynomial.eval u (ldEnc h) := by
  rw [ldEnc, map_sum, dotF]
  exact Finset.sum_congr rfl fun y _ => by rw [map_mul, MvPolynomial.eval_C]; rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {hm : m ∣ Fintype.card F}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
/-- The low-degree reading at a point is the pairing of the cube data with the point's indicator
vector. -/
theorem rdPauli_eq_dotF (u : Point F m) (a : Answer F m d) :
    rdPauli u a = dotF (rdPauliVec a) (indVec u) := by
  cases a with
  | pauliAns h => rw [rdPauli, rdPauliVec, dotF_indVec]
  | val _ => simp [rdPauli, rdPauliVec, dotF]
  | apoly _ => simp [rdPauli, rdPauliVec, dotF]
  | dpoly _ => simp [rdPauli, rdPauliVec, dotF]
  | bit _ => simp [rdPauli, rdPauliVec, dotF]
  | bitPair _ => simp [rdPauli, rdPauliVec, dotF]
  | bitTriple _ => simp [rdPauli, rdPauliVec, dotF]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
/-- `(sum_x A x) (x) B = sum_x (A x (x) B)`. -/
theorem sum_kron {iota : Type*} (s : Finset iota) (A : iota → Matrix dA dA ℂ)
    (B : Matrix (n → F) (n → F) ℂ) :
    (∑ x ∈ s, A x) ⊗ₖ B = ∑ x ∈ s, A x ⊗ₖ B := by
  ext p q
  obtain ⟨a, k⟩ := p
  obtain ⟨b, l⟩ := q
  rw [Matrix.kronecker_apply, Matrix.sum_apply, Matrix.sum_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => (Matrix.kronecker_apply _ _ _ _ _ _).symm
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
theorem uOf_conjTranspose (cd : G → (n → F)) (p : G × G) :
    (uOf cd p)ᴴ = wZ (cd p.1) * wX (cd p.2) := by
  rw [uOf, Matrix.conjTranspose_mul, wX_conjTranspose, wZ_conjTranspose]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
theorem uOf_mul_conjTranspose (cd : G → (n → F)) (p : G × G) :
    uOf cd p * (uOf cd p)ᴴ = 1 := by
  rw [uOf_conjTranspose, uOf]
  calc wX (cd p.2) * wZ (cd p.1) * (wZ (cd p.1) * wX (cd p.2))
      = wX (cd p.2) * (wZ (cd p.1) * wZ (cd p.1)) * wX (cd p.2) := by noncomm_ring
    _ = 1 := by
        rw [wZ_mul_wZ, add_self_vec, wZ_zero, Matrix.mul_one, wX_mul_wX, add_self_vec, wX_zero]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
theorem uOf_conjTranspose_mul (cd : G → (n → F)) (p : G × G) :
    (uOf cd p)ᴴ * uOf cd p = 1 := by
  rw [uOf_conjTranspose, uOf]
  calc wZ (cd p.1) * wX (cd p.2) * (wX (cd p.2) * wZ (cd p.1))
      = wZ (cd p.1) * (wX (cd p.2) * wX (cd p.2)) * wZ (cd p.1) := by noncomm_ring
    _ = 1 := by
        rw [wX_mul_wX, add_self_vec, wX_zero, Matrix.mul_one, wZ_mul_wZ, add_self_vec, wZ_zero]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {S : G × G → Matrix dA dA ℂ} {cd : G → (n → F)}
/-- **The swap map is unitary.** -/
theorem swapU_mul_conjTranspose (hS : IsPVM S) : swapU S cd * (swapU S cd)ᴴ = 1 := by
  rw [swapU, sTensor_conjTranspose hS, sTensor_mul hS,
    show (fun p => uOf cd p * (uOf cd p)ᴴ) = fun _ => (1 : Matrix (n → F) (n → F) ℂ) from
      funext fun p => uOf_mul_conjTranspose cd p,
    sTensor_one hS]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {S : G × G → Matrix dA dA ℂ} {cd : G → (n → F)}
theorem swapU_conjTranspose_mul (hS : IsPVM S) : (swapU S cd)ᴴ * swapU S cd = 1 := by
  rw [swapU, sTensor_conjTranspose hS, sTensor_mul hS,
    show (fun p => (uOf cd p)ᴴ * uOf cd p) = fun _ => (1 : Matrix (n → F) (n → F) ℂ) from
      funext fun p => uOf_conjTranspose_mul cd p,
    sTensor_one hS]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {S : G × G → Matrix dA dA ℂ} {cd : G → (n → F)}
/-- `(tau^X(x) tau^Z(z)) tau^Z(b) (tau^X(x) tau^Z(z))^dagger = (-1)^{tr(x . b)} tau^Z(b)`. -/
theorem uOf_conj_wZ (cd : G → (n → F)) (p : G × G) (b : n → F) :
    uOf cd p * wZ b * (uOf cd p)ᴴ = sgn (trDot (cd p.2) b) • wZ b := by
  rw [uOf_conjTranspose, uOf]
  calc wX (cd p.2) * wZ (cd p.1) * wZ b * (wZ (cd p.1) * wX (cd p.2))
      = wX (cd p.2) * (wZ (cd p.1) * wZ b * wZ (cd p.1)) * wX (cd p.2) := by noncomm_ring
    _ = wX (cd p.2) * wZ b * wX (cd p.2) := by
        rw [wZ_mul_wZ, wZ_mul_wZ, show cd p.1 + b + cd p.1 = b from by
          rw [add_comm (cd p.1) b, add_assoc, add_self_vec, add_zero]]
    _ = sgn (trDot (cd p.2) b) • wZ b := by
        rw [wX_mul_wZ, Matrix.smul_mul, show wZ b * wX (cd p.2) * wX (cd p.2) = wZ b from by
          rw [mul_assoc, wX_mul_wX, add_self_vec, wX_zero, Matrix.mul_one]]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : Type*} [Fintype n] [DecidableEq n] {G : Type*} [Fintype G] [DecidableEq G]
  {dA : Type*} [Fintype dA] [DecidableEq dA]
omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [DecidableEq n] in
/-- The pairing is additive in its right argument too. -/
theorem dotF_add_right (a u v : n → F) : dotF a (u + v) = dotF a u + dotF a v := by
  rw [dotF, dotF, dotF, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by
    show a l * (u l + v l) = a l * u l + a l * v l
    ring
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
omit [Fintype F] [DecidableEq F] in
/-- In characteristic two a sum is its own difference. -/
theorem add_self_eq_zero' (a : F) : a + a = 0 := by
  rw [← two_mul, MIPRE.Weyl.two_eq_zero, zero_mul]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ} {U : Matrix (n → F) (n → F) ℂ} {s : n → F}
/-- **Conjugation that twists a Weyl family by a character shifts its spectral projectors.** The
projector at the pattern `e` is the Fourier average against the character of `e`; conjugating
multiplies the term at `a` by the character of `s`, and the two characters compose by adding their
labels. -/
theorem conj_proj_of_sign (h : ∀ a, U * w a * Uᴴ = sgn (trDot a s) • w a) (e : n → F) :
    U * proj w e * Uᴴ = proj w (e + s) := by
  rw [proj_def, proj_def, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, h a, smul_smul, ← sgn_add, ← trDot_add_right]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ} {U : Matrix (n → F) (n → F) ℂ} {s : n → F}
/-- **...and shifts a syndrome projector's outcome by the shift's own pairing with the probe.**
The level set of the pairing at `a` is carried onto the level set at `a + s . v` by adding `s`,
which is an involution of the index group in characteristic two. -/
theorem conj_syn_of_sign (h : ∀ a, U * w a * Uᴴ = sgn (trDot a s) • w a) (v : n → F) (a : F) :
    U * syn w v a * Uᴴ = syn w v (a + dotF s v) := by
  classical
  have hadd : ∀ e : n → F, dotF (e + s) v = dotF e v + dotF s v := fun e => by
    rw [dotF_comm, dotF_add_right, dotF_comm v e, dotF_comm v s]
  rw [syn, syn, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_congr rfl fun e (_ : e ∈ univ.filter fun e => dotF e v = a) =>
      conj_proj_of_sign h e]
  refine Finset.sum_equiv (Equiv.addRight s) (fun e => ?_) (fun e _ => rfl)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_addRight, hadd]
  exact ⟨fun he => by rw [he], fun he => add_right_cancel he⟩
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {S : G × G → Matrix dA dA ℂ} {cd : G → (n → F)}
/-- **Conjugation by the swap unitary strips the pair measurement off the exact Pauli
measurement.** For a family each of whose operators the ancilla factor twists by the character of
`cd (pi p)` --- the very shift the outcome of `M~^{W,u}_a` is written with --- the two cancel and
only the bare syndrome projector survives:
`V M~^{W,u}_a V^dagger = Id (x) tau^W_{[g_h(u) = a]}`. -/
theorem swapU_conj_mTilde (hS : IsPVM S) {pi : G × G → G}
    {w : (n → F) → Matrix (n → F) (n → F) ℂ}
    (h : ∀ (p : G × G) (b : n → F),
      uOf cd p * w b * (uOf cd p)ᴴ = sgn (trDot b (cd (pi p))) • w b)
    (u : n → F) (a : F) :
    swapU S cd * mTilde S pi cd w u a * (swapU S cd)ᴴ = 1 ⊗ₖ syn w u a := by
  rw [mTilde_eq_sTensor, swapU, sTensor_mul hS, sTensor_conjTranspose hS, sTensor_mul hS]
  rw [show (fun p => uOf cd p * syn w u (dotF (cd (pi p)) u + a) * (uOf cd p)ᴴ)
      = fun _ => syn w u a from funext fun p => by
    rw [conj_syn_of_sign (h p) u (dotF (cd (pi p)) u + a)]
    congr 1
    rw [add_comm (dotF (cd (pi p)) u) a, add_assoc, add_self_eq_zero', add_zero]]
  show (∑ p, S p ⊗ₖ syn w u a) = 1 ⊗ₖ syn w u a
  rw [← sum_kron, hS.sum_eq_one]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {S : G × G → Matrix dA dA ℂ} {cd : G → (n → F)}
/-- **The `X`-side identity.** -/
theorem swapU_conj_mTilde_X (hS : IsPVM S) (u : n → F) (a : F) :
    swapU S cd * mTilde S Prod.fst cd wX u a * (swapU S cd)ᴴ = 1 ⊗ₖ syn wX u a :=
  swapU_conj_mTilde hS (fun p b => uOf_conj_wX cd p b) u a
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {S : G × G → Matrix dA dA ℂ} {cd : G → (n → F)}
/-- **The `Z`-side identity.** -/
theorem swapU_conj_mTilde_Z (hS : IsPVM S) (u : n → F) (a : F) :
    swapU S cd * mTilde S Prod.snd cd wZ u a * (swapU S cd)ᴴ = 1 ⊗ₖ syn wZ u a :=
  swapU_conj_mTilde hS (fun p b => by rw [uOf_conj_wZ, trDot_comm]) u a
end
end MIPRE.QLD

namespace MIPRE.QLD.SimulPair
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
open MIPRE.LIDT MIPRE.LowDegree
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
theorem swapA_mul_conjTranspose : P.swapA * P.swapAᴴ = 1 :=
  swapU_mul_conjTranspose P.SA_proj
end
end MIPRE.QLD.SimulPair

namespace MIPRE.QLD.SimulPair
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
open MIPRE.LIDT MIPRE.LowDegree
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
theorem swapA_conjTranspose_mul : P.swapAᴴ * P.swapA = 1 :=
  swapU_conjTranspose_mul P.SA_proj
end
end MIPRE.QLD.SimulPair

namespace MIPRE.QLD.SimulPair
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (P : SimulPair ψ MA MB δ)
/-- **Display `eq:qld-unitary-6` at an arbitrary probe.** Conjugation by the swap unitary strips
the pair measurement off the exact Pauli measurement whatever the probe, since the cancellation is
between the outcome's shift and the conjugation's, and both are written with the same pairing. -/
theorem swapU_conj_mTildeAnc (W : Bas) (v : Anc F m) (a : F) :
    P.swapA * P.mTildeAnc W v a * P.swapAᴴ = 1 ⊗ₖ syn (weylOf W) v a := by
  rw [SimulPair.swapA, SimulPair.mTildeAnc]
  cases W with
  | X => exact swapU_conj_mTilde_X P.SA_proj v a
  | Z => exact swapU_conj_mTilde_Z P.SA_proj v a
end
end MIPRE.QLD.SimulPair

attribute [instance] MIPRE.QLD.MirrorSimul.instFintypeEa MIPRE.QLD.MirrorSimul.instDecEqEa MIPRE.QLD.MirrorSimul.instFintypeEb MIPRE.QLD.MirrorSimul.instDecEqEb

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
universe u
set_option synthInstance.maxSize 1000
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
attribute [instance] MIPRE.QLD.MirrorSimul.instFintypeEa MIPRE.QLD.MirrorSimul.instDecEqEa MIPRE.QLD.MirrorSimul.instFintypeEb MIPRE.QLD.MirrorSimul.instDecEqEb
/-- **Display `eq:qld-unitary-6` for Bob**: his swap unitary strips the pair measurement off his
exact Pauli measurement, leaving the Weyl syndrome on `B''` alone. The paper says "an entirely
analogous calculation shows"; here it is the same calculation, at the other instance. -/
theorem bobSwap_conj_bobMTilde (W : Bas) (v : Anc F m) (a : F) :
    M.bobSwap * M.bobMTilde W v a * M.bobSwapᴴ = 1 ⊗ₖ syn (weylOf W) v a :=
  M.toSecond.swapU_conj_mTildeAnc W v a
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
/-- **A Weyl family's spectral projectors are a projective measurement.** The three facts are in
Foundations one by one; this is them bundled, which is the form `isPVM_kron` consumes. -/
theorem isPVM_proj {n : Type*} [Fintype n] [DecidableEq n]
    {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w) : IsPVM (proj w) where
  isSelfAdjoint e := proj_conjTranspose hw e
  idem e := by simpa using proj_mul_proj hw e e
  sum_eq_one := sum_proj hw
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [Fintype R] [DecidableEq R]
variable {N Λ : Type*} [Fintype N] [DecidableEq N] [Fintype Λ] [DecidableEq Λ]
/-- **Display `eq:qld-unitary-7`, read as a bound.** Once the agreement is at least `1 - c`, the
summed deviation is at most `2c`. -/
theorem sum_snorm_sq_sub_le_of_agree {v : N → ℂ} (hv : ‖evec v‖ = 1) {A T : Λ → Matrix N N ℂ}
    (hA : IsPVM A) (hT : IsPVM T) {c : ℝ} (hagree : 1 - c ≤ ∑ h, qform v (A h * T h)) :
    ∑ h, snorm v (A h - T h) ^ 2 ≤ 2 * c := by
  rw [sum_snorm_sq_sub_eq_two_sub hv hA hT]
  linarith
end
end MIPRE.QLD

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
theorem aliceSwap_conjTranspose_mul : M.aliceSwapᴴ * M.aliceSwap = 1 :=
  M.toFirst.swapA_conjTranspose_mul
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem ancPoly_toMv (hd : 1 ≤ d) (h : Anc F m) : (ancPoly (d := d) h).toMv = ldEnc h :=
  toMv_coeffTable _ fun i => (degreeOf_ldEnc_le h i).trans hd
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
/-- **Its value at a point is the pairing with the point's indicator vector**: the paper's
`g_h(u) = h . ind_m(u)`. -/
theorem ancPoly_eval (hd : 1 ≤ d) (h : Anc F m) (u : Point F m) :
    (ancPoly (d := d) h).eval u = dotF h (indVec u) := by
  rw [← LowIndDegPoly.eval_toMv, ancPoly_toMv hd, dotF_indVec]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- **Distinct cube data have distinct encodings**: the encoding reads the data back on the
cube. -/
theorem ancPoly_toMv_ne (hd : 1 ≤ d) {h h' : Anc F m} (hne : h ≠ h') :
    (ancPoly (d := d) h).toMv ≠ (ancPoly (d := d) h').toMv := by
  rw [ancPoly_toMv hd, ancPoly_toMv hd]
  intro heq
  exact hne (funext fun y => by rw [← eval_ldEnc h y, ← eval_ldEnc h' y, heq])
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- **Conjugating a projective measurement by a unitary gives a projective measurement.** -/
theorem isPVM_conj_unitary {N Λ : Type*} [Fintype N] [DecidableEq N] [Fintype Λ]
    {P : Λ → Matrix N N ℂ} (hP : IsPVM P) {V : Matrix N N ℂ} (h1 : Vᴴ * V = 1)
    (h2 : V * Vᴴ = 1) : IsPVM fun a => V * P a * Vᴴ where
  isSelfAdjoint a := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hP.isSelfAdjoint, Matrix.mul_assoc]
  idem a := by
    rw [show V * P a * Vᴴ * (V * P a * Vᴴ) = V * P a * (Vᴴ * V) * P a * Vᴴ from by
      simp only [Matrix.mul_assoc], h1, Matrix.mul_one, Matrix.mul_assoc V (P a) (P a),
      hP.idem]
  sum_eq_one := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hP.sum_eq_one, Matrix.mul_one, h2]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- A vector of norm one is a unit vector in the `dotProduct` sense. -/
theorem unit_of_norm_evec_eq_one {N : Type*} [Fintype N] {v : N → ℂ} (h : ‖evec v‖ = 1) :
    star v ⬝ᵥ v = 1 := by
  rw [← inner_evec, inner_self_eq_norm_sq_to_K, h]
  simp
end
end MIPRE.QLD

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
theorem aliceSwap_mul_conjTranspose : M.aliceSwap * M.aliceSwapᴴ = 1 :=
  M.toFirst.swapA_mul_conjTranspose
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
theorem isPVM_alicePauli (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val)) (W : Bas) :
    IsPVM (M.alicePauli W) :=
  (((isPVM_povm_map _ (hprojA _) rdPauliVec).aOp).aOp).aOp
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
theorem isPVM_aliceConjPauli (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val)) (W : Bas) :
    IsPVM (M.aliceConjPauli W) :=
  isPVM_conj_unitary (M.isPVM_alicePauli hprojA W) M.aliceSwap_conjTranspose_mul
    M.aliceSwap_mul_conjTranspose
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
theorem isPVM_aliceTau (W : Bas) : IsPVM (M.aliceTau W) :=
  (isPVM_proj (isWeylFamily_weylOf W)).bOp
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
theorem isPVM_bobTau (W : Bas) : IsPVM (M.bobTau W) :=
  (isPVM_proj (isWeylFamily_weylOf W)).bOp
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
/-- **Alice's conjugated Pauli measurement, coarse-grained along `g_h(u)`, is the conjugated
`M^{(Pauli,W)}_{[g_h(u) = a]}`.** -/
theorem sum_aliceConjPauli_fibre (hd : 1 ≤ d) (W : Bas) (u : Point F m) (a : F) :
    ∑ h ∈ univ.filter fun h => (ancPoly (d := d) h).eval u = a, M.aliceConjPauli W h
      = M.aliceSwap * aOp (aOp (aOp (((pauliAtPOVM MA W u).mats a).val))) * M.aliceSwapᴴ := by
  rw [Finset.filter_congr fun h _ => by rw [ancPoly_eval hd]]
  simp only [aliceConjPauli, alicePauli]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← aOp_sum, ← aOp_sum, ← aOp_sum]
  have hY : ((MA (.pauli W)).map rdPauliVec).map (fun k => dotF k (indVec u))
      = pauliAtPOVM MA W u := by
    rw [POVM.map_map, pauliAtPOVM, show (fun a => dotF (rdPauliVec a) (indVec u)) = rdPauli u
      from funext fun a => (rdPauli_eq_dotF u a).symm]
  rw [← hY, POVM.map_mats]
end
end MIPRE.QLD.MirrorSimul

namespace MIPRE.QLD.MirrorSimul
noncomputable section
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
/-- **The honest projectors, coarse-grained along `g_h(u)`, are the syndrome projector, which is
Bob's exact Pauli measurement conjugated by his swap unitary** (`eq:qld-unitary-6`). -/
theorem sum_bobTau_fibre (hd : 1 ≤ d) (W : Bas) (u : Point F m) (a : F) :
    ∑ h ∈ univ.filter fun h => (ancPoly (d := d) h).eval u = a, M.bobTau W h
      = M.bobSwap * M.bobMTilde W (indVec u) a * M.bobSwapᴴ := by
  rw [Finset.filter_congr fun h _ => by rw [ancPoly_eval hd], M.bobSwap_conj_bobMTilde]
  simp only [bobTau]
  rw [← bOp_sum]
  rfl
end
end MIPRE.QLD.MirrorSimul

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD.MirrorSimul
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option synthInstance.maxSize 1000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}
variable (M : MirrorSimul ψ MA MB δ)
theorem _root_.solution {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (Δ : ((((dA × Anc F m) × M.Ea) × Anc F m)) × ((((dB × Anc F m) × M.Eb) × Anc F m)) → ℂ)
    (hΔ : ‖evec Δ‖ = 1)
    (hmove : ∀ (W : Bas) (h : Anc F m),
      (aOp (M.aliceTau W h) : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
          × (((dB × Anc F m) × M.Eb) × Anc F m))
        ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ) *ᵥ Δ
        = bOp (M.bobTau W h) *ᵥ Δ)
    {r : ℝ} (hr : ‖evec (M.physSwap *ᵥ M.physVec - Δ)‖ ≤ r) (W : Bas) :
    ∑ h : Anc F m, snorm Δ ((aOp (M.aliceConjPauli W h) : Matrix ((((dA × Anc F m) × M.Ea)
          × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m))
        ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
        - aOp (M.aliceTau W h)) ^ 2
      ≤ 2 * (11 * deltaLegs δ ε m d (Fintype.card F) + (m : ℝ) * d / Fintype.card F + 2 * r) := by
  refine sum_snorm_sq_sub_le_of_agree hΔ (M.isPVM_aliceConjPauli hprojA W).aOp
    (M.isPVM_aliceTau W).aOp ?_
  have hswap : ∀ h : Anc F m,
      qform Δ ((aOp (M.aliceConjPauli W h) : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
          × (((dB × Anc F m) × M.Eb) × Anc F m))
        ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
        * aOp (M.aliceTau W h))
        = bornProb Δ (M.aliceConjPauli W h) (M.bobTau W h) := by
    intro h
    rw [bornProb_eq_qform, qform, qform, ← Matrix.mulVec_mulVec, hmove W h,
      Matrix.mulVec_mulVec]
  have hfib := sum_uniform_bornProb_fibre_le (unit_of_norm_evec_eq_one hΔ)
    (M.isPVM_aliceConjPauli hprojA W) (M.isPVM_bobTau W) (enc := ancPoly (d := d))
    (fun h h' hne => ancPoly_toMv_ne hd hne)
  simp only [M.sum_aliceConjPauli_fibre hd, M.sum_bobTau_fibre hd] at hfib
  have hagree := M.sum_bornProb_fibre_ge (hm := hm) hψ hfail hprojA hprojB hd hδ hε Δ hΔ hr W
  rw [Finset.sum_congr rfl fun h (_ : h ∈ univ) => hswap h]
  linarith
end MIPRE.QLD.MirrorSimul
