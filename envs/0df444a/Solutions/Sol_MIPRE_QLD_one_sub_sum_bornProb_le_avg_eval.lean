-- Prove2me | solution 1 for MIPRE.QLD.one_sub_sum_bornProb_le_avg_eval
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:29:52.894066+00:00
-- url     : https://prove2.me/submissions/8e294e0d-7e9d-4ab4-b807-cf0bceddab76

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/PaddedStrategy.lean (solution of MIPRE.QLD.one_sub_sum_bornProb_le_avg_eval);
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
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_bornProb_nonneg
import Theorems.Thm_MIPRE_sum_bornProb
import Theorems.Thm_MIPRE_sum_bornProb_map

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree
noncomputable section
open Finset MvPolynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
/-- The univariate case, as a count: two unequal polynomials of degree at most `d` over a
field agree at no more than `d` points. This is the form `lem:lidt-sync-transfer` uses. -/
theorem card_agree_le_of_natDegree {p q : Polynomial F} (hpq : p ≠ q) {d : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) :
    #{t ∈ (univ : Finset F) | p.eval t = q.eval t} ≤ d := by
  have hne : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have hsubset : ({t ∈ (univ : Finset F) | p.eval t = q.eval t} : Finset F).val ⊆ (p - q).roots := by
    intro t ht
    simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [Polynomial.mem_roots hne]
    simpa [Polynomial.IsRoot, sub_eq_zero] using ht
  exact (Polynomial.card_le_degree_of_subset_roots hsubset).trans
    ((Polynomial.natDegree_sub_le p q).trans (max_le hp hq))
end
end MIPRE.LowDegree

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {X Y A B C : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq C] {ψ : dA × dB → ℂ} {x : X} {y : Y}
/-- `sum_bornProb_map` for two bare POVMs. -/
theorem sum_bornProb_map' {A B : Type*} [Fintype A] [Fintype B] (P : POVM A dA) (Q : POVM B dB)
    (f : A → C) (g : B → C) :
    ∑ c, bornProb ψ (((P.map f).mats c).val) (((Q.map g).mats c).val)
      = ∑ a, ∑ b, (if f a = g b then (1 : ℝ) else 0)
          * bornProb ψ ((P.mats a).val) ((Q.mats b).val) :=
  sum_bornProb_map (MA := fun _ : Unit => P) (MB := fun _ : Unit => Q) (x := ()) (y := ()) f g
end
end MIPRE

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
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
theorem coeff_toPoly (f : LinePoly F n) (i : Fin (n + 1)) :
    (toPoly f).coeff (i : ℕ) = f i := by
  classical
  rw [toPoly, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single_of_mem i (mem_univ i) fun j _ hji => ?_]
  · rw [Polynomial.coeff_monomial, if_pos rfl]
  · rw [Polynomial.coeff_monomial, if_neg fun h => hji (Fin.ext h)]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
theorem toPoly_injective : Function.Injective (toPoly : LinePoly F n → Polynomial F) := by
  intro f g h
  funext i
  rw [← coeff_toPoly f i, ← coeff_toPoly g i, h]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
/-- **Two distinct line polynomials of degree at most `n` agree at at most `n` parameters.** The
collision bound the pasting lemma asks of the outcome map, for the map that evaluates a line
polynomial at the parameter of the sampled point. -/
theorem card_agree_linePoly_le {f g : LinePoly F n} (h : f ≠ g) :
    #{t ∈ (univ : Finset F) | LinePoly.eval f t = LinePoly.eval g t} ≤ n := by
  refine le_trans (le_of_eq (congrArg Finset.card (Finset.filter_congr fun t _ => ?_)))
    (MIPRE.LowDegree.card_agree_le_of_natDegree
      (fun he => h (toPoly_injective he))
      (natDegree_toPoly_le f) (natDegree_toPoly_le g))
  rw [eval_toPoly, eval_toPoly]
end
end MIPRE.QLD

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA : Type} [Fintype dA] [DecidableEq dA] {hm : m ∣ Fintype.card F}
variable (hm4 : 4 * m ∣ Fintype.card F)
variable (hm)
variable {dA' dB' : Type*} [Fintype dA'] [DecidableEq dA'] [Fintype dB'] [DecidableEq dB']
omit [Algebra (ZMod 2) F] [NeZero m] in
theorem _root_.solution {n : ℕ} {ψ : dA' × dB' → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (LA : POVM (LinePoly F n) dA') (LB : POVM (LinePoly F n) dB') :
    1 - ∑ f, bornProb ψ ((LA.mats f).val) ((LB.mats f).val)
      ≤ (Fintype.card F : ℝ)⁻¹ * ∑ t : F, (1 - ∑ a : F,
          bornProb ψ (((LA.map fun f => LinePoly.eval f t).mats a).val)
            (((LB.map fun f => LinePoly.eval f t).mats a).val))
        + (n : ℝ) / Fintype.card F := by
  classical
  have hq : (0 : ℝ) < Fintype.card F := Nat.cast_pos.mpr Fintype.card_pos
  set b : LinePoly F n → LinePoly F n → ℝ := fun f g =>
    bornProb ψ ((LA.mats f).val) ((LB.mats g).val) with hb
  have hb0 : ∀ f g, 0 ≤ b f g := fun f g =>
    bornProb_nonneg ψ (LA.posSemidef f) (LB.posSemidef g)
  have hb1 : ∑ f, ∑ g, b f g = 1 := sum_bornProb hψ LA LB
  -- the per-parameter identity
  have hsplit : ∀ t : F, ∑ a : F,
      bornProb ψ (((LA.map fun f => LinePoly.eval f t).mats a).val)
        (((LB.map fun f => LinePoly.eval f t).mats a).val)
      = ∑ f, b f f + ∑ f, ∑ g,
          (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g := by
    intro t
    rw [sum_bornProb_map', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    have hterm : ∀ g, (if LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g
        = (if f = g then (1 : ℝ) else 0) * b f g
          + (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g := by
      intro g
      by_cases hfg : f = g
      · subst hfg
        simp
      · simp [hfg]
    rw [Finset.sum_congr rfl fun g _ => hterm g, Finset.sum_add_distrib]
    congr 1
    simp [Finset.sum_ite_eq]
  -- the collision count
  have hcoll : ∀ f g : LinePoly F n,
      ∑ t : F, (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) ≤ n := by
    intro f g
    by_cases hfg : f = g
    · simp [hfg]
    · rw [Finset.sum_boole]
      have h1 : (univ.filter fun t : F => f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t)
          = univ.filter fun t : F => LinePoly.eval f t = LinePoly.eval g t :=
        Finset.filter_congr fun t _ => ⟨fun h => h.2, fun h => ⟨hfg, h⟩⟩
      rw [h1]
      exact_mod_cast card_agree_linePoly_le hfg
  have hrest : ∑ t : F, ∑ f, ∑ g,
      (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g ≤ n := by
    rw [Finset.sum_comm]
    calc ∑ f, ∑ t : F, ∑ g,
          (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g
        = ∑ f, ∑ g, (∑ t : F,
            (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0)) * b f g := by
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun g _ => (Finset.sum_mul _ _ _).symm
      _ ≤ ∑ f, ∑ g, (n : ℝ) * b f g :=
          Finset.sum_le_sum fun f _ => Finset.sum_le_sum fun g _ =>
            mul_le_mul_of_nonneg_right (hcoll f g) (hb0 f g)
      _ = n := by
          simp only [← Finset.mul_sum]
          rw [hb1, mul_one]
  have hsum : (Fintype.card F : ℝ) * (1 - ∑ f, b f f)
      = ∑ t : F, (1 - ∑ a : F,
          bornProb ψ (((LA.map fun f => LinePoly.eval f t).mats a).val)
            (((LB.map fun f => LinePoly.eval f t).mats a).val))
        + ∑ t : F, ∑ f, ∑ g,
          (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g := by
    simp only [hsplit]
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun t _ => show (1 - (∑ f, b f f + ∑ f, ∑ g,
        (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g)
        + ∑ f, ∑ g, (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g)
        = 1 - ∑ f, b f f by ring]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hmain : 1 - ∑ f, b f f
      = (Fintype.card F : ℝ)⁻¹ * ((∑ t : F, (1 - ∑ a : F,
          bornProb ψ (((LA.map fun f => LinePoly.eval f t).mats a).val)
            (((LB.map fun f => LinePoly.eval f t).mats a).val)))
        + ∑ t : F, ∑ f, ∑ g,
          (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g) := by
    rw [← hsum, inv_mul_cancel_left₀ hq.ne']
  rw [hmain, mul_add]
  have hlast : (Fintype.card F : ℝ)⁻¹ * ∑ t : F, ∑ f, ∑ g,
      (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g
        ≤ (n : ℝ) / Fintype.card F := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hrest (inv_nonneg.mpr hq.le)
  linarith
end MIPRE.QLD
