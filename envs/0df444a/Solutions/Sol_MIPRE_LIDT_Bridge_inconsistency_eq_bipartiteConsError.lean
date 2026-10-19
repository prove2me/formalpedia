-- Prove2me | solution 1 for MIPRE.LIDT.Bridge.inconsistency_eq_bipartiteConsError
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:56:40.494754+00:00
-- url     : https://prove2.me/submissions/455a15bd-aa37-49e3-9c05-e1bd67c0ea6e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/QuantumState.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Bridge/Consistency.lean (solution of MIPRE.LIDT.Bridge.inconsistency_eq_bipartiteConsError);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Nat
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Real
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_MIPRE_Background_LIDT_Bridge_Field
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_MIPRE_Background_LIDT_Bridge_Polynomial
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_MIPRE_Background_LIDT_Bridge_Measurement
import Definitions.Def_MIPRE_Background_LIDT_Bridge_Strategy
import Theorems.Thm_MIPStarRE_LDT_ev_sum
import Theorems.Thm_MIPStarRE_LDT_opTensor_sum_left_univ
import Theorems.Thm_MIPStarRE_LDT_opTensor_sum_right_univ
import Theorems.Thm_MIPStarRE_Quantum_normalizedTrace_mul_comm
import Theorems.Thm_MIPStarRE_Quantum_normalizedTrace_smul

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT.PureState
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
theorem normalizedTrace_density_mul {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : PureState ι) (X : MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.normalizedTrace ((ψ : QuantumState ι).density * X) =
      star ψ.vector ⬝ᵥ (X *ᵥ ψ.vector) := by
  have hcard : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    MIPStarRE.Quantum.normalizedTrace ((ψ : QuantumState ι).density * X)
      = MIPStarRE.Quantum.normalizedTrace (X * (ψ : QuantumState ι).density) := by
          rw [MIPStarRE.Quantum.normalizedTrace_mul_comm]
    _ = MIPStarRE.Quantum.normalizedTrace (X * ψ.density) := by rfl
    _ = MIPStarRE.Quantum.normalizedTrace
          ((Fintype.card ι : ℂ) • (X * Matrix.vecMulVec ψ.vector (star ψ.vector))) := by
          simp [density, pureDensity]
    _ = (Fintype.card ι : ℂ) *
          MIPStarRE.Quantum.normalizedTrace (X * Matrix.vecMulVec ψ.vector (star ψ.vector)) := by
          rw [MIPStarRE.Quantum.normalizedTrace_smul]
    _ = (Fintype.card ι : ℂ) *
          (((X * Matrix.vecMulVec ψ.vector (star ψ.vector)).trace) /
            (Fintype.card ι : ℂ)) := by
          simp [MIPStarRE.Quantum.normalizedTrace]
    _ = (Fintype.card ι : ℂ) *
          (((Matrix.vecMulVec (X *ᵥ ψ.vector) (star ψ.vector)).trace) /
            (Fintype.card ι : ℂ)) := by
          rw [Matrix.mul_vecMulVec]
    _ = (Fintype.card ι : ℂ) *
          (((X *ᵥ ψ.vector) ⬝ᵥ star ψ.vector) / (Fintype.card ι : ℂ)) := by
          rw [Matrix.trace_vecMulVec]
    _ = (X *ᵥ ψ.vector) ⬝ᵥ star ψ.vector := by
          field_simp [hcard]
    _ = star ψ.vector ⬝ᵥ (X *ᵥ ψ.vector) := by
          rw [dotProduct_comm]
end
end MIPStarRE.LDT.PureState

namespace MIPStarRE.LDT
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
theorem PureState.ev_eq_re_inner {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : PureState ι) (X : MIPStarRE.Quantum.Op ι) :
    ev (ψ : QuantumState ι) X =
      Complex.re (star ψ.vector ⬝ᵥ (X *ᵥ ψ.vector)) := by
  unfold ev
  rw [ψ.normalizedTrace_density_mul]
end
end MIPStarRE.LDT

namespace MIPRE.LIDT.Bridge
noncomputable section
open MIPStarRE.LDT (ProjStrat QuantumState PureState ev)
open Matrix
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
/-- Expectation values in the induced strategy are the Born-rule expectations of `S.ψ`. -/
theorem ev_toProjStrat (S : TensorProductStrategy (lidtGame F m d))
    (X : Matrix (Fin S.dA × Fin S.dB) (Fin S.dA × Fin S.dB) ℂ) :
    ev (toProjStrat S).state X = (star S.ψ ⬝ᵥ (X *ᵥ S.ψ)).re :=
  (pureState S).ev_eq_re_inner X
end
end MIPRE.LIDT.Bridge

namespace MIPRE.LIDT.Bridge
section
open MIPStarRE.LDT
open scoped MatrixOrder
variable {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
/-- Expectation values of tensor products of measurement operators are nonnegative. -/
theorem ev_opTensor_outcome_nonneg (ψ : QuantumState (ιA × ιB)) (A : SubMeas α ιA)
    (B : SubMeas β ιB) (a : α) (b : β) :
    0 ≤ ev ψ (opTensor (A.outcome a) (B.outcome b)) :=
  ev_nonneg_of_psd ψ _ (opTensor_nonneg (A.outcome_pos a) (B.outcome_pos b))
end
end MIPRE.LIDT.Bridge

namespace MIPRE.LIDT.Bridge
section
open MIPStarRE.LDT
open scoped MatrixOrder
variable {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
/-- The total mass of two complete measurements on a normalized state is one. -/
theorem sum_ev_opTensor_outcome (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (A : SubMeas α ιA) (B : SubMeas β ιB) (hA : A.total = 1) (hB : B.total = 1) :
    ∑ a, ∑ b, ev ψ (opTensor (A.outcome a) (B.outcome b)) = 1 := by
  have h : ∑ a, ∑ b, opTensor (A.outcome a) (B.outcome b) =
      (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
    simp_rw [← opTensor_sum_right_univ, ← opTensor_sum_left_univ, A.sum_eq_total, B.sum_eq_total,
      hA, hB]
    exact Matrix.one_kronecker_one
  rw [← ev_one_of_isNormalized ψ hψ, ← h, ev_sum]
  exact Finset.sum_congr rfl fun a _ => (ev_sum ψ _).symm
end
end MIPRE.LIDT.Bridge

namespace MIPRE.LIDT.Bridge
section
open MIPStarRE.LDT
open scoped MatrixOrder
variable {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
/-- The matching mass of two complete measurements is at most one. -/
theorem qBipartiteMatchMass_le_one (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (A : SubMeas α ιA) (B : SubMeas α ιB) (hA : A.total = 1) (hB : B.total = 1) :
    qBipartiteMatchMass ψ A B ≤ 1 := by
  rw [← sum_ev_opTensor_outcome ψ hψ A B hA hB]
  unfold qBipartiteMatchMass
  refine Finset.sum_le_sum fun a _ => ?_
  exact Finset.single_le_sum (fun b _ => ev_opTensor_outcome_nonneg ψ A B a b) (Finset.mem_univ a)
end
end MIPRE.LIDT.Bridge

namespace MIPRE.LIDT.Bridge
section
open MIPStarRE.LDT
open scoped MatrixOrder
variable {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
/-- For complete measurements on a normalized state the defect is `1 − matching mass`. -/
theorem qBipartiteConsDefect_of_complete (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (A : SubMeas α ιA) (B : SubMeas α ιB) (hA : A.total = 1) (hB : B.total = 1) :
    qBipartiteConsDefect ψ A B = 1 - qBipartiteMatchMass ψ A B := by
  have h1 : ev ψ (opTensor A.total B.total) = 1 := by
    rw [hA, hB, show opTensor (1 : MIPStarRE.Quantum.Op ιA) (1 : MIPStarRE.Quantum.Op ιB) = 1 from
      Matrix.one_kronecker_one]
    exact ev_one_of_isNormalized ψ hψ
  simp only [qBipartiteConsDefect, h1]
  exact max_eq_right (sub_nonneg.mpr (qBipartiteMatchMass_le_one ψ hψ A B hA hB))
end
end MIPRE.LIDT.Bridge

namespace MIPRE.LIDT.Bridge
section
open MIPStarRE.LDT
open scoped MatrixOrder
variable {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
/-- For complete measurements on a normalized state the defect is the off-diagonal mass. -/
theorem qBipartiteConsDefect_eq_offDiagonal [DecidableEq α] (ψ : QuantumState (ιA × ιB))
    (hψ : ψ.IsNormalized) (A : SubMeas α ιA) (B : SubMeas α ιB) (hA : A.total = 1)
    (hB : B.total = 1) :
    qBipartiteConsDefect ψ A B =
      ∑ a, ∑ b, if a = b then 0 else ev ψ (opTensor (A.outcome a) (B.outcome b)) := by
  rw [qBipartiteConsDefect_of_complete ψ hψ A B hA hB, ← sum_ev_opTensor_outcome ψ hψ A B hA hB]
  unfold qBipartiteMatchMass
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : ∀ b, (if a = b then (0 : ℝ) else ev ψ (opTensor (A.outcome a) (B.outcome b))) =
      ev ψ (opTensor (A.outcome a) (B.outcome b)) -
        if a = b then ev ψ (opTensor (A.outcome a) (B.outcome b)) else 0 := by
    intro b; split_ifs <;> simp
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
end
end MIPRE.LIDT.Bridge

namespace MIPRE.LIDT.Bridge
section
open MIPStarRE.LDT
open scoped MatrixOrder
variable {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
/-- The consistency error under the uniform distribution is the average of the defects. -/
theorem bipartiteConsError_uniform {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {ιA ιB α : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Fintype α]
    (ψ : QuantumState (ιA × ιB)) (A : IdxSubMeas X α ιA) (B : IdxSubMeas X α ιB) :
    bipartiteConsError ψ (uniformDistribution X) A B =
      (1 / (Fintype.card X : ℝ)) * ∑ x, qBipartiteConsDefect ψ (A x) (B x) := by
  classical
  unfold bipartiteConsError avgOver uniformDistribution
  simp only [Distribution.uniformOnFinset_support, Distribution.uniformOnFinset_weight,
    Finset.mem_univ, if_true, Finset.card_univ, Finset.mul_sum]
end
end MIPRE.LIDT.Bridge

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Bridge
open MIPStarRE.LDT (QuantumState ev opTensor qBipartiteConsDefect bipartiteConsError uniformDistribution SubMeas IdxSubMeas)
open Matrix
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
theorem _root_.solution (S : TensorProductStrategy (lidtGame F m d))
    {X X' α α' : Type*} [Fintype X] [Fintype X'] [DecidableEq X'] [Nonempty X'] [Fintype α]
    [DecidableEq α] [Fintype α']
    (qe : X ≃ X') (e : α ≃ α')
    (M : X → POVM α (Fin S.dA)) (N : X → POVM α (Fin S.dB))
    (A : IdxSubMeas X' α' (Fin S.dA)) (B : IdxSubMeas X' α' (Fin S.dB))
    (hA : ∀ x', (A x').total = 1) (hB : ∀ x', (B x').total = 1)
    (hM : ∀ x a, ((M x).mats a).val = (A (qe x)).outcome (e a))
    (hN : ∀ x a, ((N x).mats a).val = (B (qe x)).outcome (e a)) :
    inconsistency (uniform X) S.ψ M N =
      bipartiteConsError (toProjStrat S).state (uniformDistribution X') A B := by
  classical
  have hcard : Fintype.card X = Fintype.card X' := Fintype.card_congr qe
  unfold inconsistency uniform
  rw [bipartiteConsError_uniform]
  conv_rhs => rw [Finset.mul_sum]
  simp only [one_div, hcard]
  refine Fintype.sum_equiv qe _ _ fun x => ?_
  congr 1
  rw [qBipartiteConsDefect_eq_offDiagonal _ (toProjStrat S).isNormalized _ _ (hA _) (hB _)]
  refine Fintype.sum_equiv e _ _ fun a => ?_
  refine Fintype.sum_equiv e _ _ fun b => ?_
  simp only [e.injective.eq_iff, hM, hN, ev_toProjStrat]
  rfl
end MIPRE.LIDT.Bridge
