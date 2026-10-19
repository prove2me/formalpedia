-- Prove2me | solution 1 for MIPStarRE.LDT.Commutativity.leftRightTensor_prefix_pointMeasurement_normalization
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:56:41.092509+00:00
-- url     : https://prove2.me/submissions/ffb94bc0-1b2a-4419-a75b-f66916365059

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainBasic/Normalization.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/SubMeasurementCore.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainBasic/Normalization.lean (solution of MIPStarRE.LDT.Commutativity.leftRightTensor_prefix_pointMeasurement_normalization);
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
import Mathlib.Algebra.Field.IsField
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
import Mathlib.Analysis.LocallyConvex.WithSeminorms
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
import Mathlib.Data.Countable.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
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
import Mathlib.Data.Fintype.OfMap
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
import Mathlib.Logic.Function.Basic
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
import Mathlib.Order.MinMax
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
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Real
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ConsistencyBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Theorems.Thm_MIPStarRE_LDT_Measurement_sum_eq
import Theorems.Thm_MIPStarRE_LDT_ProjMeas_outcome_hermitian
import Theorems.Thm_MIPStarRE_LDT_ProjSubMeas_outcome_orthogonal
import Theorems.Thm_MIPStarRE_LDT_SubMeas_outcome_hermitian
import Theorems.Thm_MIPStarRE_LDT_SubMeas_outcome_le_one
import Theorems.Thm_MIPStarRE_LDT_leftTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_le_one
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_rightTensor_eq_opTensor
import Theorems.Thm_MIPStarRE_LDT_opTensor_mono_left
import Theorems.Thm_MIPStarRE_LDT_opTensor_mul
import Theorems.Thm_MIPStarRE_LDT_rightTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_rightTensor_one
import Theorems.Thm_MIPStarRE_Quantum_sq_le_self

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
/-- Distinct outcomes of a projective measurement are orthogonal. -/
theorem ProjMeas.outcome_orthogonal {α : Type*}
    {ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι]
    (P : ProjMeas α ι) (a b : α) (hab : a ≠ b) :
    P.outcome a * P.outcome b = 0 := by
  let P' : ProjSubMeas α ι :=
    { toSubMeas := P.toSubMeas
      proj := P.proj }
  simpa [P'] using P'.outcome_orthogonal a b hab
end
end MIPStarRE.LDT

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.Commutativity
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem _root_.solution
    {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) (R : ProjMeas β ι) :
    ∑ a : α,
        (∑ b : β,
          leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            rightTensor (ι₁ := ι) (R.outcome b)) *
        (∑ b : β,
          leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            rightTensor (ι₁ := ι) (R.outcome b))ᴴ ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  let D : α → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    ∑ b : β,
      leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
        rightTensor (ι₁ := ι) (R.outcome b)
  have hrow_le : ∀ a : α, D a * (D a)ᴴ ≤ leftTensor (ι₂ := ι) (A.outcome a) := by
    intro a
    have hrow_expand :
        D a * (D a)ᴴ =
          ∑ b : β,
            opTensor (A.outcome a * (B.outcome b * (B.outcome b * A.outcome a)))
              (R.outcome b) := by
      unfold D
      calc
        (∑ b : β,
            leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
              rightTensor (ι₁ := ι) (R.outcome b)) *
            (∑ b : β,
              leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                rightTensor (ι₁ := ι) (R.outcome b))ᴴ
          = (∑ b : β,
            leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
              rightTensor (ι₁ := ι) (R.outcome b)) *
              (∑ c : β,
                (leftTensor (ι₂ := ι) (A.outcome a * B.outcome c) *
                  rightTensor (ι₁ := ι) (R.outcome c))ᴴ) := by
                rw [Matrix.conjTranspose_sum]
        _ = ∑ b : β, ∑ c : β,
              (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                rightTensor (ι₁ := ι) (R.outcome b)) *
              (leftTensor (ι₂ := ι) (A.outcome a * B.outcome c) *
                rightTensor (ι₁ := ι) (R.outcome c))ᴴ := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl ?_
                intro b _
                rw [Finset.mul_sum]
        _ = ∑ b : β,
              (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                rightTensor (ι₁ := ι) (R.outcome b)) *
              (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                rightTensor (ι₁ := ι) (R.outcome b))ᴴ := by
                refine Finset.sum_congr rfl ?_
                intro b _
                rw [Finset.sum_eq_single b]
                · intro c _ hcb
                  have hbc : b ≠ c := fun h => hcb h.symm
                  have horth : R.outcome b * R.outcome c = 0 := R.outcome_orthogonal b c hbc
                  calc
                    (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                        rightTensor (ι₁ := ι) (R.outcome b)) *
                        (leftTensor (ι₂ := ι) (A.outcome a * B.outcome c) *
                          rightTensor (ι₁ := ι) (R.outcome c))ᴴ
                      = opTensor (A.outcome a * B.outcome b) (R.outcome b) *
                          (opTensor (A.outcome a * B.outcome c) (R.outcome c))ᴴ := by
                          rw [leftTensor_mul_rightTensor_eq_opTensor,
                            leftTensor_mul_rightTensor_eq_opTensor]
                    _ = opTensor (A.outcome a * B.outcome b) (R.outcome b) *
                          opTensor ((A.outcome a * B.outcome c)ᴴ) ((R.outcome c)ᴴ) := by
                          rw [conjTranspose_opTensor]
                    _ = opTensor ((A.outcome a * B.outcome b) *
                            ((A.outcome a * B.outcome c)ᴴ))
                          (R.outcome b * (R.outcome c)ᴴ) := by
                          rw [opTensor_mul]
                    _ = 0 := by
                          have hRherm : (R.outcome c)ᴴ = R.outcome c :=
                            R.outcome_hermitian c
                          rw [hRherm, horth]
                          simp [opTensor]
                · simp
        _ = ∑ b : β,
            opTensor (A.outcome a * (B.outcome b * (B.outcome b * A.outcome a)))
              (R.outcome b) := by
                refine Finset.sum_congr rfl ?_
                intro b _
                calc
                  (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                        rightTensor (ι₁ := ι) (R.outcome b)) *
                      (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                        rightTensor (ι₁ := ι) (R.outcome b))ᴴ
                    = opTensor (A.outcome a * B.outcome b) (R.outcome b) *
                        (opTensor (A.outcome a * B.outcome b) (R.outcome b))ᴴ := by
                        rw [leftTensor_mul_rightTensor_eq_opTensor]
                  _ = opTensor (A.outcome a * B.outcome b) (R.outcome b) *
                        opTensor ((A.outcome a * B.outcome b)ᴴ) ((R.outcome b)ᴴ) := by
                        rw [conjTranspose_opTensor]
                  _ = opTensor ((A.outcome a * B.outcome b) *
                          ((A.outcome a * B.outcome b)ᴴ))
                        (R.outcome b * (R.outcome b)ᴴ) := by
                        rw [opTensor_mul]
                  _ = opTensor (A.outcome a * (B.outcome b * (B.outcome b * A.outcome a)))
                        (R.outcome b) := by
                        have hABadj : (A.outcome a * B.outcome b)ᴴ =
                            B.outcome b * A.outcome a := by
                          rw [Matrix.conjTranspose_mul, A.outcome_hermitian a,
                            B.outcome_hermitian b]
                        have hRherm : (R.outcome b)ᴴ = R.outcome b :=
                          R.outcome_hermitian b
                        rw [hABadj, hRherm, R.proj b]
                        congr 1
                        noncomm_ring
    have hbound_terms :
        (∑ b : β,
            opTensor (A.outcome a * (B.outcome b * (B.outcome b * A.outcome a)))
              (R.outcome b)) ≤
          ∑ b : β, opTensor (A.outcome a) (R.outcome b) := by
      refine Finset.sum_le_sum ?_
      intro b _
      apply opTensor_mono_left
      · have hBsq : B.outcome b * B.outcome b ≤ B.outcome b :=
          MIPStarRE.Quantum.sq_le_self (B.outcome_pos b) (B.outcome_le_one b)
        have hleft1 :
            A.outcome a * (B.outcome b * B.outcome b) * A.outcome a ≤
              A.outcome a * B.outcome b * A.outcome a := by
          exact IsSelfAdjoint.conjugate_le_conjugate hBsq (A.outcome_hermitian a)
        have hleft2 :
            A.outcome a * B.outcome b * A.outcome a ≤
              A.outcome a * (1 : MIPStarRE.Quantum.Op ι) * A.outcome a := by
          exact IsSelfAdjoint.conjugate_le_conjugate (B.outcome_le_one b) (A.outcome_hermitian a)
        have hleft3 :
            A.outcome a * (1 : MIPStarRE.Quantum.Op ι) * A.outcome a ≤
              A.outcome a := by
          simpa using MIPStarRE.Quantum.sq_le_self (A.outcome_pos a) (A.outcome_le_one a)
        calc
          A.outcome a * (B.outcome b * (B.outcome b * A.outcome a))
              = A.outcome a * (B.outcome b * B.outcome b) * A.outcome a := by
                noncomm_ring
          _ ≤ A.outcome a * B.outcome b * A.outcome a := hleft1
          _ ≤ A.outcome a * (1 : MIPStarRE.Quantum.Op ι) * A.outcome a := hleft2
          _ ≤ A.outcome a := hleft3
      · exact R.outcome_pos b
    have hsum_right :
        (∑ b : β, opTensor (A.outcome a) (R.outcome b)) =
          leftTensor (ι₂ := ι) (A.outcome a) := by
      calc
        (∑ b : β, opTensor (A.outcome a) (R.outcome b))
            = ∑ b : β,
                leftTensor (ι₂ := ι) (A.outcome a) *
                  rightTensor (ι₁ := ι) (R.outcome b) := by
              simp [leftTensor_mul_rightTensor_eq_opTensor]
        _ = leftTensor (ι₂ := ι) (A.outcome a) *
              (∑ b : β, rightTensor (ι₁ := ι) (R.outcome b)) := by
              rw [← Matrix.mul_sum]
        _ = leftTensor (ι₂ := ι) (A.outcome a) *
              rightTensor (ι₁ := ι) (∑ b : β, R.outcome b) := by
              rw [rightTensor_finset_sum]
        _ = leftTensor (ι₂ := ι) (A.outcome a) := by
              rw [R.sum_eq, rightTensor_one]
              simp
    calc
      D a * (D a)ᴴ
          = ∑ b : β,
            opTensor (A.outcome a * (B.outcome b * (B.outcome b * A.outcome a)))
              (R.outcome b) := hrow_expand
      _ ≤ ∑ b : β, opTensor (A.outcome a) (R.outcome b) := hbound_terms
      _ = leftTensor (ι₂ := ι) (A.outcome a) := hsum_right
  calc
    ∑ a : α,
        (∑ b : β,
          leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            rightTensor (ι₁ := ι) (R.outcome b)) *
        (∑ b : β,
          leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            rightTensor (ι₁ := ι) (R.outcome b))ᴴ
      = ∑ a : α, D a * (D a)ᴴ := by rfl
    _ ≤ ∑ a : α, leftTensor (ι₂ := ι) (A.outcome a) := by
          exact Finset.sum_le_sum fun a _ => hrow_le a
    _ = leftTensor (ι₂ := ι) A.total := by
          rw [leftTensor_finset_sum, A.sum_eq_total]
    _ ≤ 1 := leftTensor_le_one (ι₂ := ι) A.total_le_one
end MIPStarRE.LDT.Commutativity
