-- Prove2me | solution 1 for MIPStarRE.LDT.Preliminaries.question_switchSandwich_left_gap
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:06:19.774012+00:00
-- url     : https://prove2.me/submissions/7c76f0a2-d63e-4984-b9a0-97a9dc23c4ba

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/SwitchSandwichGapBounds/Left.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/SwitchSandwichPrep/Core.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/SwitchSandwichGapBounds/Left.lean (solution of MIPStarRE.LDT.Preliminaries.question_switchSandwich_left_gap);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Hom
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ConsistencyBridges
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_subMeas_diagMass_le_one
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_sum_ev_mul_leftBounded_le_of_leftHermitian
import Theorems.Thm_MIPStarRE_LDT_ev_sub
import Theorems.Thm_MIPStarRE_LDT_leftTensor_le_one
import Theorems.Thm_MIPStarRE_LDT_leftTensor_nonneg
import Theorems.Thm_MIPStarRE_LDT_rightTensor_nonneg
import Theorems.Thm_MIPStarRE_Quantum_sq_le_self

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT.Preliminaries
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
/-- Any `OpBounded01` operator is Hermitian. -/
lemma opBounded01_hermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : MIPStarRE.Quantum.Op ι} (hB : OpBounded01 B) :
    Bᴴ = B :=
  (Matrix.nonneg_iff_posSemidef.mp hB.nonnegative).isHermitian.eq
end
end MIPStarRE.LDT.Preliminaries

namespace MIPStarRE.LDT.Preliminaries
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
/-- Any `OpBounded01` operator satisfies `B * B ≤ 1`. -/
lemma opBounded01_sq_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : MIPStarRE.Quantum.Op ι} (hB : OpBounded01 B) :
    B * B ≤ 1 := by
  have hB_le_one : B ≤ 1 := sub_nonneg.mp hB.boundedByIdentity
  exact le_trans
    (MIPStarRE.Quantum.sq_le_self hB.nonnegative hB_le_one)
    hB_le_one
end
end MIPStarRE.LDT.Preliminaries

namespace MIPStarRE.LDT.Preliminaries
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
/-- Left tensoring preserves the `0 ≤ B ≤ 1` bounds. -/
lemma leftTensor_opBounded01
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {B : MIPStarRE.Quantum.Op ι₁} (hB : OpBounded01 B) :
    OpBounded01 (leftTensor (ι₂ := ι₂) B) := by
  constructor
  · exact leftTensor_nonneg (ι₂ := ι₂) hB.nonnegative
  · exact sub_nonneg.mpr
      (leftTensor_le_one (ι₂ := ι₂) (sub_nonneg.mp hB.boundedByIdentity))
end
end MIPStarRE.LDT.Preliminaries

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.Preliminaries
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (A : ProjSubMeas Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) (hB : OpBounded01 B) :
    |(∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            leftTensor (ι₂ := ι) (A.outcome a))) -
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a))| ≤
      Real.sqrt
        (qSDD ψ A.toSubMeas.liftLeft A.toSubMeas.liftRight) := by
  let LB : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) B
  have hLB : OpBounded01 LB := by
    dsimp [LB]
    exact leftTensor_opBounded01 (ι₂ := ι) hB
  have hLB_nonneg : 0 ≤ LB := by
    exact hLB.nonnegative
  have hLB_herm : LBᴴ = LB := by
    exact opBounded01_hermitian hLB
  have hLB_sq_le_one : LB * LB ≤ 1 := by
    exact opBounded01_sq_le_one hLB
  have hLAherm :
      ∀ a : Outcome,
        (leftTensor (ι₂ := ι) (A.outcome a))ᴴ =
          leftTensor (ι₂ := ι) (A.outcome a) := by
    intro a
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) (A.outcome_pos a))).isHermitian.eq
  have hRAherm :
      ∀ a : Outcome,
        (rightTensor (ι₁ := ι) (A.outcome a))ᴴ =
          rightTensor (ι₁ := ι) (A.outcome a) := by
    intro a
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (rightTensor_nonneg (ι₁ := ι) (A.outcome_pos a))).isHermitian.eq
  have hDherm :
      ∀ a : Outcome,
        (leftTensor (ι₂ := ι) (A.outcome a) -
          rightTensor (ι₁ := ι) (A.outcome a))ᴴ =
          leftTensor (ι₂ := ι) (A.outcome a) -
            rightTensor (ι₁ := ι) (A.outcome a) := by
    intro a
    simp [hLAherm a, hRAherm a]
  have haux :
      |∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              (LB *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a))))|
        ≤
      Real.sqrt
        (∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              leftTensor (ι₂ := ι) (A.outcome a))) *
        Real.sqrt
          (∑ a : Outcome,
            ev ψ
              (((leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a))ᴴ) *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a)))) := by
    simpa using
      sum_ev_mul_leftBounded_le_of_leftHermitian ψ LB
        (fun a => leftTensor (ι₂ := ι) (A.outcome a))
        (fun a =>
          leftTensor (ι₂ := ι) (A.outcome a) -
            rightTensor (ι₁ := ι) (A.outcome a))
        hLB_herm hLB_sq_le_one hLAherm hDherm
  have hdiag_le_one :
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) (A.outcome a)) ≤ 1 := by
    simpa [SubMeas.liftLeft] using
      subMeas_diagMass_le_one ψ hψ A.toSubMeas.liftLeft
  have hsqrt_diag :
      Real.sqrt
        (∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              leftTensor (ι₂ := ι) (A.outcome a))) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiag_le_one
  have haux' :
      |∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              (LB *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a))))|
        ≤
      Real.sqrt
        (∑ a : Outcome,
          ev ψ
            (((leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a))ᴴ) *
              (leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)))) := by
    calc
      |∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              (LB *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a))))|
        ≤
          Real.sqrt
            (∑ a : Outcome,
              ev ψ
                (leftTensor (ι₂ := ι) (A.outcome a) *
                  leftTensor (ι₂ := ι) (A.outcome a))) *
            Real.sqrt
              (∑ a : Outcome,
                ev ψ
                  (((leftTensor (ι₂ := ι) (A.outcome a) -
                        rightTensor (ι₁ := ι) (A.outcome a))ᴴ) *
                    (leftTensor (ι₂ := ι) (A.outcome a) -
                      rightTensor (ι₁ := ι) (A.outcome a)))) := haux
      _ ≤ 1 *
            Real.sqrt
              (∑ a : Outcome,
                ev ψ
                  (((leftTensor (ι₂ := ι) (A.outcome a) -
                        rightTensor (ι₁ := ι) (A.outcome a))ᴴ) *
                    (leftTensor (ι₂ := ι) (A.outcome a) -
                      rightTensor (ι₁ := ι) (A.outcome a)))) := by
            exact mul_le_mul_of_nonneg_right hsqrt_diag (Real.sqrt_nonneg _)
      _ = Real.sqrt
            (∑ a : Outcome,
              ev ψ
                (((leftTensor (ι₂ := ι) (A.outcome a) -
                      rightTensor (ι₁ := ι) (A.outcome a))ᴴ) *
                  (leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)))) := by
            ring
  have hrewrite :
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            leftTensor (ι₂ := ι) (A.outcome a)) -
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a))
        =
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            (LB *
              (leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)))) := by
    calc
      (∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              leftTensor (ι₂ := ι) B *
              leftTensor (ι₂ := ι) (A.outcome a))) -
          ∑ a : Outcome,
            ev ψ
              (leftTensor (ι₂ := ι) (A.outcome a) *
                leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) (A.outcome a))
        =
        ∑ a : Outcome,
          (ev ψ
              (leftTensor (ι₂ := ι) (A.outcome a) *
                leftTensor (ι₂ := ι) B *
                leftTensor (ι₂ := ι) (A.outcome a)) -
            ev ψ
              (leftTensor (ι₂ := ι) (A.outcome a) *
                leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) (A.outcome a))) := by
            rw [← Finset.sum_sub_distrib]
      _ = ∑ a : Outcome,
            ev ψ
              (leftTensor (ι₂ := ι) (A.outcome a) *
                (LB *
                  (leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [(ev_sub ψ
                (leftTensor (ι₂ := ι) (A.outcome a) *
                  leftTensor (ι₂ := ι) B *
                  leftTensor (ι₂ := ι) (A.outcome a))
                (leftTensor (ι₂ := ι) (A.outcome a) *
                  leftTensor (ι₂ := ι) B *
                  rightTensor (ι₁ := ι) (A.outcome a))).symm]
            simp [LB, mul_assoc, mul_sub]
  calc
    |(∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            leftTensor (ι₂ := ι) (A.outcome a))) -
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a))|
      = |∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              (LB *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a))))| := by
            rw [hrewrite]
    _ ≤ Real.sqrt
          (∑ a : Outcome,
            ev ψ
              (((leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a))ᴴ) *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a)))) := haux'
    _ = Real.sqrt (qSDD ψ A.toSubMeas.liftLeft A.toSubMeas.liftRight) := by
          simp [qSDD, qSDDCore, SubMeas.liftLeft, SubMeas.liftRight]
end MIPStarRE.LDT.Preliminaries
