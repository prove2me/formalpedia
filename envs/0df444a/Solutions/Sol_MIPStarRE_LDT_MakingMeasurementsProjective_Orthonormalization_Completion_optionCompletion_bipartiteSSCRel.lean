-- Prove2me | solution 1 for MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization.Completion.optionCompletion_bipartiteSSCRel
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:45:22.707838+00:00
-- url     : https://prove2.me/submissions/d81f61f3-5ba6-4ec1-9911-0ecb25a21e4a

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization/Completion.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/FiniteMatrix/Basic.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization/Completion.lean (solution of MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization.Completion.optionCompletion_bipartiteSSCRel);
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
import Mathlib.Algebra.Module.NatInt
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
import Mathlib.Data.Finite.Prod
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
import Mathlib.Tactic.Attr.Register
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ConsistencyBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_RestrictSome
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_qBipartiteSSCDefect_postprocess_le
import Theorems.Thm_MIPStarRE_LDT_bipartiteSSCError_nonneg
import Theorems.Thm_MIPStarRE_LDT_ev_sub
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_leftTensor
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_rightTensor_eq_opTensor
import Theorems.Thm_MIPStarRE_LDT_leftTensor_one
import Theorems.Thm_MIPStarRE_LDT_opTensor_sub_left
import Theorems.Thm_MIPStarRE_LDT_rightTensor_mul_leftTensor_eq_opTensor
import Theorems.Thm_MIPStarRE_LDT_rightTensor_mul_rightTensor
import Theorems.Thm_MIPStarRE_LDT_rightTensor_one

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.Quantum
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp
set_option backward.isDefEq.respectTransparency false
/-- Kronecker product is additive in the right factor, rewritten for subtraction. -/
theorem kronecker_sub_right
    {d₁ d₂ : Type*} {A : Op d₁} {B₁ B₂ : Op d₂} :
    Matrix.kronecker A B₁ - Matrix.kronecker A B₂ =
      Matrix.kronecker A (B₁ - B₂) := by
  have hneg : Matrix.kronecker A (-B₂) = -Matrix.kronecker A B₂ := by
    simpa using (Matrix.kronecker_smul (-1 : ℂ) A B₂)
  calc
    Matrix.kronecker A B₁ - Matrix.kronecker A B₂
        = Matrix.kronecker A B₁ + Matrix.kronecker A (-B₂) := by
            rw [hneg]
            simp [sub_eq_add_neg]
    _ = Matrix.kronecker A (B₁ - B₂) := by
          simpa [sub_eq_add_neg] using (Matrix.kronecker_add A B₁ (-B₂)).symm
end
end MIPStarRE.Quantum

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization.Completion
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ) (hψ : ψ.IsNormalized)
    (A : SubMeas Outcome ι) (ζ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A) ζ →
      BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily (optionCompletion A).toSubMeas)
        (2 * ζ) := by
  intro hssc
  let R : MIPStarRE.Quantum.Op ι := 1 - A.total
  have hζ_nonneg : 0 ≤ ζ :=
    le_trans
      (bipartiteSSCError_nonneg ψ (uniformDistribution Unit)
        (constSubMeasFamily A))
      hssc.overlapBound
  have horig_q : qBipartiteSSCDefect ψ A ≤ ζ := by
    simpa [MIPStarRE.LDT.avgOver, MIPStarRE.LDT.uniformDistribution, MIPStarRE.LDT.constSubMeasFamily, MIPStarRE.LDT.sddError, MIPStarRE.LDT.sddErrorOp, MIPStarRE.LDT.bipartiteConsError, MIPStarRE.LDT.bipartiteSSCError, MIPStarRE.LDT.IdxMeas.toIdxSubMeas, MIPStarRE.LDT.IdxSubMeas.liftLeft, MIPStarRE.LDT.IdxSubMeas.liftRight, MIPStarRE.LDT.SubMeas.liftLeft, MIPStarRE.LDT.SubMeas.liftRight, MIPStarRE.LDT.ProjSubMeas.liftLeft, MIPStarRE.LDT.leftTensor_mul_leftTensor, MIPStarRE.LDT.rightTensor_mul_rightTensor, MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor, MIPStarRE.LDT.rightTensor_mul_leftTensor_eq_opTensor, MIPStarRE.LDT.leftTensor_conjTranspose, MIPStarRE.LDT.rightTensor_conjTranspose, MIPStarRE.LDT.leftTensor_one, MIPStarRE.LDT.rightTensor_one] using hssc.overlapBound
  have horig_gap :
      ev ψ (leftTensor (ι₂ := ι) A.total) - qBipartiteMatchMass ψ A A ≤ ζ :=
    le_trans (le_max_right 0 _) horig_q
  have htotal_q :
      qBipartiteSSCDefect ψ (postprocess A (fun _ : Outcome => ())) ≤ ζ :=
    le_trans
      (MIPStarRE.LDT.Preliminaries.qBipartiteSSCDefect_postprocess_le
        (ψ := ψ) (M := A) (f := fun _ : Outcome => ()))
      horig_q
  have htotal_gap :
      ev ψ (leftTensor (ι₂ := ι) A.total) - ev ψ (opTensor A.total A.total) ≤ ζ :=
    le_trans (le_max_right 0 _) <| by
      simpa [qBipartiteSSCDefect, postprocess, A.sum_eq_total] using htotal_q
  have hresidual_eq :
      ev ψ (leftTensor (ι₂ := ι) R) - ev ψ (opTensor R R) =
        ev ψ (rightTensor (ι₁ := ι) A.total) - ev ψ (opTensor A.total A.total) := by
    have hop :
        leftTensor (ι₂ := ι) R - opTensor R R =
          rightTensor (ι₁ := ι) A.total - opTensor A.total A.total := by
      calc
        leftTensor (ι₂ := ι) R - opTensor R R
            = opTensor R (1 : MIPStarRE.Quantum.Op ι) - opTensor R R := by
                try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
        _ = opTensor R ((1 : MIPStarRE.Quantum.Op ι) - R) := by
                simpa [opTensor] using
                  (MIPStarRE.Quantum.kronecker_sub_right (A := R)
                    (B₁ := (1 : MIPStarRE.Quantum.Op ι)) (B₂ := R))
        _ = opTensor R A.total := by
                simp [R]
        _ = opTensor (1 : MIPStarRE.Quantum.Op ι) A.total - opTensor A.total A.total := by
                simpa [R] using
                  (opTensor_sub_left (A := (1 : MIPStarRE.Quantum.Op ι))
                    (B := A.total) (C := A.total)).symm
        _ = rightTensor (ι₁ := ι) A.total - opTensor A.total A.total := by
                try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    simpa [ev_sub] using congrArg (ev ψ) hop
  have hresidual_gap :
      ev ψ (leftTensor (ι₂ := ι) R) - ev ψ (opTensor R R) ≤ ζ := by
    rw [hresidual_eq, ← hperm.swap_ev A.total]
    exact htotal_gap
  have hleftR :
      ev ψ (leftTensor (ι₂ := ι) R) = 1 - ev ψ (leftTensor (ι₂ := ι) A.total) := by
    have hleftSub' :
        1 - leftTensor (ι₂ := ι) A.total = leftTensor (ι₂ := ι) R := by
      calc
        1 - leftTensor (ι₂ := ι) A.total
            = leftTensor (ι₂ := ι) (1 : MIPStarRE.Quantum.Op ι) -
                leftTensor (ι₂ := ι) A.total := by
                  rw [leftTensor_one (ι₁ := ι) (ι₂ := ι)]
        _ = leftTensor (ι₂ := ι) R := by
              change opTensor (1 : MIPStarRE.Quantum.Op ι) (1 : MIPStarRE.Quantum.Op ι) -
                  opTensor A.total (1 : MIPStarRE.Quantum.Op ι) =
                opTensor R (1 : MIPStarRE.Quantum.Op ι)
              simpa [R] using
                (opTensor_sub_left (A := (1 : MIPStarRE.Quantum.Op ι))
                  (B := A.total) (C := (1 : MIPStarRE.Quantum.Op ι)))
    rw [← hleftSub', ev_sub]
    simp [ev_one_of_isNormalized ψ hψ]
  have hcompleted_gap :
      1 - (qBipartiteMatchMass ψ A A + ev ψ (opTensor R R)) ≤ 2 * ζ := by
    linarith [horig_gap, hresidual_gap, hleftR]
  have hoverlap_completion :
      ∑ oa : Option Outcome,
          ev ψ
            (opTensor
              ((optionCompletion A).outcome oa)
              ((optionCompletion A).outcome oa)) =
        ev ψ (opTensor R R) + qBipartiteMatchMass ψ A A := by
    rw [Fintype.sum_option]
    simp [qBipartiteMatchMass, R]
  have hcompleted_q :
      qBipartiteSSCDefect ψ (optionCompletion A).toSubMeas ≤ 2 * ζ := by
    unfold qBipartiteSSCDefect
    dsimp
    have hmass_completion :
        ev ψ (leftTensor (ι₂ := ι) (optionCompletion A).toSubMeas.total) = 1 := by
      calc
        ev ψ (leftTensor (ι₂ := ι) (optionCompletion A).toSubMeas.total)
            = ev ψ (leftTensor (ι₂ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
                rw [(optionCompletion A).total_eq_one]
        _ = ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
                simpa using
                  congrArg (ev ψ) (leftTensor_one (ι₁ := ι) (ι₂ := ι))
        _ = 1 := ev_one_of_isNormalized ψ hψ
    rw [hmass_completion, hoverlap_completion]
    refine max_le_iff.mpr ?_
    constructor
    · nlinarith
    · simpa [add_comm, add_left_comm, add_assoc] using hcompleted_gap
  constructor
  simpa [bipartiteSSCError, avgOver, uniformDistribution, constSubMeasFamily]
    using hcompleted_q
end MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization.Completion
