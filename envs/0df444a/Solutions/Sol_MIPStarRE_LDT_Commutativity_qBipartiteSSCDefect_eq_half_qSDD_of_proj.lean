-- Prove2me | solution 1 for MIPStarRE.LDT.Commutativity.qBipartiteSSCDefect_eq_half_qSDD_of_proj
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:40:47.427492+00:00
-- url     : https://prove2.me/submissions/c8351734-2002-450b-b65f-107b8ee10820

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Commutativity/ScalarApproximation/Core.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/ScalarApproximation/Core.lean (solution of MIPStarRE.LDT.Commutativity.qBipartiteSSCDefect_eq_half_qSDD_of_proj);
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Theorems.Thm_MIPStarRE_LDT_SubMeas_outcome_le_one
import Theorems.Thm_MIPStarRE_LDT_ev_add
import Theorems.Thm_MIPStarRE_LDT_ev_mono
import Theorems.Thm_MIPStarRE_LDT_ev_scale
import Theorems.Thm_MIPStarRE_LDT_ev_sub
import Theorems.Thm_MIPStarRE_LDT_ev_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_leftTensor
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_rightTensor_eq_opTensor
import Theorems.Thm_MIPStarRE_LDT_leftTensor_nonneg
import Theorems.Thm_MIPStarRE_LDT_rightTensor_mul_rightTensor
import Theorems.Thm_MIPStarRE_LDT_rightTensor_nonneg

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
    {α : Type*} [Fintype α]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (P : ProjSubMeas α ι) :
    qBipartiteSSCDefect ψ P.toSubMeas =
      (1 / 2 : Error) * qSDD ψ P.toSubMeas.liftLeft P.toSubMeas.liftRight := by
  have hgap_nonneg :
      0 ≤
        ev ψ (leftTensor (ι₂ := ι) P.toSubMeas.total) -
          ∑ a : α, ev ψ (opTensor (P.outcome a) (P.outcome a)) := by
    have hterm :
        ∀ a : α,
          ev ψ (opTensor (P.outcome a) (P.outcome a)) ≤
            ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) := by
      intro a
      have hop_le :
          opTensor (P.outcome a) (P.outcome a) ≤
            leftTensor (ι₂ := ι) (P.outcome a) := by
        have hrewrite :
            leftTensor (ι₂ := ι) (P.outcome a) -
                opTensor (P.outcome a) (P.outcome a) =
              opTensor (P.outcome a) (1 - P.outcome a) := by
          have hneg :
              Matrix.kronecker (P.outcome a) (-P.outcome a) =
                -Matrix.kronecker (P.outcome a) (P.outcome a) := by
            simpa using
              (Matrix.kronecker_smul (-1 : ℂ) (P.outcome a) (P.outcome a))
          calc
            leftTensor (ι₂ := ι) (P.outcome a) -
                opTensor (P.outcome a) (P.outcome a)
              = Matrix.kronecker (P.outcome a) 1 +
                  Matrix.kronecker (P.outcome a) (-P.outcome a) := by
                    rw [hneg]
                    simp [leftTensor, opTensor, sub_eq_add_neg]
            _ = Matrix.kronecker (P.outcome a) (1 - P.outcome a) := by
                  simpa [sub_eq_add_neg] using
                    (Matrix.kronecker_add (P.outcome a) 1 (-P.outcome a)).symm
            _ = opTensor (P.outcome a) (1 - P.outcome a) := by
                  simp [opTensor]
        change
          (leftTensor (ι₂ := ι) (P.outcome a) -
              opTensor (P.outcome a) (P.outcome a)).PosSemidef
        rw [hrewrite]
        change Matrix.PosSemidef (Matrix.kronecker (P.outcome a) (1 - P.outcome a))
        exact
          Matrix.PosSemidef.kronecker
            (Matrix.nonneg_iff_posSemidef.mp (P.outcome_pos a))
            (Matrix.nonneg_iff_posSemidef.mp
              (sub_nonneg.mpr (P.toSubMeas.outcome_le_one a)))
      exact ev_mono ψ _ _ hop_le
    have hsum :
        ∑ a : α, ev ψ (opTensor (P.outcome a) (P.outcome a)) ≤
          ∑ a : α, ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) := by
      exact Finset.sum_le_sum fun a _ => hterm a
    have htotal :
        ∑ a : α, ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) =
          ev ψ (leftTensor (ι₂ := ι) P.toSubMeas.total) := by
      rw [← ev_sum ψ (fun a : α => leftTensor (ι₂ := ι) (P.outcome a))]
      simp [leftTensor_finset_sum, P.toSubMeas.sum_eq_total]
    linarith
  have hq :
      qSDD ψ P.toSubMeas.liftLeft P.toSubMeas.liftRight =
        2 *
          (ev ψ (leftTensor (ι₂ := ι) P.toSubMeas.total) -
            ∑ a : α, ev ψ (opTensor (P.outcome a) (P.outcome a))) := by
    unfold qSDD qSDDCore
    calc
      ∑ a : α,
          ev ψ
            (((P.toSubMeas.liftLeft.outcome a - P.toSubMeas.liftRight.outcome a)ᴴ) *
              (P.toSubMeas.liftLeft.outcome a - P.toSubMeas.liftRight.outcome a))
        =
          ∑ a : α,
            (ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) +
              ev ψ (rightTensor (ι₁ := ι) (P.outcome a)) -
              2 * ev ψ (opTensor (P.outcome a) (P.outcome a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            let LA : MIPStarRE.Quantum.Op (ι × ι) :=
              leftTensor (ι₂ := ι) (P.outcome a)
            let RA : MIPStarRE.Quantum.Op (ι × ι) :=
              rightTensor (ι₁ := ι) (P.outcome a)
            have hLA_herm : LAᴴ = LA := by
              exact
                (Matrix.nonneg_iff_posSemidef.mp
                  (leftTensor_nonneg (ι₂ := ι) (P.outcome_pos a))).isHermitian.eq
            have hRA_herm : RAᴴ = RA := by
              exact
                (Matrix.nonneg_iff_posSemidef.mp
                  (rightTensor_nonneg (ι₁ := ι) (P.outcome_pos a))).isHermitian.eq
            have hLA_proj : LA * LA = LA := by
              calc
                LA * LA
                  = leftTensor (ι₂ := ι) (P.outcome a * P.outcome a) := by
                      dsimp [LA]
                      simp [leftTensor_mul_leftTensor]
                _ = LA := by
                      rw [P.proj a]
            have hRA_proj : RA * RA = RA := by
              calc
                RA * RA
                  = rightTensor (ι₁ := ι) (P.outcome a * P.outcome a) := by
                      dsimp [RA]
                      simp [rightTensor_mul_rightTensor]
                _ = RA := by
                      rw [P.proj a]
            have hcomm :
                LA * RA = RA * LA := by
              calc
                LA * RA
                  = opTensor (P.outcome a) (P.outcome a) := by
                      dsimp [LA, RA]
                      rw [leftTensor_mul_rightTensor_eq_opTensor]
                _ = RA * LA := by
                      dsimp [RA, LA]
                      simpa [rightTensor, leftTensor, opTensor] using
                        (Matrix.mul_kronecker_mul
                          (1 : MIPStarRE.Quantum.Op ι) (P.outcome a)
                          (P.outcome a) (1 : MIPStarRE.Quantum.Op ι))
            have hmul :
                (LA - RA) * (LA - RA) = LA * LA - LA * RA - RA * LA + RA * RA := by
              noncomm_ring
            calc
              ev ψ (((LA - RA)ᴴ) * (LA - RA))
                = ev ψ (LA + RA - (2 : Error) • (LA * RA)) := by
                    rw [show (LA - RA)ᴴ = LA - RA by simp [hLA_herm, hRA_herm]]
                    rw [hmul, hLA_proj, hRA_proj, hcomm]
                    simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
              _ = ev ψ LA + ev ψ RA - 2 * ev ψ (LA * RA) := by
                    rw [ev_sub, ev_add]
                    have hscale : ev ψ ((2 : Error) • (LA * RA)) = 2 * ev ψ (LA * RA) := by
                      exact ev_scale ψ (2 : Error) (LA * RA)
                    rw [hscale]
              _ = ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) +
                    ev ψ (rightTensor (ι₁ := ι) (P.outcome a)) -
                    2 * ev ψ (opTensor (P.outcome a) (P.outcome a)) := by
                      dsimp [LA, RA]
                      rw [leftTensor_mul_rightTensor_eq_opTensor]
      _ =
          ∑ a : α,
            2 *
              (ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) -
                ev ψ (opTensor (P.outcome a) (P.outcome a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hperm.swap_ev (P.outcome a)]
            ring
      _ = 2 *
          ∑ a : α,
            (ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) -
              ev ψ (opTensor (P.outcome a) (P.outcome a))) := by
            rw [← Finset.mul_sum]
      _ = 2 *
          (ev ψ (leftTensor (ι₂ := ι) P.toSubMeas.total) -
            ∑ a : α, ev ψ (opTensor (P.outcome a) (P.outcome a))) := by
            congr 1
            rw [Finset.sum_sub_distrib]
            rw [← ev_sum ψ (fun a : α => leftTensor (ι₂ := ι) (P.outcome a))]
            simp [leftTensor_finset_sum, P.toSubMeas.sum_eq_total]
  calc
    qBipartiteSSCDefect ψ P.toSubMeas
      = ev ψ (leftTensor (ι₂ := ι) P.toSubMeas.total) -
          ∑ a : α, ev ψ (opTensor (P.outcome a) (P.outcome a)) := by
            rw [qBipartiteSSCDefect, max_eq_right hgap_nonneg]
    _ = (1 / 2 : Error) * qSDD ψ P.toSubMeas.liftLeft P.toSubMeas.liftRight := by
          rw [hq]
          ring
end MIPStarRE.LDT.Commutativity
