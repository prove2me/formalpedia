-- Prove2me | solution 1 for MIPStarRE.LDT.MakingMeasurementsProjective.qCompleteness
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:31:35.955307+00:00
-- url     : https://prove2.me/submissions/381f36b7-0033-4986-86d3-27c902b17240

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/QCompleteness.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/QCompleteness.lean (solution of MIPStarRE.LDT.MakingMeasurementsProjective.qCompleteness);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
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
import Mathlib.Algebra.Group.Idempotent
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
import Mathlib.Algebra.Order.Group.Abs
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
import Mathlib.Algebra.Ring.CompTypeclasses
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
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
import Mathlib.Analysis.Real.Spectrum
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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
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
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Star
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
import Mathlib.Data.Sigma.Basic
import Mathlib.Data.ULift
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
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Basic
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Hom.Basic
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
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.RealSqrt
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
import Mathlib.Topology.ContinuousOn
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_ProjectorONB
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_QCompleteness
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_spectralTruncationError_nonneg
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_zetaQuarterRoot_nonneg
import Theorems.Thm_MIPStarRE_LDT_Measurement_outcome_hermitian
import Theorems.Thm_MIPStarRE_LDT_Measurement_sum_eq
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_subMeas_diagMass_le_one
import Theorems.Thm_MIPStarRE_LDT_ev_abs_mul_le_sqrt
import Theorems.Thm_MIPStarRE_LDT_ev_adjoint_self_nonneg
import Theorems.Thm_MIPStarRE_LDT_ev_mul_comm_of_psd
import Theorems.Thm_MIPStarRE_LDT_ev_sub
import Theorems.Thm_MIPStarRE_LDT_ev_sum

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QLayerData Outcome ι)
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ)
    (hζ_small : ζ ≤ 1 / (4 : Error)) :
    RankReductionWitness ψ A ζ data →
      ev ψ (QTotal data) ≥ 1 - 11 * zetaQuarterRoot ζ := by
  intro hRank
  let diagA : Error := ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
  let qMass : Error := ev ψ (QTotal data)
  let overlap : Error := ∑ a : Outcome, ev ψ (A.outcome a * Qa data a)
  have hsdd :
      qSDDOp ψ (A.toSubMeas : OpFamily Outcome ι) data.q ≤
        roundingToProjectiveError ζ := by
    simpa [SDDOpRel, sddErrorOp, avgOver, uniformDistribution, constOpFamily, qSDDOp]
      using hRank.closeness.squaredDistanceBound
  have hdiagA_nonneg : 0 ≤ diagA := by
    unfold diagA
    exact Finset.sum_nonneg fun a _ => by
      simpa [Measurement.outcome_hermitian] using ev_adjoint_self_nonneg ψ (A.outcome a)
  have hdiagA_le_one : diagA ≤ 1 := by
    simpa [diagA] using
      MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_one ψ hψ A.toSubMeas
  have hsqrt_diagA_le_one : Real.sqrt diagA ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiagA_le_one
  have hdiagA_lb : 1 - 2 * ζ ≤ diagA := by
    have hsource := hRank.source_almost_projective
    have hsum :
        ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) = 1 - diagA := by
      calc
        ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a)
            = ∑ a, (ev ψ (A.outcome a) - ev ψ (A.outcome a * A.outcome a)) := by
                refine Finset.sum_congr rfl ?_
                intro a _
                exact ev_sub ψ (A.outcome a) (A.outcome a * A.outcome a)
        _ = (∑ a, ev ψ (A.outcome a)) - ∑ a, ev ψ (A.outcome a * A.outcome a) := by
              rw [Finset.sum_sub_distrib]
        _ = 1 - diagA := by
              rw [← ev_sum ψ A.outcome, A.sum_eq]
              simp [diagA, ev_one_of_isNormalized ψ hψ]
    linarith [hsource, hsum]
  have hqtotal_nonneg : 0 ≤ QTotal data := by
    rw [← hRank.sum_eq_total]
    exact Finset.sum_nonneg fun a _ => hRank.outcome_nonneg a
  have hq_nonneg : 0 ≤ qMass := by
    exact ev_nonneg_of_psd ψ (QTotal data) hqtotal_nonneg
  have hdiagQ_eq :
      ∑ a : Outcome, ev ψ (Qa data a * Qa data a) = qMass := by
    calc
      ∑ a : Outcome, ev ψ (Qa data a * Qa data a)
          = ∑ a : Outcome, ev ψ (Qa data a) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [(hRank.projective a).isIdempotentElem.eq]
      _ = ev ψ (QTotal data) := by
            rw [← ev_sum ψ (Qa data), hRank.sum_eq_total]
  have hoverlap_le : overlap ≤ Real.sqrt diagA * Real.sqrt qMass := by
    have hoverlap_abs :
        |overlap| ≤ Real.sqrt diagA * Real.sqrt qMass := by
      calc
        |overlap|
            = |∑ a : Outcome, ev ψ (A.outcome a * Qa data a)| := by
                simp [overlap]
        _ ≤ ∑ a : Outcome, |ev ψ (A.outcome a * Qa data a)| := by
              exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a : Outcome,
              Real.sqrt (ev ψ (A.outcome a * A.outcome a)) *
                Real.sqrt (ev ψ (Qa data a * Qa data a)) := by
              refine Finset.sum_le_sum ?_
              intro a _
              simpa [Measurement.outcome_hermitian,
                (hRank.projective a).isSelfAdjoint.isHermitian.eq] using
                ev_abs_mul_le_sqrt ψ (A.outcome a) (Qa data a)
        _ ≤ Real.sqrt diagA *
              Real.sqrt (∑ a : Outcome, ev ψ (Qa data a * Qa data a)) := by
              simpa [diagA] using
                Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
                  (f := fun a => ev ψ (A.outcome a * A.outcome a))
                  (g := fun a => ev ψ (Qa data a * Qa data a))
                  (fun a => by
                    simpa [Measurement.outcome_hermitian] using
                      ev_adjoint_self_nonneg ψ (A.outcome a))
                  (fun a => by
                    simpa [(hRank.projective a).isSelfAdjoint.isHermitian.eq] using
                      ev_adjoint_self_nonneg ψ (Qa data a))
        _ = Real.sqrt diagA * Real.sqrt qMass := by rw [hdiagQ_eq]
    exact (abs_le.mp hoverlap_abs).2
  have h_expand :
      qSDDOp ψ (A.toSubMeas : OpFamily Outcome ι) data.q =
        diagA + qMass - 2 * overlap := by
    unfold qSDDOp qSDDCore
    calc
      ∑ a, ev ψ ((A.outcome a - Qa data a)ᴴ * (A.outcome a - Qa data a))
        = ∑ a, (ev ψ (A.outcome a * A.outcome a) +
            ev ψ (Qa data a * Qa data a) -
            2 * ev ψ (A.outcome a * Qa data a)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              have hcomm :
                  ev ψ (Qa data a * A.outcome a) =
                    ev ψ (A.outcome a * Qa data a) := by
                exact ev_mul_comm_of_psd ψ _ _ (hRank.outcome_nonneg a) (A.outcome_pos a)
              calc
                ev ψ ((A.outcome a - Qa data a)ᴴ * (A.outcome a - Qa data a))
                    = ev ψ ((A.outcome a * A.outcome a -
                        A.outcome a * Qa data a) -
                        (Qa data a * A.outcome a -
                          Qa data a * Qa data a)) := by
                          congr 1
                          simp [sub_mul, mul_sub, Measurement.outcome_hermitian,
                            (hRank.projective a).isSelfAdjoint.isHermitian.eq]
                          abel
                _ = ev ψ (A.outcome a * A.outcome a) -
                      ev ψ (A.outcome a * Qa data a) -
                      (ev ψ (Qa data a * A.outcome a) -
                        ev ψ (Qa data a * Qa data a)) := by
                        rw [ev_sub, ev_sub, ev_sub]
                _ = ev ψ (A.outcome a * A.outcome a) +
                      ev ψ (Qa data a * Qa data a) -
                      2 * ev ψ (A.outcome a * Qa data a) := by
                        rw [hcomm]
                        ring
      _ = (∑ a, ev ψ (A.outcome a * A.outcome a)) +
            (∑ a, ev ψ (Qa data a * Qa data a)) -
            2 * ∑ a, ev ψ (A.outcome a * Qa data a) := by
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      _ = diagA + qMass - 2 * overlap := by
            simp [diagA, overlap, hdiagQ_eq]
  have hsq_gap :
      (Real.sqrt qMass - Real.sqrt diagA) ^ (2 : Nat) ≤
        roundingToProjectiveError ζ := by
    calc
      (Real.sqrt qMass - Real.sqrt diagA) ^ (2 : Nat)
          = qMass + diagA - 2 * (Real.sqrt diagA * Real.sqrt qMass) := by
              nlinarith [Real.sq_sqrt hq_nonneg, Real.sq_sqrt hdiagA_nonneg]
      _ ≤ qMass + diagA - 2 * overlap := by
            nlinarith [hoverlap_le]
      _ = qSDDOp ψ (A.toSubMeas : OpFamily Outcome ι) data.q := by
            rw [h_expand]
            ring
      _ ≤ roundingToProjectiveError ζ := hsdd
  have hround_nonneg : 0 ≤ roundingToProjectiveError ζ := by
    dsimp [roundingToProjectiveError]
    exact mul_nonneg (by norm_num) (spectralTruncationError_nonneg hζ)
  have habs :
      |Real.sqrt qMass - Real.sqrt diagA| ≤ Real.sqrt (roundingToProjectiveError ζ) := by
    refine abs_le_of_sq_le_sq' ?_ (Real.sqrt_nonneg _) |>.2
    calc
      |Real.sqrt qMass - Real.sqrt diagA| ^ 2
          = (Real.sqrt qMass - Real.sqrt diagA) ^ (2 : Nat) := by
              rw [sq_abs]
      _ ≤ roundingToProjectiveError ζ := hsq_gap
      _ = (Real.sqrt (roundingToProjectiveError ζ)) ^ (2 : Nat) := by
            calc
              roundingToProjectiveError ζ
                  = Real.sqrt (roundingToProjectiveError ζ) *
                      Real.sqrt (roundingToProjectiveError ζ) := by
                        nlinarith [Real.sq_sqrt hround_nonneg]
              _ = (Real.sqrt (roundingToProjectiveError ζ)) ^ (2 : Nat) := by
                    simp [pow_two]
  have hsqrt_q_lb :
      Real.sqrt qMass ≥ Real.sqrt diagA - Real.sqrt (roundingToProjectiveError ζ) := by
    have hleft := (abs_le.mp habs).1
    linarith
  have hq_lb :
      qMass ≥ diagA - 2 * Real.sqrt (roundingToProjectiveError ζ) := by
    let s : Error := Real.sqrt (roundingToProjectiveError ζ)
    let x : Error := Real.sqrt qMass
    let y : Error := Real.sqrt diagA
    have hxy : x ≥ y - s := by
      dsimp [x, y, s]
      exact hsqrt_q_lb
    by_cases hys : y ≤ s
    · have htarget : diagA - 2 * Real.sqrt (roundingToProjectiveError ζ) ≤ 0 := by
        dsimp [y, s] at hys ⊢
        nlinarith [Real.sq_sqrt hdiagA_nonneg,
          Real.sqrt_nonneg diagA,
          Real.sqrt_nonneg (roundingToProjectiveError ζ),
          mul_nonneg (sub_nonneg.mpr hsqrt_diagA_le_one)
            (Real.sqrt_nonneg diagA)]
      linarith
    · have hs_le_y : s ≤ y := le_of_not_ge hys
      have hy_sub_nonneg : 0 ≤ y - s := by linarith
      have hx_sq_ge : x ^ (2 : Nat) ≥ (y - s) ^ (2 : Nat) := by
        nlinarith
      have hx_sq_ge' :
          qMass ≥ diagA -
            2 * Real.sqrt diagA * Real.sqrt (roundingToProjectiveError ζ) +
            roundingToProjectiveError ζ := by
        dsimp [x, y, s] at hx_sq_ge
        nlinarith [hx_sq_ge, Real.sq_sqrt hq_nonneg, Real.sq_sqrt hdiagA_nonneg,
          Real.sq_sqrt hround_nonneg]
      have hcross :
          2 * Real.sqrt diagA * Real.sqrt (roundingToProjectiveError ζ) ≤
            2 * Real.sqrt (roundingToProjectiveError ζ) := by
        have hmul :
            Real.sqrt diagA * Real.sqrt (roundingToProjectiveError ζ) ≤
              1 * Real.sqrt (roundingToProjectiveError ζ) := by
          exact mul_le_mul_of_nonneg_right hsqrt_diagA_le_one (Real.sqrt_nonneg _)
        nlinarith
      linarith [hx_sq_ge', hcross, hround_nonneg]
  have hzeta_term :
      2 * ζ ≤ 2 * zetaQuarterRoot ζ := by
    gcongr
    have hζ1 : ζ ≤ 1 := by linarith
    dsimp [zetaQuarterRoot]
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' hζ hζ1 (by positivity)
        (by norm_num : (1 : Error) ≥ 1 / 4))
  have hround_term :
      2 * Real.sqrt (roundingToProjectiveError ζ) ≤ 8 * zetaQuarterRoot ζ := by
    have hsqrt_rpow :
        Real.sqrt (ζ ^ (1 / (2 : Error))) = zetaQuarterRoot ζ := by
      rw [Real.sqrt_eq_rpow, zetaQuarterRoot, ← Real.rpow_mul hζ]
      congr 1
      ring
    have hsqrt_eq :
        Real.sqrt (roundingToProjectiveError ζ) =
          Real.sqrt (12 : Error) * zetaQuarterRoot ζ := by
      dsimp [roundingToProjectiveError, spectralTruncationError]
      rw [Real.sqrt_mul (by positivity), hsqrt_rpow]
    have hzqr_nonneg : 0 ≤ zetaQuarterRoot ζ := zetaQuarterRoot_nonneg hζ
    have hsqrt : Real.sqrt (12 : Error) ≤ 4 := by
      have hsq : (Real.sqrt (12 : Error)) ^ 2 ≤ (4 : Error) ^ 2 := by norm_num
      nlinarith [Real.sq_sqrt (show 0 ≤ (12 : Error) by positivity), hsq]
    have hsqrt_bound : Real.sqrt (roundingToProjectiveError ζ) ≤ 4 * zetaQuarterRoot ζ := by
      rw [hsqrt_eq]
      exact mul_le_mul_of_nonneg_right hsqrt hzqr_nonneg
    nlinarith
  calc
    ev ψ (QTotal data) = qMass := rfl
    _ ≥ diagA - 2 * Real.sqrt (roundingToProjectiveError ζ) := hq_lb
    _ ≥ (1 - 2 * ζ) - 2 * Real.sqrt (roundingToProjectiveError ζ) := by
          gcongr
    _ ≥ (1 - 2 * zetaQuarterRoot ζ) - 8 * zetaQuarterRoot ζ := by
          linarith
    _ = 1 - 10 * zetaQuarterRoot ζ := by ring
    _ ≥ 1 - 11 * zetaQuarterRoot ζ := by
          have hzqr_nonneg : 0 ≤ zetaQuarterRoot ζ := by
            dsimp [zetaQuarterRoot]
            exact Real.rpow_nonneg hζ _
          linarith
end MIPStarRE.LDT.MakingMeasurementsProjective
