-- Prove2me | solution 1 for OAI.KadisonKastler.constructedCore_equiv_of_statePreserving
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T09:00:38.943202+00:00
-- url     : https://prove2.me/submissions/bfbd2b42-83e5-40b8-b6fd-bcfc96f12021

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K037
import Theorems.Thm_OAI_KadisonKastler_statePreservingUnitary_resolvent

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularSpatialTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial transport of the constructed modular group

Intertwining the bounded graph resolvent suffices: its continuous phase
approximations intertwine, and so do their strong limits.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (J : H ≃ₗᵢ⋆[ℂ] H) (L : K ≃ₗᵢ⋆[ℂ] K) (Ω : H) (ξ : K)
  (hMsep : Function.Injective (algebraVectorMap M Ω))
  (hMcyc : DenseRange (algebraVectorMap M Ω))
  (hNsep : Function.Injective (algebraVectorMap N ξ))
  (hNcyc : DenseRange (algebraVectorMap N ξ))
  (V : H ≃ₗᵢ[ℂ] K)
  (hR : V.conjStarAlgEquiv (graphResolvent M J Ω 1) = graphResolvent N L ξ 1)

omit [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace K] in
include hR in
theorem modularApproximation_spatial (n : ℕ) (t : ℝ) (x : H) :
    V (modularApproximation M J Ω n t x) = modularApproximation N L ξ n t (V x) := by
  have he : V.conjStarAlgEquiv (modularApproximation M J Ω n t) =
      modularApproximation N L ξ n t := by
    change V.conjStarAlgEquiv
      (regularizedModularGroup M J Ω (modularRegularizationScale n)
        (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (regularizedModularGroup N L ξ (modularRegularizationScale n)
        (Multiplicative.ofAdd t) : K →L[ℂ] K)
    rw [regularizedModularGroup_eq_cfc J Ω t (modularRegularizationScale_pos n),
      regularizedModularGroup_eq_cfc L ξ t (modularRegularizationScale_pos n)]
    have hc := StarAlgHomClass.map_cfc V.conjStarAlgEquiv
      (modularPhaseScalar t (modularRegularizationScale n)) (graphResolvent M J Ω 1)
      (modularPhaseScalar_continuousOn J Ω t (modularRegularizationScale_pos n))
      (by fun_prop) (graphResolvent_positive J Ω 1).isSelfAdjoint.isStarNormal
      (by rw [hR]; exact (graphResolvent_positive L ξ 1).isSelfAdjoint.isStarNormal)
    rw [hR] at hc
    exact hc
  have hx := congrArg (fun A : K →L[ℂ] K => A (V x)) he
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply] using hx

include hR in
theorem modularStrongGroup_spatial (t : Multiplicative ℝ) (x : H) :
    V ((modularStrongGroup J Ω hMsep hMcyc t : H →L[ℂ] H) x) =
      (modularStrongGroup L ξ hNsep hNcyc t : K →L[ℂ] K) (V x) := by
  have hh := V.continuous.continuousAt.tendsto.comp
    (modularApproximation_tendsto J Ω hMsep hMcyc t.toAdd x)
  have hk := modularApproximation_tendsto L ξ hNsep hNcyc t.toAdd (V x)
  have he (n : ℕ) := modularApproximation_spatial J L Ω ξ V hR n t.toAdd x
  change Tendsto (fun n => V (modularApproximation M J Ω n t.toAdd x)) atTop
    (𝓝 (V (modularStrongLimit J Ω hMsep hMcyc t.toAdd x))) at hh
  simp_rw [he] at hh
  exact tendsto_nhds_unique hh hk

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointwiseL2Spatial
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Pointwise spatial identifications on the regular Hilbert space -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
theorem pointwiseL2Unitary_apply_ae (V : H ≃ₗᵢ[ℂ] K) (f : RegularCoreHilbert H) :
    pointwiseL2Unitary V f =ᵐ[volume] fun t => V (f t) :=
  V.toLinearIsometry.toContinuousLinearMap.coeFn_compLp f

theorem compLp_regularRightTranslation (L : H →L[ℂ] K)
    (s : Multiplicative ℝ) (f : RegularCoreHilbert H) :
    L.compLp ((regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) =
    (regularRightTranslation (H := K) s :
      RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K) (L.compLp f) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp ((regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularRightTranslation_apply_ae s f,
    regularRightTranslation_apply_ae s (L.compLp f),
    (measurePreserving_add_right volume s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (L.coeFn_compLp f)] with t hl hs ht hf
  simp only [Function.comp_def] at hf
  rw [hl, hs, ht, hf]

theorem pointwiseL2Unitary_translation (V : H ≃ₗᵢ[ℂ] K) (s : Multiplicative ℝ) :
    (pointwiseL2Unitary V).conjStarAlgEquiv
      (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (regularRightTranslation (H := K) s :
        RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  change V.toLinearIsometry.toContinuousLinearMap.compLp
      ((regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        ((pointwiseL2Unitary V).symm f)) = _
  rw [compLp_regularRightTranslation]
  change (regularRightTranslation (H := K) s :
    RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K)
    (pointwiseL2Unitary V ((pointwiseL2Unitary V).symm f)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreSpatialTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial transport of the concrete regular core

Intertwining the original unitary groups transports both kinds of core
generators. This result concerns the actual generated von Neumann algebras.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (V : H ≃ₗᵢ[ℂ] K)
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (W : Multiplicative ℝ →* unitary (K →L[ℂ] K))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (hW : ∀ x, Continuous (fun t : ℝ => (W (Multiplicative.ofAdd t) : K →L[ℂ] K) x))
  (hV : ∀ t x, V ((U t : H →L[ℂ] H) x) = (W t : K →L[ℂ] K) (V x))

include hV in
theorem pointwiseL2Unitary_embedding_apply (a : H →L[ℂ] H) (f : RegularCoreHilbert H) :
    pointwiseL2Unitary V (regularCoreEmbedding U hU a f) =
      regularCoreEmbedding W hW (V.conjStarAlgEquiv a) (pointwiseL2Unitary V f) := by
  apply Lp.ext
  filter_upwards [pointwiseL2Unitary_apply_ae V (regularCoreEmbedding U hU a f),
    regularCoreEmbedding_apply_ae U hU a f,
    regularCoreEmbedding_apply_ae W hW (V.conjStarAlgEquiv a) (pointwiseL2Unitary V f),
    pointwiseL2Unitary_apply_ae V f] with t hv hu hw hf
  rw [hv, hu, hw, hf]
  have hs (x : H) : V ((star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) x) =
      (star (W (Multiplicative.ofAdd t)) : K →L[ℂ] K) (V x) := by
    rw [← Unitary.coe_star, ← Unitary.coe_star,
      regularGroup_star_eq, regularGroup_star_eq]
    exact hV _ x
  rw [hs, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, ← hV,
    LinearIsometryEquiv.symm_apply_apply]

include hV in
theorem pointwiseL2Unitary_embedding (a : H →L[ℂ] H) :
    (pointwiseL2Unitary V).conjStarAlgEquiv (regularCoreEmbedding U hU a) =
      regularCoreEmbedding W hW (V.conjStarAlgEquiv a) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    pointwiseL2Unitary_embedding_apply V U W hU hW hV,
    LinearIsometryEquiv.apply_symm_apply]

include hV in
theorem regularCore_spatialTransport (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (hMN : spatialTransportAlgebra V M = N) :
    spatialTransportAlgebra (pointwiseL2Unitary V) (regularCoreAlgebra U hU M) =
      regularCoreAlgebra W hW N := by
  have hr : (pointwiseL2Unitary V).conjStarAlgEquiv '' regularCoreGenerators U hU M =
      regularCoreGenerators W hW N := by
    ext a
    constructor
    · rintro ⟨_, (⟨b, hb, rfl⟩ | ⟨s, rfl⟩), rfl⟩
      · left
        refine ⟨V.conjStarAlgEquiv b, ?_, (pointwiseL2Unitary_embedding V U W hU hW hV b).symm⟩
        rw [← hMN]
        exact ⟨b, hb, rfl⟩
      · right
        exact ⟨s, (pointwiseL2Unitary_translation V s).symm⟩
    · rintro (⟨b, hb, rfl⟩ | ⟨s, rfl⟩)
      · rw [← hMN] at hb
        rcases hb with ⟨b, hb, rfl⟩
        exact ⟨regularCoreEmbedding U hU b, Or.inl ⟨b, hb, rfl⟩,
          pointwiseL2Unitary_embedding V U W hU hW hV b⟩
      · exact ⟨_, Or.inr ⟨s, rfl⟩, pointwiseL2Unitary_translation V s⟩
  unfold regularCoreAlgebra
  rw [spatialTransport_generated, StarAlgHom.map_adjoin]
  exact congrArg (fun s => generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ s)) hr

include hV in
theorem regularCore_equiv_of_spatial (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (hMN : spatialTransportAlgebra V M = N) :
    Nonempty (Algebra (regularCoreAlgebra U hU M) ≃⋆ₐ[ℂ]
      Algebra (regularCoreAlgebra W hW N)) := by
  have e := spatialTransportEquiv (pointwiseL2Unitary V) (regularCoreAlgebra U hU M)
  rw [regularCore_spatialTransport V U W hU hW hV M N hMN] at e
  exact ⟨e⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StatePreservingSpatial
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial implementation of a vector-state preserving isomorphism

This is the representation-transport part of the modular-core isomorphism
argument. Changing the state itself still requires a separate construction.
-/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) (Ω : H) (ξ : K)
  (hM : DenseRange (algebraVectorMap M Ω))
  (hN : DenseRange (algebraVectorMap N ξ))
  (hstate : ∀ a : Algebra M, inner ℂ Ω (a.val Ω) = inner ℂ ξ ((θ a).val ξ))

theorem statePreservingUnitary_algebraVector (a : Algebra M) :
    statePreservingUnitary θ Ω ξ hM hN hstate (a.val Ω) = (θ a).val ξ :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ a

theorem statePreservingUnitary_intertwines (a : Algebra M) (x : H) :
    statePreservingUnitary θ Ω ξ hM hN hstate (a.val x) =
      (θ a).val (statePreservingUnitary θ Ω ξ hM hN hstate x) := by
  let V := statePreservingUnitary θ Ω ξ hM hN hstate
  apply hM.induction_on (p := fun x => V (a.val x) = (θ a).val (V x)) x
  · exact isClosed_eq (V.continuous.comp a.val.continuous)
      ((θ a).val.continuous.comp V.continuous)
  · intro b
    change V ((a * b).val Ω) = (θ a).val (V (b.val Ω))
    rw [statePreservingUnitary_algebraVector, statePreservingUnitary_algebraVector]
    simp only [map_mul]
    rfl

theorem statePreservingUnitary_conjugates (a : Algebra M) :
    (statePreservingUnitary θ Ω ξ hM hN hstate).conjStarAlgEquiv a.val = (θ a).val := by
  ext x
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, statePreservingUnitary_intertwines,
    LinearIsometryEquiv.apply_symm_apply]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateModularTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Modular transport under a vector-state preserving isomorphism -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) (Ω : H) (ξ : K)
  (hM : DenseRange (algebraVectorMap M Ω))
  (hN : DenseRange (algebraVectorMap N ξ))
  (hstate : ∀ a : Algebra M, inner ℂ Ω (a.val Ω) = inner ℂ ξ ((θ a).val ξ))
  (J : H ≃ₗᵢ⋆[ℂ] H) (L : K ≃ₗᵢ⋆[ℂ] K)

variable [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace K]
  (hMsep : Function.Injective (algebraVectorMap M Ω))
  (hNsep : Function.Injective (algebraVectorMap N ξ))

theorem statePreservingUnitary_modular (t : Multiplicative ℝ) (x : H) :
    statePreservingUnitary θ Ω ξ hM hN hstate
        ((modularStrongGroup J Ω hMsep hM t : H →L[ℂ] H) x) =
      (modularStrongGroup L ξ hNsep hN t : K →L[ℂ] K)
        (statePreservingUnitary θ Ω ξ hM hN hstate x) :=
  modularStrongGroup_spatial J L Ω ξ hMsep hM hNsep hN
    (statePreservingUnitary θ Ω ξ hM hN hstate)
    (statePreservingUnitary_resolvent θ Ω ξ hM hN hstate J L 1) t x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateCoreTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Cores of state-preserving cyclic representations

The modular groups give spatially isomorphic concrete cores.
-/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) (Ω : H) (ξ : K)
  (hM : DenseRange (algebraVectorMap M Ω))
  (hN : DenseRange (algebraVectorMap N ξ))
  (hstate : ∀ a : Algebra M, inner ℂ Ω (a.val Ω) = inner ℂ ξ ((θ a).val ξ))

theorem statePreservingUnitary_algebra :
    spatialTransportAlgebra (statePreservingUnitary θ Ω ξ hM hN hstate) M = N := by
  apply SetLike.coe_injective
  ext a
  change a ∈ (statePreservingUnitary θ Ω ξ hM hN hstate).conjStarAlgEquiv ''
    (M : Set (H →L[ℂ] H)) ↔ a ∈ N
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [statePreservingUnitary_conjugates θ Ω ξ hM hN hstate ⟨b, hb⟩]
    exact (θ ⟨b, hb⟩).property
  · intro ha
    obtain ⟨b, hb⟩ := θ.surjective ⟨a, ha⟩
    refine ⟨b.val, b.property, ?_⟩
    rw [statePreservingUnitary_conjugates θ Ω ξ hM hN hstate b]
    exact congrArg Subtype.val hb

variable [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace K]
  (J : H ≃ₗᵢ⋆[ℂ] H) (L : K ≃ₗᵢ⋆[ℂ] K)
  (hMsep : Function.Injective (algebraVectorMap M Ω))
  (hNsep : Function.Injective (algebraVectorMap N ξ))

include θ hstate in
theorem constructedCore_equiv_of_statePreserving_oai :
    Nonempty (Algebra (regularCoreAlgebra (modularStrongGroup J Ω hMsep hM)
      (modularStrongGroup_continuous J Ω hMsep hM) M) ≃⋆ₐ[ℂ]
      Algebra (regularCoreAlgebra (modularStrongGroup L ξ hNsep hN)
        (modularStrongGroup_continuous L ξ hNsep hN) N)) :=
  regularCore_equiv_of_spatial (statePreservingUnitary θ Ω ξ hM hN hstate)
    (modularStrongGroup J Ω hMsep hM) (modularStrongGroup L ξ hNsep hN)
    (modularStrongGroup_continuous J Ω hMsep hM)
    (modularStrongGroup_continuous L ξ hNsep hN)
    (statePreservingUnitary_modular θ Ω ξ hM hN hstate J L hMsep hNsep)
    M N (statePreservingUnitary_algebra θ Ω ξ hM hN hstate)

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.constructedCore_equiv_of_statePreserving_oai.{u_1, u_2} := @OAI.KadisonKastler.constructedCore_equiv_of_statePreserving_oai.{u_1, u_2}
