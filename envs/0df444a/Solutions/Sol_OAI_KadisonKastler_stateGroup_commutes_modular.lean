-- Prove2me | solution 1 for OAI.KadisonKastler.stateGroup_commutes_modular
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T14:28:18.669011+00:00
-- url     : https://prove2.me/submissions/db357d08-6d86-4e45-89f3-58143fb9e61f

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
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
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
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
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Prod
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
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K044
import Theorems.Thm_OAI_KadisonKastler_statePreservingUnitary_resolvent

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularSpatialTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
-- module Solutions.OAIQ075_KS.KadisonKastler_StatePreservingSpatial
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateModularTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
-- module Solutions.OAIQ075_KS.KadisonKastler_StateSymmetry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # State-preserving spatial symmetries commute with the modular group -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (Ω : H)
  (u : unitary (H →L[ℂ] H)) (hu : Conjugates u M M)
  (hfix : (u : H →L[ℂ] H) Ω = Ω)

include hfix in
theorem stateSymmetryAut_vector (a : Algebra M) :
    (stateSymmetryAut u hu a).val Ω = (u : H →L[ℂ] H) (a.val Ω) := by
  have hs : star (u : H →L[ℂ] H) Ω = Ω := by
    have hh := congrArg (fun A : H →L[ℂ] H => A Ω) (Unitary.star_mul_self_of_mem u.property)
    change star (u : H →L[ℂ] H) ((u : H →L[ℂ] H) Ω) = Ω at hh
    rwa [hfix] at hh
  change (u : H →L[ℂ] H) (a.val (star (u : H →L[ℂ] H) Ω)) = _
  rw [hs]

variable (hcyc : DenseRange (algebraVectorMap M Ω))

include hfix in
theorem stateSymmetry_spatial :
    statePreservingUnitary (stateSymmetryAut u hu) Ω Ω hcyc hcyc
      (stateSymmetryAut_state Ω u hu hfix) = Unitary.linearIsometryEquiv u := by
  apply LinearIsometryEquiv.ext
  intro x
  apply hcyc.induction_on (p := fun x =>
    statePreservingUnitary (stateSymmetryAut u hu) Ω Ω hcyc hcyc
      (stateSymmetryAut_state Ω u hu hfix) x = (u : H →L[ℂ] H) x) x
  · exact isClosed_eq (map_continuous _) u.val.continuous
  · intro a
    change statePreservingUnitary (stateSymmetryAut u hu) Ω Ω hcyc hcyc
      (stateSymmetryAut_state Ω u hu hfix) (a.val Ω) = (u : H →L[ℂ] H) (a.val Ω)
    rw [statePreservingUnitary_algebraVector, stateSymmetryAut_vector Ω u hu hfix]

variable [TopologicalSpace.SeparableSpace H]
  (hsep : Function.Injective (algebraVectorMap M Ω))

include hu hfix in
theorem stateSymmetry_modular (J : H ≃ₗᵢ⋆[ℂ] H) (t : Multiplicative ℝ) (x : H) :
    (u : H →L[ℂ] H) ((modularStrongGroup J Ω hsep hcyc t : H →L[ℂ] H) x) =
      (modularStrongGroup J Ω hsep hcyc t : H →L[ℂ] H) ((u : H →L[ℂ] H) x) := by
  have h := statePreservingUnitary_modular (stateSymmetryAut u hu) Ω Ω hcyc hcyc
    (stateSymmetryAut_state Ω u hu hfix) J J hsep hsep t x
  rw [stateSymmetry_spatial Ω u hu hfix hcyc] at h
  exact h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateSymmetryGroup
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Commutation of state-preserving groups with the canonical modular group -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (Ω : H)
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)

include hU in
theorem stateGroup_normalizes (t : Multiplicative ℝ) : Conjugates (U t) M M := by
  change unitaryConj (U t) '' (M : Set (H →L[ℂ] H)) = (M : Set (H →L[ℂ] H))
  apply Set.Subset.antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact hU t a ha
  · intro a ha
    have hi : star (U t) = U t⁻¹ := by
      change (U t)⁻¹ = U t⁻¹
      exact (map_inv U t).symm
    refine ⟨unitaryConj (star (U t)) a, ?_, ?_⟩
    · rw [hi]
      exact hU t⁻¹ a ha
    · simpa only [star_star] using unitaryConj_star_unitaryConj (star (U t)) a

variable (hfix : ∀ t, (U t : H →L[ℂ] H) Ω = Ω)
  (hcyc : DenseRange (algebraVectorMap M Ω))

variable [TopologicalSpace.SeparableSpace H]
  (hsep : Function.Injective (algebraVectorMap M Ω))

include hU hfix hcyc in
theorem stateGroup_commutes_modular_oai (J : H ≃ₗᵢ⋆[ℂ] H) (s t : Multiplicative ℝ) :
    Commute (U s : H →L[ℂ] H) (modularStrongGroup J Ω hsep hcyc t : H →L[ℂ] H) := by
  apply ContinuousLinearMap.ext
  intro x
  exact stateSymmetry_modular Ω (U s) (stateGroup_normalizes U hU s) (hfix s) hcyc hsep J t x

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.stateGroup_commutes_modular_oai.{u_1} := @OAI.KadisonKastler.stateGroup_commutes_modular_oai.{u_1}
