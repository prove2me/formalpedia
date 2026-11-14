-- Prove2me | solution 1 for OAI.KadisonKastler.TypeIIIFactor.exists_cyclic_vector_same_state
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T09:04:33.285528+00:00
-- url     : https://prove2.me/submissions/587e8007-f06a-4cbb-99f6-1e5c2278d549

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.QuadraticDiscriminant
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Cone.Closure
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
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
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
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
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
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
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K066
import Definitions.Def_Q260K034
import Theorems.Thm_OAI_KadisonKastler_cyclicOrbitProjection_not_finite
import Theorems.Thm_OAI_KadisonKastler_projection_equivalent_one_of_not_finite

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VectorSupportProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The support projection of a represented vector state

The support is the projection onto the closed commutant orbit. The orbit
construction proves its minimality and faithfulness on the supported corner.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An operator killing the vector kills its supported corner. -/
theorem mul_vectorSupport_eq_zero (M : VonNeumannAlgebra H) (ξ : H)
    (a : Algebra M) (ha : a.val ξ = 0) :
    a.val * (vectorSupportProjection M ξ).val.val = 0 := by
  have hker : vectorOrbitClosure M.commutant.toStarSubalgebra ξ ≤ a.val.ker := by
    apply Submodule.topologicalClosure_minimal
    · rintro y ⟨b,rfl⟩
      change a.val (b.val ξ) = 0
      have hc := congrArg (fun T : H →L[ℂ] H => T ξ)
        (VonNeumannAlgebra.mem_commutant_iff.mp b.property a.val a.property)
      change a.val (b.val ξ) = b.val (a.val ξ) at hc
      rw [hc,ha,map_zero]
    · exact a.val.isClosed_ker
  ext η
  exact hker (Submodule.starProjection_apply_mem _ η)

theorem vectorSupport_faithful_corner (M : VonNeumannAlgebra H) (ξ : H)
    (a : Algebra M) (ha : a.val * (vectorSupportProjection M ξ).val.val = a.val)
    (hξ : a.val ξ = 0) : a = 0 := by
  apply Subtype.ext
  exact ha.symm.trans (mul_vectorSupport_eq_zero M ξ a hξ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIIMatrixCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable matrix corners in type III factors

The absence of nonzero finite projections gives a proper isometry. Its
wandering projections are nonzero and orthogonal. A projection supremum
completes them to a partition of one; the published comparison theorem
then joins the pieces by partial isometries.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped BigOperators Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem TypeIIIFactor.exists_proper_isometry (hM : TypeIIIFactor M) :
    ∃ w : Algebra M, star w * w = 1 ∧ w * star w ≠ 1 := by
  have hn : ¬ FiniteProjectionIn M (1 : Algebra M) := by
    intro hf
    have hz := hM.purelyInfinite 1 (IsStarProjection.one (Algebra M)) hf
    exact hM.nonzero (congrArg Subtype.val hz)
  simp only [FiniteProjectionIn, one_mul] at hn
  push Not at hn
  obtain ⟨w, hw, _, hproper⟩ := hn
  exact ⟨w, hw, hproper⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SupportVectorTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Moving a supported vector back to the original representation

Isometries onto its left and right supports turn a vector into a separating
and cyclic vector on the original Hilbert space. Only the concrete support
identities enter the proof.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem support_transfer_separating (M : VonNeumannAlgebra H) (ξ : H)
    (v : Algebra M) (w : Algebra M.commutant)
    (hv : star v * v = 1)
    (hvp : v.val * star v.val = (vectorSupportProjection M ξ).val.val)
    (hwξ : (w.val * star w.val) ξ = ξ) :
    ∀ a : Algebra M, a.val (star (v.val * w.val) ξ) = 0 → a = 0 := by
  intro a ha
  have hwa : a.val * w.val = w.val * a.val :=
    VonNeumannAlgebra.mem_commutant_iff.mp w.property a.val a.property
  have hwv : star v.val * (w.val * star w.val) =
      (w.val * star w.val) * star v.val :=
    VonNeumannAlgebra.mem_commutant_iff.mp
      (M.commutant.mul_mem w.property (M.commutant.star_mem' w.property))
      (star v.val) (M.star_mem' v.property)
  have he : v.val * w.val * a.val * star (v.val * w.val) =
      (v.val * a.val * star v.val) * (w.val * star w.val) := by
    rw [star_mul]
    calc
      v.val * w.val * a.val * (star w.val * star v.val) =
          v.val * a.val * ((w.val * star w.val) * star v.val) := by
        rw [mul_assoc v.val w.val a.val, ← hwa]
        simp only [mul_assoc]
      _ = (v.val * a.val * star v.val) * (w.val * star w.val) := by
        rw [← hwv]
        simp only [mul_assoc]
  have hbξ : (v.val * a.val * star v.val) ξ = 0 := by
    have hzero : (v.val * w.val * a.val * star (v.val * w.val)) ξ = 0 := by
      change v.val (w.val (a.val (star (v.val * w.val) ξ))) = 0
      rw [ha,map_zero,map_zero]
    rw [he,mul_apply_eq_comp,hwξ] at hzero
    exact hzero
  have hv' : star v.val * v.val = 1 := congrArg Subtype.val hv
  have hb : v * a * star v = 0 := by
    apply vectorSupport_faithful_corner M ξ (v * a * star v) _ hbξ
    change (v.val * a.val * star v.val) * (vectorSupportProjection M ξ).val.val = _
    rw [← hvp]
    calc
      (v.val * a.val * star v.val) * (v.val * star v.val) =
          v.val * a.val * (star v.val * v.val) * star v.val := by simp only [mul_assoc]
      _ = v.val * a.val * star v.val := by rw [hv',mul_one]
  have h := congrArg (fun b : Algebra M => star v * b * v) hb
  simpa only [mul_assoc, ← mul_assoc (star v) v, hv, one_mul,
    mul_one, mul_zero, zero_mul] using h

theorem support_transfer_cyclic (M : VonNeumannAlgebra H) (ξ : H)
    (v : Algebra M) (w : Algebra M.commutant)
    (hw : star w * w = 1)
    (hwq : w.val * star w.val = (vectorSupportProjection M.commutant ξ).val.val)
    (hvξ : (v.val * star v.val) ξ = ξ) :
    DenseRange (algebraVectorMap M (star (v.val * w.val) ξ)) := by
  have hswap : v.val * w.val = w.val * v.val :=
    VonNeumannAlgebra.mem_commutant_iff.mp w.property v.val v.property
  let v' : Algebra M.commutant.commutant :=
    ⟨v.val, by simpa only [M.commutant_commutant] using v.property⟩
  have hs := support_transfer_separating M.commutant ξ w v' hw hwq hvξ
  rw [← hswap] at hs
  have hd := commutant_orbit_dense M.commutant (star (v.val * w.val) ξ) hs
  change Dense (Set.range (fun a : Algebra M.commutant.commutant =>
    a.val (star (v.val * w.val) ξ))) at hd
  rw [VonNeumannAlgebra.commutant_commutant] at hd
  change Dense (Set.range (fun a : Algebra M => a.val (star (v.val * w.val) ξ)))
  exact hd

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SymmetricSupportTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Support isometries for a symmetric vector in a type III factor -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem support_transfer_norm (M : VonNeumannAlgebra H) (ξ : H)
    (v : Algebra M) (w : Algebra M.commutant)
    (hv : star v * v = 1) (hw : star w * w = 1)
    (hvp : v.val * star v.val = (vectorSupportProjection M ξ).val.val)
    (hwq : w.val * star w.val = (vectorSupportProjection M.commutant ξ).val.val) :
    ‖star (v.val * w.val) ξ‖ = ‖ξ‖ := by
  have hv' : star v.val * v.val = 1 := congrArg Subtype.val hv
  have hw' : star w.val * w.val = 1 := congrArg Subtype.val hw
  have hU : star (v.val * w.val) * (v.val * w.val) = 1 := by
    rw [star_mul]
    calc
      star w.val * star v.val * (v.val * w.val) =
          star w.val * (star v.val * v.val) * w.val := by simp only [mul_assoc]
      _ = 1 := by rw [hv',mul_one,hw']
  have hqv : (vectorSupportProjection M.commutant ξ).val.val * star v.val =
      star v.val * (vectorSupportProjection M.commutant ξ).val.val :=
    (VonNeumannAlgebra.mem_commutant_iff.mp
      (vectorSupportProjection M.commutant ξ).val.property
      (star v.val) (M.star_mem' v.property)).symm
  have hfix : (v.val * w.val) (star (v.val * w.val) ξ) = ξ := by
    change ((v.val * w.val) * star (v.val * w.val)) ξ = ξ
    rw [star_mul]
    have he : (v.val * w.val) * (star w.val * star v.val) =
        (v.val * star v.val) * (w.val * star w.val) := by
      calc
        _ = v.val * ((w.val * star w.val) * star v.val) := by simp only [mul_assoc]
        _ = _ := by rw [hwq,hqv]; simp only [mul_assoc]
    rw [he,hvp,hwq,mul_apply_eq_comp,vectorSupportProjection_apply,vectorSupportProjection_apply]
  exact (norm_apply_of_operator_isometry (v.val * w.val) hU _).symm.trans
    (congrArg norm hfix)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIICyclicState
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.mem_projectionFamilyRemainderSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A separating state has a cyclic vector in the same type III representation -/

namespace KadisonKastler
open Generator Generator.Tracial
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem TypeIIIFactor.exists_cyclic_vector_same_state_oai
    [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    {M : VonNeumannAlgebra H} (hM : TypeIIIFactor M) (ξ : H) (hξ : ‖ξ‖=1)
    (hs : Function.Injective (algebraVectorMap M ξ)) :
    ∃ Ω : H, ‖Ω‖=1 ∧ DenseRange (algebraVectorMap M Ω) ∧
      Function.Injective (algebraVectorMap M Ω) ∧
      vectorFunctional (M := M) Ω=vectorFunctional ξ := by
  obtain ⟨v,hv,hproper⟩ := hM.exists_proper_isometry
  let q : AlgebraProjection M.commutant :=
    ⟨⟨(cyclicOrbitSpace M ξ).starProjection,cyclicOrbitProjection_mem M ξ⟩,
      ⟨Subtype.ext (Submodule.isIdempotentElem_starProjection _).eq,
        Subtype.ext (isSelfAdjoint_starProjection _).star_eq⟩⟩
  have hq : ¬ FiniteProjectionIn M.commutant q.val :=
    cyclicOrbitProjection_not_finite M ξ hs v hv hproper
  have he := projection_equivalent_one_of_not_finite
    (scalarCenter_commutant M hM.factor) q hq
  obtain ⟨u,hu,hut⟩ := AlgebraProjection.equivalent_symm he
  let w : Algebra M.commutant := u.val
  have hw : star w * w = 1 := u.initial.trans (congrArg Subtype.val hu)
  have hwq : w.val * star w.val = (vectorSupportProjection M.commutant ξ).val.val := by
    have ht : w * star w = q.val := congrArg Subtype.val hut
    have ht' := congrArg Subtype.val ht
    change w.val * star w.val = (cyclicOrbitSpace M ξ).starProjection at ht'
    simpa only [vectorSupportProjection,VonNeumannAlgebra.commutant_commutant,
      cyclicOrbitSpace] using ht'
  have hp : (vectorSupportProjection M ξ).val = 1 := by
    apply hs
    change (vectorSupportProjection M ξ).val.val ξ = (1 : H →L[ℂ] H) ξ
    exact (vectorSupportProjection_apply M ξ).trans (one_apply_eq_self ξ).symm
  have hp' : (1 : H →L[ℂ] H) * star 1 = (vectorSupportProjection M ξ).val.val := by
    simp only [star_one,mul_one,hp,OneMemClass.coe_one]
  let Ω := star ((1 : Algebra M).val * w.val) ξ
  have hcyc : DenseRange (algebraVectorMap M Ω) :=
    support_transfer_cyclic M ξ 1 w hw hwq (by simp)
  have hsep : Function.Injective (algebraVectorMap M Ω) := by
    intro a b hab
    apply sub_eq_zero.mp
    apply support_transfer_separating M ξ 1 w (by simp) hp'
      (by rw [hwq,vectorSupportProjection_apply]) (a-b)
    change a.val Ω - b.val Ω = 0
    exact sub_eq_zero.mpr hab
  have hn := support_transfer_norm M ξ 1 w (by simp) hw hp' hwq
  have hfix : w.val Ω=ξ := by
    change w.val (star ((1 : Algebra M).val*w.val) ξ)=ξ
    simp only [OneMemClass.coe_one,one_mul,← mul_apply_eq_comp,hwq,
      vectorSupportProjection_apply]
  have hstate : vectorFunctional (M := M) Ω=vectorFunctional ξ := by
    ext a
    have hc := VonNeumannAlgebra.mem_commutant_iff.mp w.property a.val a.property
    have he : w.val (a.val Ω)=a.val ξ := by
      change (w.val*a.val) Ω=a.val ξ
      rw [← hc,mul_apply_eq_comp,hfix]
    change inner ℂ Ω (a.val Ω)=inner ℂ ξ (a.val ξ)
    have hi (x y : H) : inner ℂ (w.val x) (w.val y)=inner ℂ x y := by
      rw [← ContinuousLinearMap.adjoint_inner_right]
      change inner ℂ x ((star w.val*w.val) y)=inner ℂ x y
      rw [show star w.val*w.val=1 from congrArg Subtype.val hw,one_apply_eq_self]
    rw [← hi Ω (a.val Ω),hfix,he]
  exact ⟨Ω,hn.trans hξ,hcyc,hsep,hstate⟩


end
end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.TypeIIIFactor.exists_cyclic_vector_same_state_oai.{u_1} := @OAI.KadisonKastler.TypeIIIFactor.exists_cyclic_vector_same_state_oai.{u_1}
