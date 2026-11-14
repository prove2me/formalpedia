-- Prove2me | solution 1 for OAI.KadisonKastler.twoStateCorner_positive_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T09:08:12.568936+00:00
-- url     : https://prove2.me/submissions/435996bb-cf12-4743-a890-68f466a809c9

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
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
import Mathlib.Analysis.InnerProductSpace.ProdL2
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
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K039
import Definitions.Def_Q260K041
import Definitions.Def_Q260K042
import Theorems.Thm_OAI_KadisonKastler_twoStateCorner_polar_conjugation
import Theorems.Thm_OAI_KadisonKastler_twoStateCorner_positive

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPositiveCone
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The cone generated by modular quadratic vectors

The definition uses actual vectors `a J a J ξ`, finite positive combinations,
and norm closure. Its invariance is algebraic. Positivity of the reference
pairing is kept explicit here and proved for the polar Tomita conjugation
in `TomitaPositivePairing`.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.instInnerProductSpaceReal_solutions
theorem modularPositiveCone_isClosed (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) :
    IsClosed (modularPositiveCone (M := M) J ξ : Set H) := isClosed_closure

theorem modularQuadratic_mem_positiveCone (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (a : Algebra M) :
    modularQuadratic J a ξ ∈ modularPositiveCone (M := M) J ξ :=
  subset_closure (ConvexCone.subset_hull ⟨a,rfl⟩)

theorem zero_mem_modularPositiveCone (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) :
    (0 : H) ∈ modularPositiveCone (M := M) J ξ := by
  have h := modularQuadratic_mem_positiveCone J ξ (0 : Algebra M)
  simpa only [modularQuadratic,ZeroMemClass.coe_zero,zero_mul,zero_apply] using h

theorem modularQuadratic_preserves_positiveCone
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (a : Algebra M) {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ) :
    modularQuadratic J a η ∈ modularPositiveCone (M := M) J ξ := by
  let C := ConvexCone.hull ℝ (Set.range (fun b : Algebra M => modularQuadratic J b ξ))
  have hC : C ≤ C.comap ((modularQuadratic J a).restrictScalars ℝ).toLinearMap := by
    apply ConvexCone.hull_min
    rintro _ ⟨b,rfl⟩
    change modularQuadratic J a (modularQuadratic J b ξ) ∈ C
    change (modularQuadratic J a * modularQuadratic J b) ξ ∈ C
    rw [modularQuadratic_mul J hJ hright]
    exact ConvexCone.subset_hull ⟨a*b,rfl⟩
  exact map_mem_closure (modularQuadratic J a).continuous hη (fun _ hx => hC hx)

theorem modularPositiveCone_acute
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η ζ : H} (hη : η ∈ modularPositiveCone (M := M) J ξ) (hζ : ζ ∈ modularPositiveCone (M := M) J ξ) :
    0 ≤ inner ℝ η ζ := by
  let C := ConvexCone.hull ℝ (Set.range (fun a : Algebra M => modularQuadratic J a ξ))
  have hgen (a b : Algebra M) :
      0 ≤ inner ℝ (modularQuadratic J a ξ) (modularQuadratic J b ξ) := by
    rw [real_inner_eq_re_inner,← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.star_eq_adjoint,modularQuadratic_star J hJ hright]
    change 0 ≤ (inner ℂ ξ ((modularQuadratic J (star a) * modularQuadratic J b) ξ)).re
    rw [modularQuadratic_mul J hJ hright]
    exact hpos (star a*b)
  have hleft (b : Algebra M) : C ≤ realInnerHalfspace (modularQuadratic J b ξ) := by
    apply ConvexCone.hull_min
    rintro _ ⟨a,rfl⟩
    exact hgen a b
  have hh (υ : H) (hυ : υ ∈ C) : C ≤ realInnerHalfspace υ := by
    apply ConvexCone.hull_min
    rintro _ ⟨b,rfl⟩
    change 0 ≤ inner ℝ (modularQuadratic J b ξ) υ
    rw [real_inner_comm]
    exact hleft b hυ
  have hhclosed (υ : H) : IsClosed {v : H | 0 ≤ inner ℝ v υ} :=
    isClosed_le continuous_const (continuous_id.inner continuous_const)
  have hηC (υ : H) (hυ : υ ∈ C) : 0 ≤ inner ℝ η υ :=
    closure_minimal (fun _ hx => hh υ hυ hx) (hhclosed υ) hη
  rw [real_inner_comm]
  apply closure_minimal (s := (C : Set H)) ?_ (hhclosed η) hζ
  intro υ hυ
  change 0 ≤ inner ℝ υ η
  rw [real_inner_comm]
  exact hηC υ hυ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaPositivePairing
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positivity of the modular quadratic vectors

The two commuting positive graph roots give the positive core pairing
for the constructed polar conjugation. No natural-cone axiom is assumed.
-/

namespace KadisonKastler

open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem tomitaPolarConjugation_positive_pairing (a : Algebra M) :
    0 ≤ inner ℂ (a.val Ω) (tomitaPolarConjugation J Ω hsep hcyc (star a.val Ω)) := by
  rw [← tomitaCoreCoordinate_first J Ω hsep hcyc a,
    ← tomitaCoreCoordinate_complement J Ω hsep hcyc a,
    ← ContinuousLinearMap.adjoint_inner_right]
  have hs : (tomitaGraphRoot (M := M) J Ω).adjoint = tomitaGraphRoot (M := M) J Ω :=
    (tomitaGraphRoot_selfAdjoint J Ω).star_eq
  rw [hs]
  have hp : 0 ≤ tomitaGraphRoot (M := M) J Ω * tomitaGraphComplementRoot (M := M) J Ω :=
    Commute.mul_nonneg (CFC.sqrt_nonneg _) (tomitaGraphComplementRoot_nonneg J Ω)
      (tomitaGraphRoots_commute J Ω)
  exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hp).inner_nonneg_right _

theorem tomitaPolarConjugation_quadratic_nonneg (a : Algebra M) :
    0 ≤ inner ℂ Ω (a.val (conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc)
      a.val Ω)) := by
  have he := tomitaPolarConjugation_positive_pairing J Ω hsep hcyc (star a)
  simp only [StarMemClass.coe_star,star_star] at he
  change 0 ≤ inner ℂ Ω (a.val (tomitaPolarConjugation J Ω hsep hcyc
    (a.val (tomitaPolarConjugation J Ω hsep hcyc Ω))))
  rw [tomitaPolarConjugation_fixes_vector J Ω hsep hcyc,
    ← ContinuousLinearMap.adjoint_inner_left]
  exact he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CanonicalPositiveCone
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positivity of the cone for the constructed modular conjugation

The positive core pairing and the constructed commutant theorem make the
generated cone acute. In particular its intersection with its negative is
zero. Self-duality and representation of all normal states are not asserted.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H)
  (hsep : Function.Injective (algebraVectorMap M ξ))
  (hcyc : DenseRange (algebraVectorMap M ξ))

theorem tomitaPolarConjugation_right_mem (a : Algebra M) :
    conjugationOperator (tomitaPolarConjugation J ξ hsep hcyc) a.val ∈ M.commutant := by
  rw [← tomitaPolarConjugation_commutant_eq J ξ hsep hcyc]
  exact ⟨a.val,a.property,rfl⟩

theorem canonicalModularPositiveCone_acute {η ζ : H}
    (hη : η ∈ canonicalModularPositiveCone J ξ hsep hcyc)
    (hζ : ζ ∈ canonicalModularPositiveCone J ξ hsep hcyc) :
    0 ≤ (inner ℂ η ζ).re := by
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  change 0 ≤ inner ℝ η ζ
  apply modularPositiveCone_acute _ (tomitaPolarConjugation_involutive J ξ hsep hcyc)
    (tomitaPolarConjugation_right_mem J ξ hsep hcyc) ξ ?_ hη hζ
  intro a
  exact (tomitaPolarConjugation_quadratic_nonneg J ξ hsep hcyc a).1

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPositiveReal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The modular conjugation fixes the generated positive cone -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem modularPositiveCone_fixed
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ = ξ) {η : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ) : J η = η := by
  have hgen (a : Algebra M) : J (modularQuadratic J a ξ) = modularQuadratic J a ξ := by
    have he : J (modularQuadratic J a ξ) =
        conjugationOperator J a.val (a.val ξ) := by
      change J (a.val (J (a.val (J ξ)))) = J (a.val (J (a.val ξ)))
      rw [hξ]
    rw [he]
    exact congrArg (fun T : H →L[ℂ] H => T ξ)
      (VonNeumannAlgebra.mem_commutant_iff.mp (hright a) a.val a.property).symm
  have hh : ConvexCone.hull ℝ (Set.range (fun a : Algebra M => modularQuadratic J a ξ)) ≤
      conjugationFixedCone J := by
    apply ConvexCone.hull_min
    rintro _ ⟨a,rfl⟩
    exact hgen a
  exact closure_minimal (fun _ h => hh h)
    (isClosed_eq J.continuous continuous_id) hη

theorem reference_mem_modularPositiveCone
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (ξ : H) :
    ξ ∈ modularPositiveCone (M := M) J ξ := by
  have h := modularQuadratic_mem_positiveCone J ξ (1 : Algebra M)
  simpa only [modularQuadratic,OneMemClass.coe_one,conjugationOperator_one J hJ,
    one_mul,one_apply_eq_self] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveConeOrthogonality
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixCentralVectorSpace_complete _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.faithfulTensorHom_intertwines _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_symm_apply _root_.OAI.KadisonKastler.tomitaPolarCoordinates_root _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Orthogonal positive vectors have orthogonal algebra supports

The quadratic positivity of the generated modular cone suffices for this
step of Araki's Theorem 4(7), Pacific J. Math. 50 (1974), 309–354.
No self-duality or positive decomposition is assumed.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

private theorem linear_coefficient_eq_zero {A B : ℝ}
    (h : ∀ t : ℝ, 0 ≤ A*(t*t)+B*t) : B=0 := by
  have hd := discrim_le_zero (a := A) (b := B) (c := 0) (by simpa using h)
  simp only [discrim,mul_zero,sub_zero] at hd
  nlinarith [sq_nonneg B]

attribute [local instance] OAI.KadisonKastler.positiveOrthogonalityRealInner
theorem positiveCone_inner_left_eq_zero_of_dual_orthogonal
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ=ξ)
    {η ζ : H} (hηJ : J η=η)
    (hdual : ∀ v ∈ modularPositiveCone (M := M) J ξ, 0 ≤ inner ℝ η v)
    (hζ : ζ ∈ modularPositiveCone (M := M) J ξ)
    (horth : inner ℝ η ζ=0) (a : Algebra M) :
    inner ℂ η (a.val ζ)=0 := by
  have hζJ := modularPositiveCone_fixed J hright ξ hξ hζ
  have hreal (b : Algebra M) : (inner ℂ η (b.val ζ)).re=0 := by
    have hp (t : ℝ) : 0 ≤
        inner ℝ η (modularQuadratic J b ζ)*(t*t)+
          (2*inner ℝ η (b.val ζ))*t := by
      let c : Algebra M := 1+(t : ℂ) • b
      have hc := hdual _
        (modularQuadratic_preserves_positiveCone J hJ hright ξ c hζ)
      have he : conjugationOperator J c.val =
          1+(t : ℂ) • conjugationOperator J b.val := by
        change conjugationOperator J (1+(t : ℂ) • b.val)=_
        rw [conjugationOperator_add,conjugationOperator_one J hJ,conjugationOperator_smul]
        simp
      have hv : modularQuadratic J c ζ =
          ζ+(t : ℂ) • conjugationOperator J b.val ζ+
            (t : ℂ) • b.val ζ+((t*t : ℝ) : ℂ) • modularQuadratic J b ζ := by
        change (1+(t : ℂ) • b.val) (conjugationOperator J c.val ζ)=_
        rw [he]
        simp only [add_apply,one_apply_eq_self,smul_apply,map_add,map_smul,smul_add,
          smul_smul,modularQuadratic,mul_apply_eq_comp,Complex.ofReal_mul]
        abel
      have hs (v : H) : (t : ℂ) • v=t • v := by
        simpa only [Complex.coe_algebraMap] using (IsScalarTower.algebraMap_smul ℂ t v)
      have hs2 (v : H) : ((t*t : ℝ) : ℂ) • v=(t*t) • v := by
        simpa only [Complex.coe_algebraMap] using (IsScalarTower.algebraMap_smul ℂ (t*t) v)
      have heq : inner ℝ η (conjugationOperator J b.val ζ)=inner ℝ η (b.val ζ) := by
        simp only [real_inner_eq_re_inner]
        change (inner ℂ η (J (b.val (J ζ)))).re=_
        rw [hζJ,← hηJ,conjugateIsometry_inner]
        simp only [hηJ,RCLike.re_eq_complex_re,Complex.star_def,Complex.conj_re]
      rw [hv,inner_add_right,inner_add_right,inner_add_right,hs,hs,hs2,
        real_inner_smul_right,real_inner_smul_right,real_inner_smul_right,horth,heq] at hc
      nlinarith only [hc]
    have he := linear_coefficient_eq_zero hp
    change (inner ℂ η (b.val ζ)).re=0
    change 2*(inner ℂ η (b.val ζ)).re=0 at he
    linarith
  apply Complex.ext
  · exact hreal a
  · have hi := hreal (Complex.I • a)
    change (inner ℂ η (Complex.I • a.val ζ)).re=0 at hi
    rw [inner_smul_right] at hi
    simpa using hi

/-- A positive support also kills orthogonal fixed vectors in the dual cone. -/
theorem positiveCone_support_kills_dual_of_orthogonal
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ)
    {η ζ : H} (hηJ : J η=η)
    (hdual : ∀ v ∈ modularPositiveCone (M := M) J ξ, 0 ≤ inner ℝ η v)
    (hζ : ζ ∈ modularPositiveCone (M := M) J ξ)
    (horth : inner ℝ η ζ=0) :
    (vectorSupportProjection M ζ).val.val η=0 := by
  have hζJ := modularPositiveCone_fixed J hright ξ hξ hζ
  have horbit (b : Algebra M.commutant) : inner ℂ (b.val ζ) η=0 := by
    have hb := positiveCone_inner_left_eq_zero_of_dual_orthogonal J hJ hright ξ hξ
      hηJ hdual hζ horth ⟨conjugationOperator J b.val,hleft b⟩
    change inner ℂ η (J (b.val (J ζ)))=0 at hb
    rw [hζJ,← hηJ,conjugateIsometry_inner] at hb
    have hh : inner ℂ η (b.val ζ)=0 := star_eq_zero.mp hb
    rwa [inner_eq_zero_symm]
  have hz : η ∈ (vectorOrbitClosure M.commutant.toStarSubalgebra ζ)ᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro v hv
    have hc : IsClosed {v : H | inner ℂ v η=0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    apply closure_minimal ?_ hc hv
    rintro v ⟨b,rfl⟩
    exact horbit b
  change (vectorOrbitClosure M.commutant.toStarSubalgebra ζ).starProjection η=0
  simpa only [Submodule.starProjection_apply,ZeroMemClass.coe_zero] using congrArg Subtype.val
    ((vectorOrbitClosure M.commutant.toStarSubalgebra ζ).orthogonalProjectionOnto_apply_of_mem_orthogonal hz)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveConeDualProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Projection onto the generated positive cone

The Hilbert projection theorem gives a positive part and an orthogonal
residual in the dual cone. Both vectors are fixed by the conjugation.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.positiveDualProjectionRealInner
theorem exists_positiveCone_dual_decomposition
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ=ξ) (x : H) (hx : J x=x) :
    ∃ v r : H, v ∈ modularPositiveCone (M := M) J ξ ∧ J r=r ∧
      (∀ w ∈ modularPositiveCone (M := M) J ξ, 0 ≤ inner ℝ r w) ∧
      inner ℝ r v=0 ∧ x=v-r := by
  let C := modularPositiveCone (M := M) J ξ
  have h0 : (0 : H) ∈ C := zero_mem_modularPositiveCone J ξ
  obtain ⟨v,hv,hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    ⟨0,h0⟩ (modularPositiveCone_isClosed J ξ).isComplete C.convex x
  have hineq := (norm_eq_iInf_iff_real_inner_le_zero C.convex hv).mp hmin
  have hvJ := modularPositiveCone_fixed J hright ξ hξ hv
  have hinner : inner ℝ (x-v) v=0 := by
    have hzero := hineq 0 h0
    have htwo := hineq (v+v) (C.add_mem hv hv)
    simp only [zero_sub,inner_neg_right] at hzero
    rw [add_sub_cancel_left] at htwo
    linarith
  refine ⟨v,v-x,hv,?_,?_,?_,by abel⟩
  · rw [map_sub,hvJ,hx]
  · intro w hw
    have h := hineq (w+v) (C.add_mem hw hv)
    rw [add_sub_cancel_right,inner_sub_left] at h
    rw [inner_sub_left]
    linarith
  · rw [inner_sub_left] at hinner ⊢
    linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveConeSelfDual
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Self-duality on the conjugation-fixed real Hilbert space

A dual residual orthogonal to a positive vector is killed by its support.
Compressing the reference vector to the complementary corner then forces
that residual to vanish. Cyclicity of the reference is the only density
hypothesis. This proves the local self-duality needed for state estimates.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.positiveSelfDualRealInner
theorem positiveCone_dual_eq_zero_of_reference_orthogonal
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    {r : H} (hrJ : J r=r)
    (hdual : ∀ w ∈ modularPositiveCone (M := M) J ξ, 0 ≤ inner ℝ r w)
    (horth : inner ℝ r ξ=0) : r=0 := by
  have hcoeff (a : Algebra M) : inner ℂ r (a.val ξ)=0 :=
    positiveCone_inner_left_eq_zero_of_dual_orthogonal J hJ hright ξ hξ hrJ hdual
      (reference_mem_modularPositiveCone J hJ ξ) horth a
  apply ext_inner_right ℂ
  intro y
  simp only [inner_zero_left]
  apply hcyc.induction_on (p := fun y => inner ℂ r y=0) y
  · exact isClosed_eq (continuous_const.inner continuous_id) continuous_const
  · exact hcoeff

theorem modularPositiveCone_mem_of_dual
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    {x : H} (hxJ : J x=x)
    (hxdual : ∀ w ∈ modularPositiveCone (M := M) J ξ, 0 ≤ inner ℝ x w) :
    x ∈ modularPositiveCone (M := M) J ξ := by
  obtain ⟨v,r,hv,hrJ,hrdual,hrv,hx⟩ :=
    exists_positiveCone_dual_decomposition J hright ξ hξ x hxJ
  let p := vectorSupportProjection M v
  let q : AlgebraProjection M := ⟨1-p.val,p.property.one_sub⟩
  have hpv : p.val.val v=v := vectorSupportProjection_apply M v
  have hpr : p.val.val r=0 :=
    positiveCone_support_kills_dual_of_orthogonal J hJ hright hleft ξ hξ hrJ hrdual hv hrv
  have hqv : q.val.val v=0 := by
    change v-p.val.val v=0
    rw [hpv,sub_self]
  have hqr : q.val.val r=r := by
    change r-p.val.val r=r
    rw [hpr,sub_zero]
  have hvJ := modularPositiveCone_fixed J hright ξ hξ hv
  have hQv : modularQuadratic J q.val v=0 := by
    change q.val.val (J (q.val.val (J v)))=0
    rw [hvJ,hqv,map_zero,map_zero]
  have hQr : modularQuadratic J q.val r=r := by
    change q.val.val (J (q.val.val (J r)))=r
    rw [hrJ,hqr,hrJ,hqr]
  have hQstar : star (modularQuadratic J q.val)=modularQuadratic J q.val := by
    rw [modularQuadratic_star J hJ hright,q.property.isSelfAdjoint.star_eq]
  have hpair (z : H) : inner ℝ z (modularQuadratic J q.val ξ)=
      inner ℝ (modularQuadratic J q.val z) ξ := by
    simp only [real_inner_eq_re_inner]
    rw [← ContinuousLinearMap.adjoint_inner_left,← ContinuousLinearMap.star_eq_adjoint,hQstar]
  have hrξ : inner ℝ r ξ=0 := by
    have hnonneg := hrdual ξ (reference_mem_modularPositiveCone J hJ ξ)
    have hcut := hxdual (modularQuadratic J q.val ξ)
      (modularQuadratic_mem_positiveCone J ξ q.val)
    rw [hx,inner_sub_left,hpair v,hpair r,hQv,hQr,inner_zero_left] at hcut
    linarith
  have hr := positiveCone_dual_eq_zero_of_reference_orthogonal J hJ hright ξ hξ hcyc
    hrJ hrdual hrξ
  rw [hx,hr,sub_zero]
  exact hv

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StandardTypeIIIVector
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Modular conjugation on the original type III representation -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem ModularConjugationData.left_mem {M : VonNeumannAlgebra H} {ξ : H}
    (d : ModularConjugationData M ξ) (a : Algebra M.commutant) :
    conjugationOperator d.conjugation a.val ∈ M := by
  have ha : a.val ∈ (conjugateRightAlgebra d.conjugation d.involutive M :
      Set (H →L[ℂ] H)) := by
    rw [d.commutant]
    exact a.property
  obtain ⟨b,hb,hba⟩ := ha
  rw [← hba,conjugationOperator_twice _ d.involutive]
  exact hb

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoStatePositiveCorner
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positive vectors in the diagonal corners of the two-state representation -/

namespace KadisonKastler
open Generator
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (M : VonNeumannAlgebra H) (Ω ξ : H)
  (hΩc : DenseRange (algebraVectorMap M Ω)) (hξc : DenseRange (algebraVectorMap M ξ))
  (hΩs : Function.Injective (algebraVectorMap M Ω))
  (hξs : Function.Injective (algebraVectorMap M ξ))
  (J : H ≃ₗᵢ⋆[ℂ] H)
  (L : TwoStateMatrixHilbert H H ≃ₗᵢ⋆[ℂ] TwoStateMatrixHilbert H H)

attribute [local instance] OAI.KadisonKastler.twoStatePositiveReal
attribute [local instance] OAI.KadisonKastler.twoStateBigPositiveReal
theorem twoStateCorner_positive_iff_oai (i : Fin 2) (x : H) :
    twoStateCornerEmbedding i x ∈ canonicalModularPositiveCone L (twoStateMatrixVector Ω ξ)
      (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)
      (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc) ↔
    x ∈ canonicalModularPositiveCone J (twoStateVectorAt Ω ξ i)
      (twoStateVectorAt_separating M Ω ξ hΩs hξs i)
      (twoStateVectorAt_cyclic M Ω ξ hΩc hξc i) := by
  constructor
  · intro hx
    let η := twoStateVectorAt Ω ξ i
    let hs := twoStateVectorAt_separating M Ω ξ hΩs hξs i
    let hc := twoStateVectorAt_cyclic M Ω ξ hΩc hξc i
    let d := constructedModularConjugationData J η hs hc
      (tomitaPolarConjugation_commutant_eq J η hs hc)
    apply modularPositiveCone_mem_of_dual d.conjugation d.involutive (d.right_mem le_rfl)
      d.left_mem η d.fixes_vector hc
    · apply (twoStateCornerEmbedding i).injective
      have hf := modularPositiveCone_fixed _
        (tomitaPolarConjugation_right_mem L (twoStateMatrixVector Ω ξ)
          (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)
          (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc))
        (twoStateMatrixVector Ω ξ)
        (tomitaPolarConjugation_fixes_vector L (twoStateMatrixVector Ω ξ)
          (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)
          (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc)) hx
      rw [twoStateCorner_polar_conjugation M Ω ξ hΩc hξc hΩs hξs J L] at hf
      exact hf
    · intro w hw
      have hp := canonicalModularPositiveCone_acute L (twoStateMatrixVector Ω ξ)
        (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)
        (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc) hx
        (twoStateCorner_positive M Ω ξ hΩc hξc hΩs hξs J L i hw)
      have hi := congrArg Complex.re ((twoStateCornerEmbedding i).inner_map_map x w)
      change inner ℝ (twoStateCornerEmbedding i x) (twoStateCornerEmbedding i w) =
        inner ℝ x w at hi
      exact hi ▸ hp
  · exact twoStateCorner_positive M Ω ξ hΩc hξc hΩs hξs J L i

end
end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.twoStateCorner_positive_iff_oai.{u_1} := @OAI.KadisonKastler.twoStateCorner_positive_iff_oai.{u_1}
