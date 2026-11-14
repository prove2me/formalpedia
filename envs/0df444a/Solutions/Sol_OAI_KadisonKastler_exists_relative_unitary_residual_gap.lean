-- Prove2me | solution 1 for OAI.KadisonKastler.exists_relative_unitary_residual_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T14:33:10.491641+00:00
-- url     : https://prove2.me/submissions/6e56d77e-3f9c-4e02-b357-2219ad9bd880

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
import Definitions.Def_Q260K044
import Theorems.Thm_OAI_KadisonKastler_exists_unitary_gap_of_scalar_state_orbit_hull
import Theorems.Thm_OAI_KadisonKastler_relative_centralVectorDefect_unitary_sq_le_stateCommutator
import Theorems.Thm_OAI_KadisonKastler_relative_centralVector_orbit_dense
import Theorems.Thm_OAI_KadisonKastler_scalar_stateOrbitHulls_of_stateBicentralizer

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPositiveReal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveConeFaithfulApproximation
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Faithful positive perturbations in the original Hilbert space

Adding a positive vector to a separating positive vector preserves
separation. A small positive multiple of the reference vector therefore
approximates any cone vector by cyclic separating cone vectors.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.positiveApproximationRealInner
variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
  (ξ : H) (hξ : J ξ = ξ)
  (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))

include hJ in
/-- For a conjugation exchanging the two algebras, a fixed separating
vector is cyclic on the same representation. -/
theorem cyclic_of_separating_of_conjugation_fixed
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    {η : H} (hη : J η = η) (hs : Function.Injective (algebraVectorMap M η)) :
    DenseRange (algebraVectorMap M η) := by
  have hsep' (b : Algebra M.commutant) (hb : b.val η = 0) : b = 0 := by
    let a : Algebra M := ⟨conjugationOperator J b.val,hleft b⟩
    have ha : a.val η = 0 := by
      change J (b.val (J η)) = 0
      rw [hη,hb,map_zero]
    have ha0 : a = 0 := hs (ha.trans (map_zero (algebraVectorMap M η)).symm)
    apply Subtype.ext
    have he := congrArg (fun c : Algebra M => conjugationOperator J c.val) ha0
    change conjugationOperator J (conjugationOperator J b.val) = conjugationOperator J 0 at he
    rw [conjugationOperator_twice J hJ] at he
    have hz : conjugationOperator J (0 : H →L[ℂ] H) = 0 := by
      ext x
      exact map_zero J
    rwa [hz] at he
  have hd := Generator.commutant_orbit_dense M.commutant η hsep'
  change Dense (Set.range (fun a : Algebra M.commutant.commutant => a.val η)) at hd
  rw [VonNeumannAlgebra.commutant_commutant] at hd
  exact hd

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativeCentralStandardSpace
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete standard space for a finite matrix relative commutant

The relative algebra's cyclic orbit is exactly the matrix central-vector
space. The original conjugation restricts to this same Hilbert subspace.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (E : MatrixUnitSystem ι (Algebra M))
  (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

omit [Nonempty ι] in
theorem relative_vector_separating (η : H)
    (hsep : Function.Injective (algebraVectorMap M η)) :
    Function.Injective (algebraVectorMap E.relativeVonNeumann η) := by
  intro a b hab
  have he := hsep (a₁ := ⟨a.val,E.relativeVonNeumann_le a.property⟩)
    (a₂ := ⟨b.val,E.relativeVonNeumann_le b.property⟩) hab
  exact Subtype.ext (congrArg (fun c : Algebra M => c.val) he)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CenteredVectorApproximation
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.faithfulTensorHom_intertwines _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Centered cyclic approximation and commutator defects -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_centered_algebra_vector_near_of_mem_closure
    (ξ : H) (hunit : ‖ξ‖=1) (η : H) (horth : inner ℂ ξ η=0)
    (hηclosure : η ∈ closure (Set.range (algebraVectorMap M ξ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : Algebra M, vectorFunctional (M := M) ξ a=0 ∧ ‖a.val ξ-η‖ < ε := by
  obtain ⟨v,⟨a,rfl⟩,ha⟩ := Metric.mem_closure_iff.mp hηclosure (ε/2) (half_pos hε)
  have hd : ‖a.val ξ-η‖ < ε/2 := by
    change dist η (a.val ξ) < ε/2 at ha
    simpa only [dist_eq_norm,norm_sub_rev] using ha
  let c : ℂ := inner ℂ ξ (a.val ξ)
  let b : Algebra M := a-c • 1
  have hbe : b.val ξ=a.val ξ-c • ξ := by
    change (a.val-c • (1 : H →L[ℂ] H)) ξ=_
    simp only [sub_apply,smul_apply,one_apply_eq_self]
  have hself : inner ℂ ξ ξ=1 := by
    rw [inner_self_eq_norm_sq_to_K,hunit]
    norm_num
  have hc : ‖c‖ ≤ ‖a.val ξ-η‖ := by
    have he : c=inner ℂ ξ (a.val ξ-η) := by rw [inner_sub_right,horth,sub_zero]
    rw [he]
    simpa only [hunit,one_mul] using norm_inner_le_norm ξ (a.val ξ-η)
  refine ⟨b,?_,?_⟩
  · change inner ℂ ξ (b.val ξ)=0
    rw [hbe,inner_sub_right,inner_smul_right,hself,mul_one]
    exact sub_self c
  · rw [hbe]
    have he : a.val ξ-c • ξ-η=(a.val ξ-η)-c • ξ := by abel
    rw [he]
    have hn := norm_sub_le (a.val ξ-η) (c • ξ)
    rw [norm_smul,hunit,mul_one] at hn
    linarith

theorem centralVectorDefect_on_algebra_vector
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (a b : Algebra M) :
    centralVectorDefect J (a.val ξ) b.val =
      (b*a-a*b).val ξ+a.val (centralVectorDefect J ξ b.val) := by
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp (hright (star b)) a.val a.property
  have he := congrArg (fun T : H →L[ℂ] H => T ξ) hc
  change a.val (conjugationOperator J (star b).val ξ)=
    conjugationOperator J (star b).val (a.val ξ) at he
  change a.val (conjugationOperator J (star b.val) ξ)=
    conjugationOperator J (star b.val) (a.val ξ) at he
  change b.val (a.val ξ)-conjugationOperator J (star b.val) (a.val ξ)=
    (b.val (a.val ξ)-a.val (b.val ξ))+
      a.val (b.val ξ-conjugationOperator J (star b.val) ξ)
  rw [map_sub,← he]
  abel

theorem commutator_vector_norm_le_central_defects
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (a b : Algebra M) :
    ‖(b*a-a*b).val ξ‖ ≤ ‖centralVectorDefect J (a.val ξ) b.val‖+
      ‖a‖*‖centralVectorDefect J ξ b.val‖ := by
  have he := centralVectorDefect_on_algebra_vector J hright ξ a b
  have h : (b*a-a*b).val ξ=centralVectorDefect J (a.val ξ) b.val-
      a.val (centralVectorDefect J ξ b.val) := by rw [he]; abel
  rw [h]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl (a.val.le_opNorm _))

theorem centralVectorDefect_vector_lipschitz
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (ξ η : H) (a : H →L[ℂ] H) :
    ‖centralVectorDefect J ξ a‖ ≤ ‖centralVectorDefect J η a‖+2*‖ξ-η‖*‖a‖ := by
  have he : centralVectorDefect J ξ a=centralVectorDefect J η a+
      centralVectorDefect J (ξ-η) a := by
    simp only [centralVectorDefect_apply,map_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add le_rfl
    (centralVectorDefect_norm_le J hJ (ξ-η) a))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UnitaryResidualGap
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.faithfulTensorHom_intertwines _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Near-central unitaries with a uniform residual gap

The scalar hull conclusion of Haagerup's Proposition 1.3 gives the
unitary gap in Lemma 3.2. Centered cyclic approximation extends the
operator-vector calculation to every vector orthogonal to the reference.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.unitaryResidualRealInner
private theorem centered_unitary_gap
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H)
    (hbound : ∀ u : unitary (Algebra M),
      ‖centralVectorDefect J ξ u.val.val‖^2 ≤ ‖vectorStateCommutator ξ u.val‖)
    (a : Algebra M) (hcenter : vectorFunctional ξ a=0) (haξ : a.val ξ≠0)
    (hhull : ∀ δ : ℝ, 0 < δ → ∃ z : ℂ,
      ContinuousLinearMapWOT.ofCLM (z • (1 : H →L[ℂ] H)) ∈
        closedConvexHull ℝ (stateUnitaryOrbit ξ a δ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary (Algebra M), ‖centralVectorDefect J ξ u.val.val‖ < ε ∧
      (3/4:ℝ)*‖a.val ξ‖ < ‖centralVectorDefect J (a.val ξ) u.val.val‖ := by
  have hn : 0 < ‖a.val ξ‖ := norm_pos_iff.mpr haξ
  let e := min ε (‖a.val ξ‖/(16*(‖a‖+1)))
  have he : 0 < e := lt_min hε (div_pos hn (by positivity))
  let δ := e^2/2
  have hδ : 0 < δ := by dsimp only [δ] <;> positivity
  obtain ⟨z,hz⟩ := hhull δ hδ
  obtain ⟨u,hustate,hugap⟩ := exists_unitary_gap_of_scalar_state_orbit_hull
    ξ a hcenter haξ δ (7/8) (by norm_num) (by norm_num) z hz
  have hsq := hbound u
  have hu : ‖centralVectorDefect J ξ u.val.val‖ < e := by
    dsimp only [δ] at hustate
    nlinarith only [hsq,hustate,he,norm_nonneg (centralVectorDefect J ξ u.val.val)]
  have hden : 0 < 16*(‖a‖+1) := by positivity
  have hprod : ‖a‖*‖centralVectorDefect J ξ u.val.val‖ ≤ ‖a.val ξ‖/16 := by
    have hle := hu.le.trans (min_le_right ε (‖a.val ξ‖/(16*(‖a‖+1))))
    have hm := (le_div_iff₀ hden).mp hle
    nlinarith only [hm,norm_nonneg (centralVectorDefect J ξ u.val.val)]
  have hcomm := commutator_vector_norm_le_central_defects J hright ξ a u.val
  refine ⟨u,hu.trans_le (min_le_left _ _),?_⟩
  linarith only [hugap,hcomm,hprod,hn]

theorem exists_unitary_residual_gap_of_state_defect_bound
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hunit : ‖ξ‖=1)
    (hbound : ∀ u : unitary (Algebra M),
      ‖centralVectorDefect J ξ u.val.val‖^2 ≤ ‖vectorStateCommutator ξ u.val‖)
    (hhull : ∀ a : Algebra M, ∀ δ : ℝ, 0 < δ → ∃ z : ℂ,
      ContinuousLinearMapWOT.ofCLM (z • (1 : H →L[ℂ] H)) ∈
        closedConvexHull ℝ (stateUnitaryOrbit ξ a δ))
    (η : H) (hη : η≠0) (horth : inner ℂ ξ η=0)
    (hηclosure : η ∈ closure (Set.range (algebraVectorMap M ξ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary (Algebra M), ‖centralVectorDefect J ξ u.val.val‖ < ε ∧
      ‖η‖/2 ≤ ‖centralVectorDefect J η u.val.val‖ := by
  have hn : 0 < ‖η‖ := norm_pos_iff.mpr hη
  obtain ⟨a,hcenter,hnear⟩ := exists_centered_algebra_vector_near_of_mem_closure ξ hunit η horth hηclosure
    (‖η‖/64) (by positivity)
  have haξ : a.val ξ≠0 := by
    intro hz
    rw [hz,zero_sub,norm_neg] at hnear
    linarith
  have hnorm : ‖η‖ ≤ ‖a.val ξ‖+‖a.val ξ-η‖ := by
    have h := norm_le_insert (a.val ξ) η
    simpa only [norm_sub_rev,add_comm] using h
  obtain ⟨u,hu,hugap⟩ := centered_unitary_gap J hright ξ hbound
    a hcenter haξ (hhull a) ε hε
  have hLip := centralVectorDefect_vector_lipschitz J hJ (a.val ξ) η u.val.val
  have hU : ‖u.val.val‖ ≤ 1 := by
    change ‖u.val‖ ≤ 1
    exact norm_unitary_le_one u
  have hnearD : ‖centralVectorDefect J (a.val ξ) u.val.val‖ ≤
      ‖centralVectorDefect J η u.val.val‖+2*‖a.val ξ-η‖ := by
    exact hLip.trans (add_le_add le_rfl
      (mul_le_of_le_one_right (by positivity) hU))
  refine ⟨u,hu,?_⟩
  linarith only [hugap,hnearD,hnorm,hnear,hn]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativeUnitaryStateDefect
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # State commutator bounds in a finite-matrix relative commutant

The relative Powers–Størmer estimate supplies the unitary defect bound
on the central-vector space, without treating the relative algebra as
cyclic on the full ambient Hilbert space.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem relative_conjugation_mem_commutant (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (a : Algebra E.relativeVonNeumann) :
    conjugationOperator J a.val ∈ E.relativeVonNeumann.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  exact VonNeumannAlgebra.mem_commutant_iff.mp
    (hright ⟨a.val,E.relativeVonNeumann_le a.property⟩) T (E.relativeVonNeumann_le hT)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativeBicentralizerGap
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bicentralizer projection gaps in the matrix relative algebra

The residual vector is approximated only in the central-vector space.
The original positive cone supplies the relative state-to-vector bound.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

attribute [local instance] OAI.KadisonKastler.relativeBicentralizerRealInner
theorem exists_relative_unitary_residual_gap_oai
    (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (ζ : H) (hζ : ζ ∈ modularPositiveCone (M := M) J ξ) (hunit : ‖ζ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ζ))
    (hζE : ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (hscalar : ∀ b : Algebra E.relativeVonNeumann, stateBicentralizerMember ζ b →
      ∃ z : ℂ, b=z • 1)
    (η : H) (hη : η≠0) (hηE : η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (horth : inner ℂ ζ η=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary (Algebra E.relativeVonNeumann),
      ‖centralVectorDefect J ζ u.val.val‖ < ε ∧
      ‖η‖/2 ≤ ‖centralVectorDefect J η u.val.val‖ := by
  have hcζ := cyclic_of_separating_of_conjugation_fixed J hJ hleft
    (modularPositiveCone_fixed J hright ξ hξ hζ) hsep
  have hηclosure : η ∈ closure (Set.range (algebraVectorMap E.relativeVonNeumann ζ)) := by
    change η ∈ closure (Set.range (fun a : Algebra E.relativeVonNeumann => a.val ζ))
    rw [relative_centralVector_orbit_dense E J hJ hright ζ hζE hcζ]
    exact hηE
  apply exists_unitary_residual_gap_of_state_defect_bound J hJ
    (relative_conjugation_mem_commutant E J hright) ζ hunit
    (relative_centralVectorDefect_unitary_sq_le_stateCommutator E J hJ hright hleft
      ξ hξ hcyc hpos hζ hζE)
    (scalar_stateOrbitHulls_of_stateBicentralizer ζ (relative_vector_separating E ζ hsep) hscalar)
    η hη horth hηclosure ε hε

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.exists_relative_unitary_residual_gap_oai.{u_1, u_2} := @OAI.KadisonKastler.exists_relative_unitary_residual_gap_oai.{u_1, u_2}
