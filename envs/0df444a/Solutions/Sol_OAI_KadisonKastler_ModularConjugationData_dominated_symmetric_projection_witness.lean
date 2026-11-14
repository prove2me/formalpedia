-- Prove2me | solution 1 for OAI.KadisonKastler.ModularConjugationData.dominated_symmetric_projection_witness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:13:03.713753+00:00
-- url     : https://prove2.me/submissions/20e60058-400b-4629-80fd-ef7e7bf885fa

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
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Interval.Set.Group
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
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
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
import Mathlib.Analysis.Normed.Algebra.Exponential
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
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
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
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Dual.Lemmas
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
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
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
import Mathlib.MeasureTheory.Group.Integral
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
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
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
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Contracting
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
import Definitions.Def_Q260K068
import Definitions.Def_Q260K034
import Theorems.Thm_OAI_KadisonKastler_ModularConjugationData_rightAction_commute
import Theorems.Thm_OAI_KadisonKastler_exists_selfAdjoint_two_vector_gap
import Theorems.Thm_OAI_KadisonKastler_exists_selfAdjoint_two_vector_projection

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CenteredTestEnergy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The centered test as a commutator-energy difference -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularConjugationData

variable (d : ModularConjugationData M Ω)

theorem rightAction_conjugation (a : Algebra M) (ξ : H) :
    d.rightAction (star a) (d.conjugation ξ)=d.conjugation (a.val ξ) := by
  change d.conjugation (star (star a).val (d.conjugation (d.conjugation ξ)))=_
  simp only [StarMemClass.coe_star,star_star]
  rw [d.involutive]

end ModularConjugationData

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DominatedVectorState
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_symm_apply _root_.OAI.KadisonKastler.tomitaPolarCoordinates_root _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded Radon--Nikodym operators for vector states

Domination of the two orbit norms extends the algebraic orbit map to a
bounded operator in the commutant. Its square gives the positive
Radon--Nikodym operator on the original cyclic representation.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

variable (ξ η : H) (hcyc : DenseRange (algebraVectorMap M ξ)) (C : ℝ)
  (hbound : ∀ a : Algebra M, ‖a.val η‖ ≤ C * ‖a.val ξ‖)

include hcyc hbound in
theorem dominatedVectorIntertwiner_orbit (a : Algebra M) :
    dominatedVectorIntertwiner M ξ η (a.val ξ) = a.val η :=
  LinearMap.extendOfNorm_eq hcyc ⟨C,hbound⟩ a

include hcyc hbound in
theorem dominatedVectorIntertwiner_vector : dominatedVectorIntertwiner M ξ η ξ = η := by
  simpa using dominatedVectorIntertwiner_orbit ξ η hcyc C hbound 1

include hcyc hbound in
theorem dominatedVectorIntertwiner_commutant : dominatedVectorIntertwiner M ξ η ∈ M.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  let b : Algebra M := ⟨a,ha⟩
  ext x
  change a (dominatedVectorIntertwiner M ξ η x) = dominatedVectorIntertwiner M ξ η (a x)
  apply hcyc.induction_on
    (p := fun x => a (dominatedVectorIntertwiner M ξ η x) =
      dominatedVectorIntertwiner M ξ η (a x)) x
  · exact isClosed_eq (a.continuous.comp (dominatedVectorIntertwiner M ξ η).continuous)
      ((dominatedVectorIntertwiner M ξ η).continuous.comp a.continuous)
  · intro c
    change a (dominatedVectorIntertwiner M ξ η (c.val ξ)) =
      dominatedVectorIntertwiner M ξ η ((b*c).val ξ)
    rw [dominatedVectorIntertwiner_orbit ξ η hcyc C hbound,
      dominatedVectorIntertwiner_orbit ξ η hcyc C hbound]
    rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HaagerupBoundedVectorWitness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Two-vector witnesses on the algebraic symmetric core

This is the bounded-vector part of Haagerup's Lemma 2.9. The constants
are deliberately loose; they remain uniform over the algebra and vector.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularConjugationData

variable (d : ModularConjugationData M Ω)

theorem commutator_norm_le_vector_defects (a b : Algebra M) :
    ‖(a*b-b*a).val Ω‖ ≤
      ‖a‖*‖b.val Ω-d.rightAction b Ω‖+
        ‖b.val (a.val Ω)-d.rightAction b (a.val Ω)‖ := by
  have he : (a*b-b*a).val Ω =
      a.val (b.val Ω-d.rightAction b Ω)-
        (b.val (a.val Ω)-d.rightAction b (a.val Ω)) := by
    have hc := congrArg (fun T : H →L[ℂ] H => T Ω) (d.rightAction_commute a b)
    change a.val (d.rightAction b Ω)=d.rightAction b (a.val Ω) at hc
    change a.val (b.val Ω)-b.val (a.val Ω)=_
    rw [map_sub,hc]
    abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add (a.val.le_opNorm _) le_rfl)

theorem bounded_symmetric_vector_witness
    (h : HaagerupCommutatorWitnesses d)
    (a : Algebra M) (hbal : a.val Ω=d.rightAction (star a) Ω)
    (hzero : productVectorState Ω a.val=0) (hnorm : ‖a.val Ω‖=1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : Algebra M,
      ‖b.val Ω‖+‖b.val (a.val Ω)‖ <
        12*‖b.val (a.val Ω)-d.rightAction b (a.val Ω)‖ ∧
      ‖b.val Ω-d.rightAction b Ω‖ <
        δ*‖b.val (a.val Ω)-d.rightAction b (a.val Ω)‖ := by
  let γ := min (δ/2) (1/(2*(‖a‖+1)))
  have hγ : 0 < γ := lt_min (by positivity) (by positivity)
  have hγδ : γ ≤ δ/2 := min_le_left _ _
  have ham : ‖a‖*γ ≤ 1/2 := by
    have hh := (le_div_iff₀ (show 0 < 2*(‖a‖+1) by positivity)).mp
      (show γ ≤ 1/(2*(‖a‖+1)) from min_le_right _ _)
    nlinarith
  obtain ⟨b,hsize,hdef⟩ := h a hbal hzero hnorm γ hγ
  let C := ‖(a*b-b*a).val Ω‖
  let D := ‖b.val (a.val Ω)-d.rightAction b (a.val Ω)‖
  have hC : C ≤ 2*D := by
    have hnorms := d.commutator_norm_le_vector_defects a b
    have he : ‖a‖*‖b.val Ω-d.rightAction b Ω‖ ≤ (1/2)*C := by
      calc
        _ ≤ ‖a‖*(γ*C) := mul_le_mul_of_nonneg_left hdef.le (norm_nonneg a)
        _ = (‖a‖*γ)*C := by ring
        _ ≤ (1/2)*C := mul_le_mul_of_nonneg_right ham (norm_nonneg _)
    change C ≤ _+D at hnorms
    linarith
  refine ⟨b,?_,?_⟩
  · change ‖b.val Ω‖+‖(b*a).val Ω‖ < 12*D
    exact hsize.trans_le (by linarith)
  · calc
      _ < γ*C := hdef
      _ ≤ (δ/2)*C := mul_le_mul_of_nonneg_right hγδ (norm_nonneg _)
      _ ≤ δ*D := by nlinarith

end ModularConjugationData

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SelfAdjointVectorWitness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Self-adjoint two-vector witnesses

The real and imaginary parts are controlled on the two specified vectors,
rather than in operator norm. This is the reduction used before the
spectral cuts in Haagerup's Lemma 2.10.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

namespace ModularConjugationData

variable {Ω : H} (d : ModularConjugationData M Ω)

theorem selfAdjoint_symmetric_vector_witness
    (h : HaagerupCommutatorWitnesses d)
    (a : Algebra M) (hbal : a.val Ω=d.rightAction (star a) Ω)
    (hzero : productVectorState Ω a.val=0) (hnorm : ‖a.val Ω‖=1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : Algebra M, IsSelfAdjoint b ∧
      ‖b.val Ω‖+‖b.val (a.val Ω)‖ <
        26*‖centralVectorDefect d.conjugation (a.val Ω) b.val‖ ∧
      ‖centralVectorDefect d.conjugation Ω b.val‖ <
        δ*‖centralVectorDefect d.conjugation (a.val Ω) b.val‖ := by
  let γ := min (δ/2) 1
  have hγ : 0 < γ := lt_min (by positivity) zero_lt_one
  obtain ⟨b,hsize,hdef⟩ := d.bounded_symmetric_vector_witness h a hbal hzero hnorm hγ
  have hη : d.conjugation (a.val Ω)=a.val Ω := by
    have he := d.rightAction_conjugation a Ω
    rw [d.fixes_vector] at he
    exact he.symm.trans hbal.symm
  obtain ⟨c,hc,hsizec,hdefc,hgapc⟩ := exists_selfAdjoint_two_vector_gap
    d.conjugation d.involutive Ω (a.val Ω) d.fixes_vector hη b
  have hdef' : ‖centralVectorDefect d.conjugation Ω b.val‖ <
      γ*‖centralVectorDefect d.conjugation (a.val Ω) b.val‖ := hdef
  have hsize' : ‖b.val Ω‖+‖b.val (a.val Ω)‖ <
      12*‖centralVectorDefect d.conjugation (a.val Ω) b.val‖ := hsize
  have hγ₁ : γ ≤ 1 := min_le_right _ _
  have hγδ : γ ≤ δ/2 := min_le_left _ _
  refine ⟨c,hc,?_,?_⟩
  · have hsmall : ‖centralVectorDefect d.conjugation Ω b.val‖ <
        ‖centralVectorDefect d.conjugation (a.val Ω) b.val‖ :=
      hdef'.trans_le (mul_le_of_le_one_left (norm_nonneg _) hγ₁)
    linarith
  · have he := mul_le_mul_of_nonneg_right hγδ
      (norm_nonneg (centralVectorDefect d.conjugation (a.val Ω) b.val))
    nlinarith

end ModularConjugationData

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HaagerupProjectionWitness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.mem_projectionFamilyRemainderSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Projection witnesses from the modular commutator premise

This is the bounded symmetric-vector case of Haagerup's Lemma 2.13.
Both estimates concern a genuine projection in the original algebra.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

private theorem two_vector_energy_bound {L R X D α : ℝ}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hX : 0 ≤ X) (hα : 0 < α)
    (hsize : L+R < 26*D) (hsmall : X < (α/106496)*D) :
    α*(L^2+R^2)+2*2048*L*X < α*2048/2*D^2 := by
  have hD : 0 < D := by linarith
  have hLD : L ≤ 26*D := by linarith
  have hsq := (sq_lt_sq₀ (add_nonneg hL hR) (by positivity : 0 ≤ 26*D)).mpr hsize
  have hmass : L^2+R^2 < 676*D^2 := by nlinarith [mul_nonneg hL hR]
  have hmassα := mul_lt_mul_of_pos_left hmass hα
  have hLX := mul_le_mul_of_nonneg_right hLD hX
  have hXD := mul_lt_mul_of_pos_left hsmall (by positivity : 0 < 26*D)
  have hterm : 2*2048*L*X < α*D^2 := by nlinarith
  nlinarith [mul_pos hα (sq_pos_of_pos hD)]

namespace ModularConjugationData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H} (d : ModularConjugationData M Ω)

theorem symmetric_vector_projection_witness
    (h : HaagerupCommutatorWitnesses d)
    (a : Algebra M) (hbal : a.val Ω=d.rightAction (star a) Ω)
    (hzero : productVectorState Ω a.val=0) (hnorm : ‖a.val Ω‖=1)
    {α : ℝ} (hα : 0 < α) :
    ∃ p : AlgebraProjection M,
      ‖p.val.val Ω‖^2+‖p.val.val (a.val Ω)‖^2 <
        2048*‖centralVectorDefect d.conjugation (a.val Ω) p.val.val‖^2 ∧
      ‖centralVectorDefect d.conjugation Ω p.val.val‖^2 <
        α*‖centralVectorDefect d.conjugation (a.val Ω) p.val.val‖^2 := by
  obtain ⟨b,hb,hsize,hsmall⟩ := d.selfAdjoint_symmetric_vector_witness
    h a hbal hzero hnorm (show 0 < α/106496 by positivity)
  have hDb (ζ : H) : centralVectorDefect d.conjugation ζ b.val=
      (b.val-conjugationOperator d.conjugation b.val) ζ := by
    rw [centralVectorDefect_apply,
      show star b.val=b.val from congrArg Subtype.val hb.star_eq]
    rfl
  apply exists_selfAdjoint_two_vector_projection d.conjugation d.involutive
    (d.right_mem le_rfl) b hb Ω (a.val Ω) d.fixes_vector hα (by norm_num)
  have he := two_vector_energy_bound (norm_nonneg (b.val Ω))
    (norm_nonneg (b.val (a.val Ω)))
    (norm_nonneg (centralVectorDefect d.conjugation Ω b.val)) hα hsize hsmall
  simpa only [hDb] using he

theorem symmetric_vector_nonzero_projection_witness
    (h : HaagerupCommutatorWitnesses d)
    (a : Algebra M) (hbal : a.val Ω=d.rightAction (star a) Ω)
    (hzero : productVectorState Ω a.val=0) (hnorm : ‖a.val Ω‖=1)
    {α : ℝ} (hα : 0 < α) :
    ∃ p : AlgebraProjection M, p.val ≠ 0 ∧
      ‖p.val.val Ω‖^2+‖p.val.val (a.val Ω)‖^2 <
        2048*‖centralVectorDefect d.conjugation (a.val Ω) p.val.val‖^2 ∧
      ‖centralVectorDefect d.conjugation Ω p.val.val‖^2 <
        α*‖centralVectorDefect d.conjugation (a.val Ω) p.val.val‖^2 := by
  obtain ⟨p,hp,hc⟩ := d.symmetric_vector_projection_witness h a hbal hzero hnorm hα
  refine ⟨p,?_,hp,hc⟩
  intro hz
  have hzv : p.val.val=0 := congrArg Subtype.val hz
  have he : (0 : ℝ) < 0 := by simpa only [hzv,map_zero,norm_zero,pow_two,mul_zero] using hc
  exact (lt_irrefl 0) he

end ModularConjugationData

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DominatedSymmetricWitness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Dominated symmetric vectors belong to the bounded modular core

The bounded commutant intertwiner becomes a left algebra element after
conjugation. Thus the constructed projection witnesses apply exactly to
every symmetric vector whose state is dominated by the reference state.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularConjugationData

variable (d : ModularConjugationData M Ω)

theorem exists_symmetric_algebra_vector_of_domination
    (hcyc : DenseRange (algebraVectorMap M Ω)) (η : H) (hη : d.conjugation η=η)
    (C : ℝ) (hdom : ∀ a : Algebra M, ‖a.val η‖ ≤ C*‖a.val Ω‖) :
    ∃ a : Algebra M, a.val Ω=η ∧ a.val Ω=d.rightAction (star a) Ω := by
  let R := dominatedVectorIntertwiner M Ω η
  have hRM : R ∈ M.commutant := dominatedVectorIntertwiner_commutant Ω η hcyc C hdom
  have hRv : R Ω=η := dominatedVectorIntertwiner_vector Ω η hcyc C hdom
  rw [← d.commutant] at hRM
  change R ∈ conjugationOperator d.conjugation '' (M : Set (H →L[ℂ] H)) at hRM
  obtain ⟨A,hAM,hAR⟩ := hRM
  let a : Algebra M := ⟨A,hAM⟩
  have hv : a.val Ω=η := by
    have he := congrArg d.conjugation hRv
    rw [← hAR] at he
    change d.conjugation (d.conjugation (A (d.conjugation Ω)))=d.conjugation η at he
    rw [d.fixes_vector,d.involutive,hη] at he
    exact he
  refine ⟨a,hv,?_⟩
  have he := d.rightAction_conjugation a Ω
  rw [d.fixes_vector,hv,hη] at he
  exact hv.trans he.symm

theorem dominated_symmetric_projection_witness_oai
    (h : HaagerupCommutatorWitnesses d)
    (hcyc : DenseRange (algebraVectorMap M Ω)) (η : H) (hη : d.conjugation η=η)
    (hunit : ‖η‖=1) (horth : inner ℂ Ω η=0)
    (C : ℝ) (hdom : ∀ a : Algebra M, ‖a.val η‖ ≤ C*‖a.val Ω‖)
    {α : ℝ} (hα : 0 < α) :
    ∃ p : AlgebraProjection M, p.val ≠ 0 ∧
      ‖p.val.val Ω‖^2+‖p.val.val η‖^2 <
        2048*‖centralVectorDefect d.conjugation η p.val.val‖^2 ∧
      ‖centralVectorDefect d.conjugation Ω p.val.val‖^2 <
        α*‖centralVectorDefect d.conjugation η p.val.val‖^2 := by
  obtain ⟨a,ha,hbal⟩ := d.exists_symmetric_algebra_vector_of_domination hcyc η hη C hdom
  have hzero : productVectorState Ω a.val=0 := by
    change inner ℂ Ω (a.val Ω)=0
    rwa [ha]
  have hnorm : ‖a.val Ω‖=1 := ha ▸ hunit
  obtain ⟨p,hp⟩ := d.symmetric_vector_nonzero_projection_witness h a hbal hzero hnorm hα
  rw [ha] at hp
  exact ⟨p,hp⟩

end ModularConjugationData

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.ModularConjugationData.dominated_symmetric_projection_witness_oai.{u_1} := @OAI.KadisonKastler.ModularConjugationData.dominated_symmetric_projection_witness_oai.{u_1}
