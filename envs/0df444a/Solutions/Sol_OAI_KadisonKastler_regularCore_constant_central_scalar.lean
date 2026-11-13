-- Prove2me | solution 1 for OAI.KadisonKastler.regularCore_constant_central_scalar
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:17:27.497329+00:00
-- url     : https://prove2.me/submissions/ea42c67c-10bc-42d5-9504-e74138ecbd93

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
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
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
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
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
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
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Tactic
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
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
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K024

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FixedPointGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fixed-point algebras and the common-action gap

The fixed algebra is an actual von Neumann algebra, defined as a commutant.
The scalar invariant mean constructed in `InvariantOperatorMean` averages
ordinary unit-ball approximants into fixed-point approximants without
increasing either their norm or their error. No existence of a scalar mean
or fixed-point averaging map is postulated here.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {G H : Type*} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem fixedPointAlgebra_le (U : G →* unitary (H →L[ℂ] H))
    (M : VonNeumannAlgebra H) : fixedPointAlgebra U M ≤ M :=
  fun T hT => ((mem_fixedPointAlgebra_iff U M T).mp hT).1

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreOperators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Operators on the actual regular Hilbert space

The regular core acts on `L²(ℝ,H)`, with a constant operator
representation and multiplication by a measurable unitary
field. The latter gives the gauge transformation used to write the core
embedding as a faithful conjugate of the constant representation.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

variable {D H : Type*} [MeasurableSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A finite positive-measure test set makes the constant representation
faithful, without requiring a finite total measure. -/
theorem regularConstantHom_injective (μ : Measure D) (s : Set D)
    (hs : MeasurableSet s) (hfin : μ s ≠ ∞) (hpos : μ s ≠ 0) :
    Function.Injective (regularConstantHom (H := H) μ) := by
  intro T S hTS
  apply ContinuousLinearMap.ext
  intro x
  let f : Lp H 2 μ := indicatorConstLp 2 hs hfin x
  have heq : regularConstantHom μ T f = regularConstantHom μ S f :=
    congrArg (fun R : Lp H 2 μ →L[ℂ] Lp H 2 μ => R f) hTS
  have hpoint : ∀ᵐ t ∂μ, t ∈ s → T x = S x := by
    filter_upwards [regularConstantHom_apply_ae μ T f,
      regularConstantHom_apply_ae μ S f,
      (indicatorConstLp_coeFn_mem (p := 2) (hs := hs) (hμs := hfin) (c := x))]
      with t hT hS hf
    intro ht
    rw [hf ht] at hT hS
    exact hT.symm.trans ((congrArg (fun v : Lp H 2 μ => v t) heq).trans hS)
  obtain ⟨t, ht, h⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (ae_restrict_of_ae hpoint)
  exact h ht

theorem real_regularConstantHom_injective :
    Function.Injective (regularConstantHom (H := H) (volume : Measure ℝ)) := by
  apply regularConstantHom_injective volume (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc
  · simp only [Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, ne_eq, ENNReal.one_ne_top,
      not_false_eq_true]
  · simp only [Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, ne_eq, _root_.one_ne_zero,
      not_false_eq_true]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete regular core and its first fixed-point inclusion

The tensor algebra is the commutant of the constant copy of `P'` on
`L²(ℝ,H)`. The regular core is the von Neumann algebra generated by the
concrete regular embedding and translations. Its generators lie in the
tensor algebra and are fixed by the common regular action. This proves
the first fixed-point inclusion without a crossed-product assumption.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem regularCoreAlgebra_le_tensor (P : VonNeumannAlgebra H)
    (hP : ∀ s T, T ∈ P → unitaryConj (U s) T ∈ P) :
    regularCoreAlgebra U hU P ≤ regularTensorAlgebra P :=
  (regularCoreAlgebra_le_fixed U hU P hP).trans (fixedPointAlgebra_le _ _)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded field multiplication and constant translation-fixed fields

Bounded measurable operator fields act on the actual vector-valued `L²`
space. Finite-measure indicator tests recover their coefficients, so this
action is faithful modulo almost-everywhere equality. A decomposable
operator commuting with every real translation is a constant operator.
No decomposability assertion for an arbitrary operator is assumed here.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Indicator tests recover each vector coefficient of an operator field
on a finite-measure set. -/
theorem RepresentsOperatorField.eval_eq_ae_on {μ : Measure X}
    {F G : X → H →L[ℂ] H} {T : Lp H 2 μ →L[ℂ] Lp H 2 μ}
    (hF : RepresentsOperatorField μ F T) (hG : RepresentsOperatorField μ G T)
    {s : Set X} (hs : MeasurableSet s) (hfinite : μ s ≠ ∞) (ξ : H) :
    ∀ᵐ t ∂μ, t ∈ s → F t ξ = G t ξ := by
  let f : Lp H 2 μ := indicatorConstLp 2 hs hfinite ξ
  filter_upwards [hF f, hG f,
    (indicatorConstLp_coeFn_mem (p := 2) (hs := hs) (hμs := hfinite) (c := ξ))]
    with t hf hg hξ
  intro ht
  rw [hξ ht] at hf hg
  exact hf.symm.trans hg

omit [CompleteSpace H] in
/-- Equality of actual real-line multiplication operators recovers each
vector value almost everywhere. -/
theorem RepresentsOperatorField.eval_eq_ae_real
    {F G : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (hG : RepresentsOperatorField volume G T)
    (ξ : H) : (fun t => F t ξ) =ᵐ[volume] fun t => G t ξ := by
  have hall : ∀ᵐ t : ℝ ∂volume, ∀ n : ℕ,
      t ∈ Set.Icc (-(n : ℝ)) (n : ℝ) → F t ξ = G t ξ := by
    apply ae_all_iff.mpr
    intro n
    exact hF.eval_eq_ae_on hG measurableSet_Icc (by simp) ξ
  filter_upwards [hall] with t ht
  obtain ⟨n, hn⟩ := exists_nat_gt |t|
  exact ht n (Set.mem_Icc.mpr (abs_le.mp hn.le))

omit [CompleteSpace H] in
/-- On a separable Hilbert space, equality of multiplication operators
recovers the entire field almost everywhere. -/
theorem RepresentsOperatorField.field_eq_ae_real [TopologicalSpace.SeparableSpace H]
    {F G : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (hG : RepresentsOperatorField volume G T) :
    F =ᵐ[volume] G := by
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq (α := H)
  have hall : ∀ᵐ t : ℝ ∂volume, ∀ n : ℕ, F t (v n) = G t (v n) :=
    ae_all_iff.mpr fun n => hF.eval_eq_ae_real hG (v n)
  filter_upwards [hall] with t ht
  apply ContinuousLinearMap.ext
  exact congrFun (hv.equalizer (F t).continuous (G t).continuous (funext ht))

/-- Translation conjugates an actual multiplication operator by shifting
its field. -/
theorem RepresentsOperatorField.real_translate
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (s : Multiplicative ℝ) :
    RepresentsOperatorField volume (fun t => F (t + s.toAdd))
      (unitaryConj (regularRightTranslation (H := H) s) T) := by
  intro f
  have hstar : (star (regularRightTranslation (H := H) s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (regularRightTranslation (H := H) s⁻¹ :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
    rw [map_inv]
    rfl
  unfold unitaryConj
  rw [hstar]
  filter_upwards [regularRightTranslation_apply_ae s
      (T ((regularRightTranslation (H := H) s⁻¹ :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)),
    (measurePreserving_add_right volume s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (hF ((regularRightTranslation (H := H) s⁻¹ :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)),
    (measurePreserving_add_right volume s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (regularRightTranslation_apply_ae s⁻¹ f)] with t hρ hFshift hback
  simp only [Function.comp_def] at hFshift hback
  change (regularRightTranslation (H := H) s :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (T ((regularRightTranslation (H := H) s⁻¹ :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) t = _
  rw [hρ, hFshift, hback]
  simp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreIntersection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The joint fixed algebra in the concrete regular representation

The reverse tensor membership is proved from the actual multiplier
representation. The joint fixed-point identification then uses only the
two separate published spectral and diagonal decomposition inputs.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

include hU in
theorem regularCoreEmbedding_field_continuous (A : H →L[ℂ] H) (ξ : H) :
    Continuous (fun t : ℝ =>
      unitaryConj (star (U (Multiplicative.ofAdd t))) A ξ) := by
  have hs (η : H) : Continuous (fun t : ℝ =>
      (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) η) := by
    have he : (fun t : ℝ => (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) η) =
        (fun t : ℝ => (U (Multiplicative.ofAdd (-t)) : H →L[ℂ] H) η) := by
      funext t
      exact congrArg (fun v : unitary (H →L[ℂ] H) => (v : H →L[ℂ] H) η)
        (regularGroup_star_eq U t)
    rw [he]
    exact (hU η).comp continuous_neg
  simpa only [unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp] using
    continuous_unitary_field_apply (fun t : ℝ => star (U (Multiplicative.ofAdd t)))
      hs (fun t : ℝ => A ((U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
      (A.continuous.comp (hU ξ))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialFieldPeriods
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Tensor coefficients turn central commutation into frequency periods

In Fourier coordinates a site eigenoperator is a constant second-leg
operator followed by a frequency translation. Commuting with it forces
an actual first-leg coefficient field to have that period. Two
incommensurable site frequencies therefore make the field constant.
-/

namespace KadisonKastler

open MeasureTheory UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Commutation with a constant coefficient followed by translation gives
an almost-everywhere field intertwining identity. -/
theorem RepresentsOperatorField.intertwine_translation
    [TopologicalSpace.SeparableSpace E]
    {F : ℝ → E →L[ℂ] E}
    {T : RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E}
    (hF : RepresentsOperatorField volume F T) (b : E →L[ℂ] E) (s : ℝ)
    (hcomm : Commute T (regularConstantHom volume b *
      (regularRightTranslation (H := E) (Multiplicative.ofAdd s) :
        RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E))) :
    ∀ᵐ t ∂volume, F t * b = b * F (t + s) := by
  let R := regularRightTranslation (H := E) (Multiplicative.ofAdd s)
  change Commute T (regularConstantHom volume b *
    (R : RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E)) at hcomm
  have he : T * regularConstantHom volume b = regularConstantHom volume b *
      unitaryConj R T := by
    have h := congrArg (fun S : RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E =>
      S * (star R : RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E)) hcomm.eq
    simpa only [mul_assoc, Unitary.mul_star_self_of_mem R.property, mul_one,
      unitaryConj] using h
  have hl : RepresentsOperatorField volume (fun t => F t * b)
      (T * regularConstantHom volume b) := by
    intro f
    filter_upwards [hF (regularConstantHom volume b f),
      regularConstantHom_apply_ae volume b f] with t ht hb
    change T (regularConstantHom volume b f) t = _
    rw [ht, hb]
    rfl
  have hr : RepresentsOperatorField volume (fun t => b * F (t + s))
      (T * regularConstantHom volume b) := by
    rw [he]
    intro f
    filter_upwards [regularConstantHom_apply_ae volume b (unitaryConj R T f),
      hF.real_translate (Multiplicative.ofAdd s) f] with t hb ht
    change regularConstantHom volume b (unitaryConj R T f) t = _
    rw [hb, ht]
    rfl
  exact hl.field_eq_ae_real hr

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularFieldMembership
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable tests recover fiberwise algebra membership

A represented measurable field inherits commutation with a bounded set
of constant operators on one common conull set. Countable strong tests
justify the interchange of the almost-everywhere and operator quantifiers.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Constant commutation descends to a represented field almost everywhere. -/
theorem RepresentsOperatorField.commute_constant_ae
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (b : H →L[ℂ] H)
    (hcomm : Commute T (regularConstantHom volume b)) :
    ∀ᵐ t ∂volume, Commute (F t) b := by
  have he := hF.intertwine_translation b 0 (by simpa using hcomm)
  filter_upwards [he] with t ht
  change F t * b = b * F t
  simpa only [add_zero] using ht

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreCentralField
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourier fields of central elements in the actual regular core -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
  (P : VonNeumannAlgebra H)

/-- Commutation with a constant operator in the regular representation
recovers commutation at time zero by continuity of the modular action. -/
theorem constant_commutes_regularEmbedding
    (A x : H →L[ℂ] H)
    (hc : Commute (regularConstantHom volume A) (regularCoreEmbedding U hU x)) :
    Commute A x := by
  have hf : RepresentsOperatorField volume
      (fun t : ℝ => unitaryConj (star (U (Multiplicative.ofAdd t))) x)
      (regularCoreEmbedding U hU x) := by
    intro f
    simpa only [unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp]
      using regularCoreEmbedding_apply_ae U hU x f
  have ha := hf.commute_constant_ae A hc.symm
  change A * x = x * A
  ext ξ
  have hae : (fun t : ℝ =>
      A (unitaryConj (star (U (Multiplicative.ofAdd t))) x ξ)) =ᵐ[volume]
      (fun t : ℝ => unitaryConj (star (U (Multiplicative.ofAdd t))) x (A ξ)) := by
    filter_upwards [ha] with t ht
    exact congrArg (fun B : H →L[ℂ] H => B ξ) ht.eq.symm
  have he := Measure.eq_of_ae_eq hae
    (A.continuous.comp (regularCoreEmbedding_field_continuous U hU x ξ))
    (regularCoreEmbedding_field_continuous U hU x (A ξ))
  have hzero := congrFun he 0
  simpa only [ofAdd_zero, map_one, star_one, unitaryConj_one,
    mul_apply_eq_comp] using hzero

/-- A constant central operator in the core of a factor is scalar. -/
theorem regularCore_constant_central_scalar_oai
    (hP : ∀ s x, x ∈ P → unitaryConj (U s) x ∈ P) (hfactor : ScalarCenter P)
    (A : H →L[ℂ] H)
    (hA : regularConstantHom volume A ∈ regularCoreAlgebra U hU P)
    (hcentral : ∀ S ∈ regularCoreAlgebra U hU P,
      S * regularConstantHom volume A = regularConstantHom volume A * S) :
    ∃ c : ℂ, regularConstantHom volume A = c •
      (1 : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  have hAmem : A ∈ P := by
    rw [← P.commutant_commutant]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro b hb
    have he := (mem_regularTensorAlgebra_iff P _).mp
      (regularCoreAlgebra_le_tensor U hU P hP hA) b hb
    apply real_regularConstantHom_injective
    simpa only [map_mul] using he
  have hac : ∀ x ∈ P, x * A = A * x := by
    intro x hx
    exact (constant_commutes_regularEmbedding U hU A x
      (hcentral _ (regularCoreEmbedding_mem_core U hU P hx)).symm).eq.symm
  obtain ⟨c, hc⟩ := hfactor A hAmem hac
  refine ⟨c, ?_⟩
  rw [hc, map_smul, map_one]

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.regularCore_constant_central_scalar_oai.{u} := @OAI.KadisonKastler.regularCore_constant_central_scalar_oai.{u}
