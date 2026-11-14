-- Prove2me | solution 1 for OAI.KadisonKastler.regularCoreConjugation_commutant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:58:02.199632+00:00
-- url     : https://prove2.me/submissions/dab8e56d-b4ba-45f0-a958-a5c0fd679415

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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
import Mathlib.Analysis.InnerProductSpace.Basic
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
import Mathlib.Analysis.Normed.Group.Tannery
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
import Mathlib.LinearAlgebra.Countable
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
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
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
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K028
import Definitions.Def_Q260K030
import Definitions.Def_Q260K067

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreConjugateGenerators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Conjugation of the regular generators

The regular modular conjugation sends the represented algebra to the
constant right algebra. Its formula is proved on actual L2 classes.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (J : H ≃ₗᵢ⋆[ℂ] H)
  (hJU : ∀ t x, J ((U t : H →L[ℂ] H) x) = (U t : H →L[ℂ] H) (J x))

private theorem unitary_star_apply_apply (v : unitary (H →L[ℂ] H)) (x : H) :
    (star v : H →L[ℂ] H) ((v : H →L[ℂ] H) x) = x :=
  congrArg (fun A : H →L[ℂ] H => A x) (Unitary.star_mul_self_of_mem v.property)

include hJU in
theorem regularCoreConjugation_embedding (a : H →L[ℂ] H) :
    conjugationOperator (regularCoreConjugation U hU J) (regularCoreEmbedding U hU a) =
      regularConstantHom volume (conjugationOperator J a) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularCoreConjugation_apply_ae U hU J
      (regularCoreEmbedding U hU a (regularCoreConjugation U hU J f)),
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq_comp
      (regularCoreEmbedding_apply_ae U hU a (regularCoreConjugation U hU J f)),
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq_comp
      (regularCoreConjugation_apply_ae U hU J f),
    regularConstantHom_apply_ae volume (conjugationOperator J a) f]
    with t ho ha hc hr
  simp only [Function.comp_def, neg_neg] at ha hc
  change (regularCoreConjugation U hU J
    (regularCoreEmbedding U hU a (regularCoreConjugation U hU J f))) t = _
  have hneg (x : H) : (U (Multiplicative.ofAdd (-t)) : H →L[ℂ] H)
      ((U (Multiplicative.ofAdd t) : H →L[ℂ] H) x) = x := by
    simpa only [← Unitary.coe_star, regularGroup_star_eq] using
      unitary_star_apply_apply (U (Multiplicative.ofAdd t)) x
  rw [ho, ha, hc]
  simp only [← Unitary.coe_star, regularGroup_star_eq U (-t), neg_neg]
  rw [hneg, hJU]
  simp only [Unitary.coe_star]
  rw [unitary_star_apply_apply, hr]
  rfl

include hJU in
theorem regularCoreConjugation_translation (hJ : Function.Involutive J) (s : ℝ) :
    conjugationOperator (regularCoreConjugation U hU J)
      (regularRightTranslation (H := H) (Multiplicative.ofAdd s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (regularCoreAction U (Multiplicative.ofAdd (-s)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  have hshift : MeasurePreserving (fun t : ℝ => -t + s) volume volume :=
    (measurePreserving_add_right volume s).comp (Measure.measurePreserving_neg volume)
  have hproduct (t : ℝ) :
      (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) *
        (U (Multiplicative.ofAdd (-(-t + s))) : H →L[ℂ] H) =
      (U (Multiplicative.ofAdd (-s)) : H →L[ℂ] H) := by
    have he : U (Multiplicative.ofAdd (-t)) * U (Multiplicative.ofAdd (-(-t + s))) =
        U (Multiplicative.ofAdd (-s)) := by
      rw [← map_mul]
      congr 1
      change -t + -(-t + s) = -s
      ring
    simp only [← Unitary.coe_star, regularGroup_star_eq]
    exact congrArg Subtype.val he
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularCoreConjugation_apply_ae U hU J
      ((regularRightTranslation (H := H) (Multiplicative.ofAdd s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularCoreConjugation U hU J f)),
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq_comp
      (regularRightTranslation_apply_ae (Multiplicative.ofAdd s)
        (regularCoreConjugation U hU J f)),
    hshift.quasiMeasurePreserving.ae_eq_comp (regularCoreConjugation_apply_ae U hU J f),
    regularCoreAction_apply_ae U (Multiplicative.ofAdd (-s)) f]
    with t ho ht hc hr
  simp only [Function.comp_def, toAdd_ofAdd] at ht hc hr
  change (regularCoreConjugation U hU J
    ((regularRightTranslation (H := H) (Multiplicative.ofAdd s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularCoreConjugation U hU J f))) t = _
  rw [ho, ht, hc]
  simp only [← Unitary.coe_star, regularGroup_star_eq U (-t + s)]
  rw [hJU, hJ, hr]
  change ((star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) *
    (U (Multiplicative.ofAdd (-(-t + s))) : H →L[ℂ] H)) (f (-(-t + s))) = _
  rw [hproduct]
  congr 2
  ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreStandardConjugation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The commutant identity for the regular modular conjugation -/

namespace KadisonKastler

open MeasureTheory Generator

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hJU : ∀ t x, J ((U t : H →L[ℂ] H) x) = (U t : H →L[ℂ] H) (J x))
  (M : VonNeumannAlgebra H)
  (hJM : conjugateRightAlgebra J hJ M = M.commutant)

include hJM in
private theorem right_constant_mem (a : H →L[ℂ] H) (ha : a ∈ M) :
    conjugationOperator J a ∈ M.commutant := by
  rw [← hJM]
  exact ⟨a, ha, rfl⟩

include hJM in
private theorem exists_left_of_right (z : H →L[ℂ] H) (hz : z ∈ M.commutant) :
    ∃ a ∈ M, conjugationOperator J a = z := by
  rw [← hJM] at hz
  exact hz

include hJU hJM in
theorem regularCoreConjugation_image :
    conjugateRightAlgebra (regularCoreConjugation U hU J)
      (regularCoreConjugation_involutive U hU J hJ hJU) (regularCoreAlgebra U hU M) =
      regularCommutantAlgebra U M := by
  let C := regularCoreConjugation U hU J
  have hC := regularCoreConjugation_involutive U hU J hJ hJU
  let R := regularCommutantAlgebra U M
  have hpre : regularCoreAlgebra U hU M ≤ conjugateRightAlgebra C hC R := by
    apply generatedVonNeumannAlgebra_le_of_le
    apply StarAlgebra.adjoin_le
    rintro a (⟨x, hx, rfl⟩ | ⟨s, rfl⟩)
    · change regularCoreEmbedding U hU x ∈ conjugateRightAlgebra C hC R
      refine ⟨conjugationOperator C (regularCoreEmbedding U hU x), ?_,
        conjugationOperator_twice C hC _⟩
      rw [regularCoreConjugation_embedding U hU J hJU]
      exact subset_generatedVonNeumannAlgebra _ (StarAlgebra.subset_adjoin ℂ _
        (Or.inl ⟨conjugationOperator J x, right_constant_mem J hJ M hJM x hx, rfl⟩))
    · change (regularRightTranslation (H := H) s :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) ∈ conjugateRightAlgebra C hC R
      refine ⟨conjugationOperator C (regularRightTranslation (H := H) s), ?_,
        conjugationOperator_twice C hC _⟩
      change conjugationOperator (regularCoreConjugation U hU J)
        (regularRightTranslation (H := H) (Multiplicative.ofAdd s.toAdd)) ∈ R
      rw [regularCoreConjugation_translation U hU J hJU hJ]
      exact subset_generatedVonNeumannAlgebra _
        (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨Multiplicative.ofAdd (-s.toAdd), rfl⟩))
  apply le_antisymm
  · intro T hT
    rcases hT with ⟨a, ha, rfl⟩
    rcases hpre ha with ⟨b, hb, he⟩
    have hback := congrArg (conjugationOperator C) he
    rw [conjugationOperator_twice C hC] at hback
    exact hback ▸ hb
  · apply generatedVonNeumannAlgebra_le_of_le
    apply StarAlgebra.adjoin_le
    rintro a (⟨z, hz, rfl⟩ | ⟨s, rfl⟩)
    · obtain ⟨x, hx, rfl⟩ := exists_left_of_right J hJ M hJM z hz
      change regularConstantHom volume (conjugationOperator J x) ∈
        conjugateRightAlgebra C hC (regularCoreAlgebra U hU M)
      exact ⟨regularCoreEmbedding U hU x, regularCoreEmbedding_mem_core U hU M hx,
        regularCoreConjugation_embedding U hU J hJU x⟩
    · change (regularCoreAction U s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) ∈
        conjugateRightAlgebra C hC (regularCoreAlgebra U hU M)
      refine ⟨(regularRightTranslation (H := H) (Multiplicative.ofAdd (-s.toAdd)) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H),
        regularTranslation_mem_core U hU M _, ?_⟩
      simpa only [neg_neg, ofAdd_toAdd] using
        regularCoreConjugation_translation U hU J hJU hJ (-s.toAdd)

include hJU hJM in
theorem regularCoreConjugation_commutant_oai [TopologicalSpace.SeparableSpace H]
    (hn : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M) :
    conjugateRightAlgebra (regularCoreConjugation U hU J)
      (regularCoreConjugation_involutive U hU J hJ hJU) (regularCoreAlgebra U hU M) =
      (regularCoreAlgebra U hU M).commutant := by
  rw [regularCoreConjugation_image U hU J hJ hJU M hJM]
  exact (publishedRegularCommutant H U hU M hn).symm

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.regularCoreConjugation_commutant_oai.{u} := @OAI.KadisonKastler.regularCoreConjugation_commutant_oai.{u}
