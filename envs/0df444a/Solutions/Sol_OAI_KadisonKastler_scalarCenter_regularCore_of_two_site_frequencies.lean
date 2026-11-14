-- Prove2me | solution 1 for OAI.KadisonKastler.scalarCenter_regularCore_of_two_site_frequencies
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:26:21.224277+00:00
-- url     : https://prove2.me/submissions/27dbb1eb-79cd-43d6-8a3c-283ba2d1f11b

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
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Continuous
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
import Definitions.Def_Q260K064
import Theorems.Thm_OAI_KadisonKastler_first_leg_field_of_product_centralizer
import Theorems.Thm_OAI_KadisonKastler_regularCore_central_fourier_field
import Theorems.Thm_OAI_KadisonKastler_regularCore_constant_central_scalar
import Theorems.Thm_OAI_KadisonKastler_scalarCenter_spatialProduct_of_local_swaps

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DirectIntegralConjugacy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Assembling fiber conjugacies on the actual direct-integral space

`OperatorFieldDecomposition` records the decomposition and reconstruction
properties of a given constant-fiber direct integral. It is data, not a
published theorem or an existence assertion. The assembly argument below
uses actual multiplication unitaries on `L²(X,H)`.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem RepresentsOperatorField.unique {μ : Measure X} {F : X → H →L[ℂ] H}
    {T S : Lp H 2 μ →L[ℂ] Lp H 2 μ}
    (hT : RepresentsOperatorField μ F T) (hS : RepresentsOperatorField μ F S) : T = S := by
  apply ContinuousLinearMap.ext
  intro f
  exact Lp.ext ((hT f).trans (hS f).symm)

end

end KadisonKastler

end OAI
end

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
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreInvariant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Translation-invariant measurable fields are constant

For each translation the exceptional null set may differ. Fubini and the
measure-preserving shear `(s,t) ↦ (s-t,t)` nevertheless give a single
almost-everywhere constant representative. The operator-valued version
uses only countably many dense Hilbert coefficients.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

/-- A measurable scalar function invariant under every real translation
as an almost-everywhere class is almost everywhere constant. -/
theorem measurable_real_translation_invariant_const (f : ℝ → ℂ)
    (hf : Measurable f)
    (htrans : ∀ s : ℝ, (fun t => f (t + s)) =ᵐ[volume] f) :
    ∃ c : ℂ, f =ᵐ[volume] fun _ => c := by
  have hm : MeasurableSet {p : ℝ × ℝ | f (p.1 + p.2) = f p.2} :=
    measurableSet_eq_fun (hf.comp (measurable_fst.add measurable_snd))
      (hf.comp measurable_snd)
  have hp : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), f (p.1 + p.2) = f p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ)) hm).mpr
    apply Eventually.of_forall
    intro s
    change ∀ᵐ y : ℝ ∂(volume : Measure ℝ), f (s + y) = f y
    filter_upwards [htrans s] with t ht
    simpa only [add_comm] using ht
  have hp' : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), f p.1 = f p.2 := by
    have h := (measurePreserving_sub_prod (volume : Measure ℝ) volume).quasiMeasurePreserving.ae hp
    simpa only [sub_add_cancel] using h
  obtain ⟨s, hs⟩ := (Measure.ae_ae_of_ae_prod hp').exists
  exact ⟨f s, hs.mono fun _ h => h.symm⟩

/-- The same conclusion for a scalar almost-everywhere measurable class. -/
theorem aestronglyMeasurable_real_translation_invariant_const (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f volume)
    (htrans : ∀ s : ℝ, (fun t => f (t + s)) =ᵐ[volume] f) :
    ∃ c : ℂ, f =ᵐ[volume] fun _ => c := by
  have hmk (s : ℝ) : (fun t => hf.mk f (t + s)) =ᵐ[volume] hf.mk f := by
    have hshift := (measurePreserving_add_right (volume : Measure ℝ) s).quasiMeasurePreserving.ae_eq_comp
      hf.ae_eq_mk
    filter_upwards [hshift, htrans s, hf.ae_eq_mk] with t hshift ht hbase
    exact hshift.symm.trans (ht.trans hbase)
  obtain ⟨c, hc⟩ := measurable_real_translation_invariant_const
    (hf.mk f) hf.measurable_mk hmk
  exact ⟨c, hf.ae_eq_mk.trans hc⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H]

/-- Scalar translation invariance of a weakly measurable operator field
implies a single almost-everywhere constant bounded operator. No common
exceptional set for the original uncountable family of translations is
required. -/
theorem operatorField_real_translation_invariant_const
    (F : ℝ → H →L[ℂ] H)
    (hF : ∀ ξ η : H, AEStronglyMeasurable
      (fun t => inner ℂ η (F t ξ)) volume)
    (htrans : ∀ (s : ℝ) (ξ η : H),
      (fun t => inner ℂ η (F (t + s) ξ)) =ᵐ[volume]
        fun t => inner ℂ η (F t ξ)) :
    ∃ T : H →L[ℂ] H, F =ᵐ[volume] fun _ => T := by
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq (α := H)
  have hex (i j : ℕ) := aestronglyMeasurable_real_translation_invariant_const
    (fun t => inner ℂ (v i) (F t (v j))) (hF (v j) (v i))
    (fun s => htrans s (v j) (v i))
  choose c hc using hex
  have hall : ∀ᵐ t : ℝ ∂volume, ∀ i j : ℕ,
      inner ℂ (v i) (F t (v j)) = c i j :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hc i j
  obtain ⟨t₀, ht₀⟩ := hall.exists
  refine ⟨F t₀, hall.mono fun t ht => ?_⟩
  apply ContinuousLinearMap.ext
  have he : (fun ξ => F t ξ) = (fun ξ => F t₀ ξ) := by
    apply hv.equalizer (F t).continuous (F t₀).continuous
    funext j
    exact hv.eq_of_inner_right ℂ (fun i => (ht i j).trans (ht₀ i j).symm)
  exact congrFun he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- An actually decomposable operator fixed by every translation is a
constant operator. Decomposability itself is not posited for arbitrary
operators. -/
theorem constant_of_regularField_translation_fixed [TopologicalSpace.SeparableSpace H]
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume)
    (hfixed : ∀ s, unitaryConj (regularRightTranslation (H := H) s) T = T) :
    ∃ A : H →L[ℂ] H, F =ᵐ[volume] (fun _ => A) ∧ T = regularConstantHom volume A := by
  have hshift (s : ℝ) : (fun t => F (t + s)) =ᵐ[volume] F := by
    have h := hF.real_translate (Multiplicative.ofAdd s)
    rw [hfixed] at h
    exact h.field_eq_ae_real hF
  have hcoeff (s : ℝ) (ξ η : H) :
      (fun t => inner ℂ η (F (t + s) ξ)) =ᵐ[volume] fun t => inner ℂ η (F t ξ) :=
    (hshift s).mono fun _ h => congrArg (fun A : H →L[ℂ] H => inner ℂ η (A ξ)) h
  obtain ⟨A, hA⟩ := operatorField_real_translation_invariant_const F
    (fun ξ η => (hmeas ξ).const_inner (c := η)) hcoeff
  refine ⟨A, hA, hF.unique ?_⟩
  intro f
  filter_upwards [regularConstantHom_apply_ae volume A f, hA] with t ht hAt
  exact ht.trans (congrArg (fun B : H →L[ℂ] H => B (f t)) hAt.symm)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreDensePeriods
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Dense periods of bounded regular coefficient fields

Strong continuity of translations on the actual `L²` space extends
commutation from any dense family of translations to all translations.
Consequently a bounded measurable field with dense periods is constant
almost everywhere. In particular, two incommensurable scalar periods
suffice, as required by the two-frequency modular-core argument.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A bounded operator commuting with a dense set of translations commutes
with every translation. -/
theorem regularTranslation_commute_of_dense
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    {S : Set ℝ} (hS : Dense S)
    (hcomm : ∀ s ∈ S, Commute T
      (regularRightTranslation (H := H) (Multiplicative.ofAdd s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) (s : ℝ) :
    Commute T
      (regularRightTranslation (H := H) (Multiplicative.ofAdd s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  change T * _ = _ * T
  apply ContinuousLinearMap.ext
  intro f
  change T (regularTranslateApply s f) = regularTranslateApply s (T f)
  exact hS.induction
    (fun t ht => congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => A f)
      (hcomm t ht).eq)
    (isClosed_eq (T.continuous.comp (continuous_regularTranslateApply f))
      (continuous_regularTranslateApply (T f))) s

/-- A decomposable operator fixed by a dense set of translations has an
almost-everywhere constant field. -/
theorem constant_of_regularField_dense_translation_fixed
    [TopologicalSpace.SeparableSpace H]
    {F : ℝ → H →L[ℂ] H}
    {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume)
    {S : Set ℝ} (hS : Dense S)
    (hfixed : ∀ s ∈ S, unitaryConj
      (regularRightTranslation (H := H) (Multiplicative.ofAdd s)) T = T) :
    ∃ A : H →L[ℂ] H, F =ᵐ[volume] (fun _ => A) ∧
      T = regularConstantHom volume A := by
  apply constant_of_regularField_translation_fixed hF hmeas
  intro s
  have hc : Commute T
      (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
    regularTranslation_commute_of_dense T hS (fun t ht =>
      ((commute_unitary_iff_star_right_conjugate
        (regularRightTranslation (H := H) (Multiplicative.ofAdd t)).property).mpr
          (hfixed t ht)).symm) s.toAdd
  exact (commute_unitary_iff_star_right_conjugate
    (regularRightTranslation (H := H) s).property).mp hc.symm

/-- Bounded measurable operator fields with a dense set of periods are
constant almost everywhere. -/
theorem bounded_operatorField_dense_periods_const
    [TopologicalSpace.SeparableSpace H]
    (F : ℝ → H →L[ℂ] H)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume)
    (C : ℝ) (hbound : ∀ᵐ t ∂volume, ‖F t‖ ≤ C)
    {S : Set ℝ} (hS : Dense S)
    (hperiod : ∀ s ∈ S, (fun t => F (t + s)) =ᵐ[volume] F) :
    ∃ A : H →L[ℂ] H, F =ᵐ[volume] fun _ => A := by
  let T := regularFieldOperator volume F hmeas C hbound
  have hT : RepresentsOperatorField volume F T :=
    regularFieldOperator_represents volume F hmeas C hbound
  have hfixed (s : ℝ) (hs : s ∈ S) : unitaryConj
      (regularRightTranslation (H := H) (Multiplicative.ofAdd s)) T = T := by
    apply RepresentsOperatorField.unique (F := F) ?_ hT
    intro f
    filter_upwards [hT.real_translate (Multiplicative.ofAdd s) f, hperiod s hs]
      with t ht hp
    exact ht.trans (congrArg (fun A : H →L[ℂ] H => A (f t)) hp)
  obtain ⟨A, hA, _⟩ := constant_of_regularField_dense_translation_fixed hT hmeas hS hfixed
  exact ⟨A, hA⟩

/-- Scalar bounded coefficient fields are a special case of the actual
operator-field construction. -/
theorem bounded_scalar_dense_periods_const
    (f : ℝ → ℂ) (hmeas : AEStronglyMeasurable f volume)
    (C : ℝ) (hbound : ∀ᵐ t ∂volume, ‖f t‖ ≤ C)
    {S : Set ℝ} (hS : Dense S)
    (hperiod : ∀ s ∈ S, (fun t => f (t + s)) =ᵐ[volume] f) :
    ∃ c : ℂ, f =ᵐ[volume] fun _ => c := by
  let F : ℝ → ℂ →L[ℂ] ℂ := fun t => f t • 1
  have hFmeas (ξ : ℂ) : AEStronglyMeasurable (fun t => F t ξ) volume := by
    simpa only [F, smul_apply, one_apply_eq_self] using hmeas.smul_const ξ
  have hFbound : ∀ᵐ t ∂volume, ‖F t‖ ≤ C := by
    filter_upwards [hbound] with t ht
    simpa only [F, norm_smul, norm_one, mul_one] using ht
  have hFperiod : ∀ s ∈ S, (fun t => F (t + s)) =ᵐ[volume] F := by
    intro s hs
    exact (hperiod s hs).mono fun t ht => congrArg (fun z : ℂ => z • (1 : ℂ →L[ℂ] ℂ)) ht
  obtain ⟨A, hA⟩ := bounded_operatorField_dense_periods_const F hFmeas C hFbound hS hFperiod
  refine ⟨A 1, hA.mono fun t ht => ?_⟩
  have he := congrArg (fun B : ℂ →L[ℂ] ℂ => B 1) ht
  simpa only [F, smul_apply, one_apply_eq_self, smul_eq_mul, mul_one] using he

/-- Two periods with irrational ratio force any essentially bounded
measurable scalar field to be constant almost everywhere. -/
theorem bounded_scalar_two_periods_const
    (f : ℝ → ℂ) (hmeas : AEStronglyMeasurable f volume)
    (C : ℝ) (hbound : ∀ᵐ t ∂volume, ‖f t‖ ≤ C)
    {a b : ℝ} (hirr : Irrational (a / b))
    (ha : (fun t => f (t + a)) =ᵐ[volume] f)
    (hb : (fun t => f (t + b)) =ᵐ[volume] f) :
    ∃ c : ℂ, f =ᵐ[volume] fun _ => c := by
  have hle : AddSubgroup.closure {a, b} ≤ scalarAEPeriods f := by
    apply (AddSubgroup.closure_le (scalarAEPeriods f)).mpr
    intro s hs
    rcases Set.mem_insert_iff.mp hs with h | h
    · subst s
      exact ha
    · have he : s = b := Set.mem_singleton_iff.mp h
      subst s
      exact hb
  have hd : Dense (AddSubgroup.closure {a, b} : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr hirr
  exact bounded_scalar_dense_periods_const f hmeas C hbound hd (fun s hs => hle hs)

omit [CompleteSpace H] in
/-- Two incommensurable periods scalarize an entire bounded measurable
operator field, with one common exceptional null set. -/
theorem bounded_operatorField_two_periods_const
    [TopologicalSpace.SeparableSpace H]
    (F : ℝ → H →L[ℂ] H)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume)
    (C : ℝ) (hbound : ∀ᵐ t ∂volume, ‖F t‖ ≤ C)
    {a b : ℝ} (hirr : Irrational (a / b))
    (ha : (fun t => F (t + a)) =ᵐ[volume] F)
    (hb : (fun t => F (t + b)) =ᵐ[volume] F) :
    ∃ A : H →L[ℂ] H, F =ᵐ[volume] fun _ => A := by
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq (α := H)
  have hcoeff (ξ η : H) : ∃ c : ℂ,
      (fun t => inner ℂ η (F t ξ)) =ᵐ[volume] fun _ => c := by
    apply bounded_scalar_two_periods_const
      (fun t => inner ℂ η (F t ξ)) ((hmeas ξ).const_inner (c := η))
      (‖η‖ * (C * ‖ξ‖)) ?_ hirr
      (ha.mono fun _ h => congrArg (fun T : H →L[ℂ] H => inner ℂ η (T ξ)) h)
      (hb.mono fun _ h => congrArg (fun T : H →L[ℂ] H => inner ℂ η (T ξ)) h)
    filter_upwards [hbound] with t ht
    exact (norm_inner_le_norm η (F t ξ)).trans
      (mul_le_mul_of_nonneg_left
        (((F t).le_opNorm ξ).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg ξ)))
        (norm_nonneg η))
  choose c hc using fun i j : ℕ => hcoeff (v j) (v i)
  have hall : ∀ᵐ t : ℝ ∂volume, ∀ i j : ℕ,
      inner ℂ (v i) (F t (v j)) = c i j :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hc i j
  obtain ⟨t₀, ht₀⟩ := hall.exists
  refine ⟨F t₀, hall.mono fun t ht => ?_⟩
  apply ContinuousLinearMap.ext
  have he : (fun ξ => F t ξ) = (fun ξ => F t₀ ξ) := by
    apply hv.equalizer (F t).continuous (F t₀).continuous
    funext j
    exact hv.eq_of_inner_right ℂ (fun i => (ht i j).trans (ht₀ i j).symm)
  exact congrFun he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialFieldPeriods
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

omit [CompleteSpace H] [CompleteSpace K] in
/-- A nonzero site operator detects its first tensor coefficient. -/
theorem spatialTensorOp_left_injective (b : K →L[ℂ] K) (hb : b ≠ 0) :
    Function.Injective (fun a : H →L[ℂ] H => spatialTensorOp a b) := by
  obtain ⟨η, hη⟩ : ∃ η : K, b η ≠ 0 := by
    by_contra h
    apply hb
    ext η
    exact not_exists_not.mp h η
  intro a c hac
  apply ContinuousLinearMap.ext
  intro ξ
  have he := congrArg (fun T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K =>
    T ((ξ ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : SpatialHilbert H K)) hac
  have hz : ‖a ξ - c ξ‖ * ‖b η‖ = 0 := by
    have he' : (((a ξ - c ξ) ⊗ₜ[ℂ] b η : H ⊗[ℂ] K) : SpatialHilbert H K) = 0 := by
      simpa only [spatialTensorOp_coe, TensorProduct.mapL_tmul,
        TensorProduct.sub_tmul, UniformSpace.Completion.coe_sub, sub_eq_zero] using he
    simpa only [UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul,
      norm_zero] using congrArg norm he'
  exact sub_eq_zero.mp (norm_eq_zero.mp
    ((mul_eq_zero.mp hz).resolve_right (norm_ne_zero_iff.mpr hη)))

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

/-- A nonzero site eigenoperator forces its frequency to be a period of
the first-leg coefficient field. -/
theorem spatialField_period_of_commute
    [TopologicalSpace.SeparableSpace (SpatialHilbert H K)]
    {F : ℝ → H →L[ℂ] H}
    {T : RegularCoreHilbert (SpatialHilbert H K) →L[ℂ]
      RegularCoreHilbert (SpatialHilbert H K)}
    (hF : RepresentsOperatorField volume (fun t => spatialLeft (K := K) (F t)) T)
    (b : K →L[ℂ] K) (hb : b ≠ 0) (s : ℝ)
    (hcomm : Commute T (regularConstantHom volume (spatialRight (H := H) b) *
      (regularRightTranslation (H := SpatialHilbert H K) (Multiplicative.ofAdd s) :
        RegularCoreHilbert (SpatialHilbert H K) →L[ℂ]
          RegularCoreHilbert (SpatialHilbert H K)))) :
    (fun t => F (t + s)) =ᵐ[volume] F := by
  have h := hF.intertwine_translation (spatialRight (H := H) b) s hcomm
  filter_upwards [h] with t ht
  apply (spatialTensorOp_left_injective b hb)
  have ht' := ht.symm
  change spatialTensorOp 1 b * spatialTensorOp (F (t + s)) 1 =
    spatialTensorOp (F t) 1 * spatialTensorOp 1 b at ht'
  simpa only [← spatialTensorOp_mul, one_mul, mul_one] using ht'

/-- The two site frequencies make a represented spatial coefficient field
constant. No factoriality or core classification is assumed. -/
theorem spatialField_constant_of_two_shifts
    [TopologicalSpace.SeparableSpace H]
    [TopologicalSpace.SeparableSpace (SpatialHilbert H K)]
    {F : ℝ → H →L[ℂ] H}
    {T : RegularCoreHilbert (SpatialHilbert H K) →L[ℂ]
      RegularCoreHilbert (SpatialHilbert H K)}
    (hF : RepresentsOperatorField volume (fun t => spatialLeft (K := K) (F t)) T)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume)
    (C : ℝ) (hbound : ∀ᵐ t ∂volume, ‖F t‖ ≤ C)
    (b₁ b₂ : K →L[ℂ] K) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0)
    (s₁ s₂ : ℝ) (hirr : Irrational (s₁ / s₂))
    (hcomm : ∀ (b : K →L[ℂ] K) (s : ℝ),
      (b = b₁ ∧ s = s₁) ∨ (b = b₂ ∧ s = s₂) →
      Commute T (regularConstantHom volume (spatialRight (H := H) b) *
        (regularRightTranslation (H := SpatialHilbert H K) (Multiplicative.ofAdd s) :
          RegularCoreHilbert (SpatialHilbert H K) →L[ℂ]
            RegularCoreHilbert (SpatialHilbert H K)))) :
    ∃ A : H →L[ℂ] H, F =ᵐ[volume] (fun _ => A) ∧
      T = regularConstantHom volume (spatialLeft (K := K) A) := by
  have h₁ := spatialField_period_of_commute hF b₁ hb₁ s₁
    (hcomm b₁ s₁ (Or.inl ⟨rfl, rfl⟩))
  have h₂ := spatialField_period_of_commute hF b₂ hb₂ s₂
    (hcomm b₂ s₂ (Or.inr ⟨rfl, rfl⟩))
  obtain ⟨A, hA⟩ := bounded_operatorField_two_periods_const F hmeas C hbound hirr h₁ h₂
  refine ⟨A, hA, hF.unique ?_⟩
  intro f
  filter_upwards [regularConstantHom_apply_ae volume (spatialLeft (K := K) A) f,
    hA] with t ht hAt
  rw [ht, hAt]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularFourierTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

/-! # Fourier transport of constant operators and real translations -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem postcomp_toLp_p1 (b : H →L[ℂ] H) (f : SchwartzMap ℝ H) :
    (SchwartzMap.postcompCLM b f).toLp 2 = regularConstantHom volume b (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(SchwartzMap.postcompCLM b f).coeFn_toLp 2, f.coeFn_toLp 2,
    regularConstantHom_apply_ae volume b (f.toLp 2)] with t h₁ h₂ h₃
  rw [h₁, h₃, h₂]
  rfl

private theorem fourier_postcomp_p1 (b : H →L[ℂ] H) (f : SchwartzMap ℝ H) (t : ℝ) :
    (𝓕 (SchwartzMap.postcompCLM b f)) t = b ((𝓕 f) t) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  simp only [Real.fourier_eq, SchwartzMap.postcompCLM_apply]
  rw [← b.integral_comp_comm ((Real.fourierIntegral_convergent_iff t).mpr f.integrable)]
  apply integral_congr_ae
  filter_upwards [] with s
  simp only [Circle.smul_def, map_smul]

private theorem fourier_constant_schwartz_p1 (b : H →L[ℂ] H) (f : SchwartzMap ℝ H) :
    (𝓕 (regularConstantHom volume b (f.toLp 2)) : RegularCoreHilbert H) =
      regularConstantHom volume b (𝓕 (f.toLp 2)) := by
  rw [← postcomp_toLp_p1, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (SchwartzMap.postcompCLM b f)).coeFn_toLp 2,
    (𝓕 f).coeFn_toLp 2, regularConstantHom_apply_ae volume b ((𝓕 f).toLp 2)]
    with t h₁ h₂ h₃
  rw [h₁, h₃, h₂]
  exact fourier_postcomp_p1 b f t

/-- Fourier transformation commutes with every constant operator. -/
theorem fourier_regularConstantHom (b : H →L[ℂ] H) (f : RegularCoreHilbert H) :
    (𝓕 (regularConstantHom volume b f) : RegularCoreHilbert H) =
      regularConstantHom volume b (𝓕 f) := by
  let F : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H := Lp.fourierTransformₗᵢ ℝ H
  have he : F.comp (regularConstantHom volume b) = (regularConstantHom volume b).comp F := by
    apply DFunLike.coe_injective
    apply (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := H)
      (p := 2) ENNReal.ofNat_ne_top).equalizer
      (F.comp (regularConstantHom volume b)).continuous
      ((regularConstantHom volume b).comp F).continuous
    funext g
    exact fourier_constant_schwartz_p1 b g
  exact congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => A f) he

/-- Constant operators are unchanged by Fourier conjugation. -/
theorem fourierConj_regularConstantHom (b : H →L[ℂ] H) :
    (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv (regularConstantHom volume b) =
      regularConstantHom volume b := by
  apply ContinuousLinearMap.ext
  intro f
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  change (𝓕 (regularConstantHom volume b ((Lp.fourierTransformₗᵢ ℝ H).symm f)) :
    RegularCoreHilbert H) = _
  rw [fourier_regularConstantHom]
  exact congrArg (regularConstantHom volume b) ((Lp.fourierTransformₗᵢ ℝ H).apply_symm_apply f)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreCentralField
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

omit [TopologicalSpace.SeparableSpace H] in
/-- Fixed operators have constant regular embeddings. -/
theorem regularCoreEmbedding_eq_constant_of_fixed (b : H →L[ℂ] H)
    (hfixed : ∀ s, unitaryConj (U s) b = b) :
    regularCoreEmbedding U hU b = regularConstantHom volume b := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularCoreEmbedding_apply_ae U hU b f,
    regularConstantHom_apply_ae volume b f] with t h₁ h₂
  rw [h₁, h₂]
  have he : unitaryConj (star (U (Multiplicative.ofAdd t))) b = b := by
    rw [regularGroup_star_eq U t]
    exact hfixed _
  simpa only [unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp]
    using congrArg (fun A : H →L[ℂ] H => A (f t)) he

omit [TopologicalSpace.SeparableSpace H] in
/-- A fixed base element commutes with the Fourier transform of a central
core element, in its constant representation. -/
theorem regularCore_central_fourier_commutes_fixed
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hcentral : ∀ S ∈ regularCoreAlgebra U hU P, S * T = T * S)
    (b : H →L[ℂ] H) (hb : b ∈ P) (hfixed : ∀ s, unitaryConj (U s) b = b) :
    Commute ((Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv T)
      (regularConstantHom volume b) := by
  have he := hcentral _ (regularCoreEmbedding_mem_core U hU P hb)
  rw [regularCoreEmbedding_eq_constant_of_fixed U hU b hfixed] at he
  have hf := congrArg (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv he
  simp only [map_mul, fourierConj_regularConstantHom] at hf
  exact hf.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreEigenoperator
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Site eigenoperators become coefficient-weighted frequency shifts -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A scalar character becomes a frequency translation. -/
theorem fourierConj_regularCharacter (s : ℝ) :
    (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv
      (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (regularRightTranslation (H := H) (Multiplicative.ofAdd (-s)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  change (𝓕 ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) ((Lp.fourierTransformₗᵢ ℝ H).symm f)) :
      RegularCoreHilbert H) = _
  rw [fourier_regularCharacterUnitary]
  change regularTranslateApply (-s) (𝓕 ((Lp.fourierTransformₗᵢ ℝ H).symm f)) =
    regularTranslateApply (-s) f
  exact congrArg (regularTranslateApply (-s)) ((Lp.fourierTransformₗᵢ ℝ H).apply_symm_apply f)

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

/-- The regular representation of an eigenoperator is a constant
coefficient followed by the associated character multiplier. -/
theorem regularCoreEmbedding_of_eigenoperator (b : H →L[ℂ] H) (s : ℝ)
    (heigen : ∀ t : ℝ, unitaryConj (star (U (Multiplicative.ofAdd t))) b =
      regularCharacterScalar (2 * Real.pi * s) t • b) :
    regularCoreEmbedding U hU b = regularConstantHom volume b *
      (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularCoreEmbedding_apply_ae U hU b f,
    regularConstantHom_apply_ae volume b
      ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularCharacterUnitary_apply_ae (2 * Real.pi * s) f] with t hp hc hm
  change regularCoreEmbedding U hU b f t =
    regularConstantHom volume b
      ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t
  rw [hp, hc, hm]
  simpa only [unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp,
    smul_apply, map_smul] using
    congrArg (fun B : H →L[ℂ] H => B (f t)) (heigen t)

/-- After Fourier transform, the eigenoperator is a coefficient-weighted
translation. This is the shift used in the factorial-core argument. -/
theorem fourierConj_regularCoreEigenoperator (b : H →L[ℂ] H) (s : ℝ)
    (heigen : ∀ t : ℝ, unitaryConj (star (U (Multiplicative.ofAdd t))) b =
      regularCharacterScalar (2 * Real.pi * s) t • b) :
    (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv (regularCoreEmbedding U hU b) =
      regularConstantHom volume b *
        (regularRightTranslation (H := H) (Multiplicative.ofAdd (-s)) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  rw [regularCoreEmbedding_of_eigenoperator U hU b s heigen, map_mul,
    fourierConj_regularConstantHom, fourierConj_regularCharacter]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoFrequencyCoreFactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Factoriality of the core from two site frequencies

This is the fixed tensor-factor argument of the manuscript. Its product
hypotheses concern local swaps and two explicit site eigenoperators.
These hypotheses imply factoriality of the crossed product.
-/

namespace KadisonKastler

open MeasureTheory UnitalTomsWinter

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace H]
  [TopologicalSpace.SeparableSpace (SpatialHilbert H K)]

/-- Independent product swaps and two incommensurable site frequencies
force the actual regular crossed product of a tensor factor to be a factor. -/
theorem scalarCenter_regularCore_of_two_site_frequencies_oai
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (M : VonNeumannAlgebra H) (hM : ScalarCenter M)
    (D : VonNeumannAlgebra K) (Ω : K) (hΩ : ‖Ω‖ = 1)
    (L : LocalProductSwaps D Ω)
    (hsep : Function.Injective (algebraVectorMap D Ω))
    (U : Multiplicative ℝ →* unitary (SpatialHilbert H K →L[ℂ] SpatialHilbert H K))
    (hU : ∀ ξ, Continuous (fun t : ℝ =>
      (U (Multiplicative.ofAdd t) : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) ξ))
    (hP : ∀ s x, x ∈ spatialProductAlgebra M D →
      unitaryConj (U s) x ∈ spatialProductAlgebra M D)
    (hfixed : ∀ u : unitary (K →L[ℂ] K), (u : K →L[ℂ] K) ∈ D →
      ProductStateCentralizes D Ω u → ∀ s,
      unitaryConj (U s) (spatialRight (H := H) (u : K →L[ℂ] K)) =
        spatialRight (H := H) (u : K →L[ℂ] K))
    (b₁ b₂ : K →L[ℂ] K) (hb₁ : b₁ ∈ D) (hb₂ : b₂ ∈ D)
    (hn₁ : b₁ ≠ 0) (hn₂ : b₂ ≠ 0) (s₁ s₂ : ℝ) (hirr : Irrational (s₁ / s₂))
    (heigen₁ : ∀ t : ℝ,
      unitaryConj (star (U (Multiplicative.ofAdd t))) (spatialRight (H := H) b₁) =
        regularCharacterScalar (2 * Real.pi * s₁) t • spatialRight (H := H) b₁)
    (heigen₂ : ∀ t : ℝ,
      unitaryConj (star (U (Multiplicative.ofAdd t))) (spatialRight (H := H) b₂) =
        regularCharacterScalar (2 * Real.pi * s₂) t • spatialRight (H := H) b₂) :
    ScalarCenter (regularCoreAlgebra U hU (spatialProductAlgebra M D)) := by
  let P := spatialProductAlgebra M D
  let Φ := (Lp.fourierTransformₗᵢ ℝ (SpatialHilbert H K)).conjStarAlgEquiv
  intro T hT hcentral
  obtain ⟨F, hFm, hFn, _, hFT⟩ := regularCore_central_fourier_field U hU P
    hSpectral hDiagonal hP T hT hcentral
  have htensor : Φ T ∈ regularTensorAlgebra P := by
    apply (mem_regularTensorAlgebra_iff P _).mpr
    intro b hb
    have he := congrArg Φ ((mem_regularTensorAlgebra_iff P T).mp
      (regularCoreAlgebra_le_tensor U hU P hP hT) b hb)
    simpa only [map_mul, Φ, fourierConj_regularConstantHom] using he
  have hcomm : ∀ u : unitary (K →L[ℂ] K), (u : K →L[ℂ] K) ∈ D →
      ProductStateCentralizes D Ω u → Commute (Φ T)
        (regularConstantHom volume (spatialRight (H := H) (u : K →L[ℂ] K))) := by
    intro u hu hc
    exact regularCore_central_fourier_commutes_fixed U hU P T hcentral _
      (spatialRight_mem_product M D hu) (hfixed u hu hc)
  obtain ⟨A, hAm, hAn, _, hAT⟩ := first_leg_field_of_product_centralizer M L hΩ hsep
    F (Φ T) hFT hFm ‖T‖ hFn htensor hcomm
  have hEigenComm (b : K →L[ℂ] K) (hb : b ∈ D) (s : ℝ)
      (heigen : ∀ t : ℝ,
        unitaryConj (star (U (Multiplicative.ofAdd t))) (spatialRight (H := H) b) =
          regularCharacterScalar (2 * Real.pi * s) t • spatialRight (H := H) b) :
      Commute (Φ T) (regularConstantHom volume (spatialRight (H := H) b) *
        (regularRightTranslation (H := SpatialHilbert H K) (Multiplicative.ofAdd (-s)) :
          RegularCoreHilbert (SpatialHilbert H K) →L[ℂ]
            RegularCoreHilbert (SpatialHilbert H K))) := by
    have he := congrArg Φ (hcentral _ (regularCoreEmbedding_mem_core U hU P
      (spatialRight_mem_product M D hb)))
    simp only [map_mul] at he
    rw [show Φ (regularCoreEmbedding U hU (spatialRight (H := H) b)) = _ from
      fourierConj_regularCoreEigenoperator U hU _ s heigen] at he
    exact he.symm
  have hirr' : Irrational ((-s₁) / (-s₂)) := by simpa only [neg_div_neg_eq] using hirr
  obtain ⟨a, _, hconst⟩ := spatialField_constant_of_two_shifts hAT hAm ‖T‖ hAn
    b₁ b₂ hn₁ hn₂ (-s₁) (-s₂) hirr' (by
      rintro b s (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hEigenComm b hb₁ s₁ heigen₁
      · exact hEigenComm b hb₂ s₂ heigen₂)
  have hTconst : T = regularConstantHom volume (spatialLeft (K := K) a) := by
    have he : Φ T = Φ (regularConstantHom volume (spatialLeft (K := K) a)) :=
      hconst.trans (fourierConj_regularConstantHom _).symm
    exact Φ.injective he
  rw [hTconst] at hT hcentral ⊢
  exact regularCore_constant_central_scalar U hU P hP
    (scalarCenter_spatialProduct_of_local_swaps M hM L hΩ hsep) _ hT hcentral

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.scalarCenter_regularCore_of_two_site_frequencies_oai.{u} := @OAI.KadisonKastler.scalarCenter_regularCore_of_two_site_frequencies_oai.{u}
