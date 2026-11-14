-- Prove2me | solution 1 for OAI.KadisonKastler.TypeIIInfinityFactor.nonempty_finiteMatrixCornerData
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:25:02.336075+00:00
-- url     : https://prove2.me/submissions/b30b9822-bdf3-41fe-91d8-518227e129b1

import Mathlib
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
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
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
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
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
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
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
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
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
import Definitions.Def_Q260K059
import Definitions.Def_Q260K061
import Theorems.Thm_OAI_KadisonKastler_FullMatrixCorner_representedCorner_isII1

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreMatrixData
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable equivalent projection families give full matrix corners

The input here is actual projection and partial-isometry data in a represented
von Neumann algebra.  No existence of a semifinite decomposition is assumed as
a published input.  Once such a decomposition has been constructed, the
matrix-corner machinery applies to the explicit operators `v i * star (v j)`.
-/

namespace KadisonKastler

open Generator.Tracial
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

namespace FullMatrixCorner

theorem ofEquivalentProjectionFamily_entry_mem
    (E : Submodule ℂ H) [CompleteSpace E]
    (p : ℕ → AlgebraProjection M) (v : ℕ → Algebra M)
    (hvi : ∀ i, star (v i) * v i = (p 0).val)
    (hvf : ∀ i, v i * star (v i) = (p i).val)
    (horth : Pairwise (fun i j => (p i).val * (p j).val = 0))
    (hp0 : ((p 0).val : H →L[ℂ] H) = E.starProjection)
    (htotal : ∀ x : H, HasSum (fun i => ((p i).val : H →L[ℂ] H) x) x)
    (i j : ℕ) :
    (ofEquivalentProjectionFamily E p v hvi hvf horth hp0 htotal).entry i j ∈ M :=
  (projectionFamilyEntry v i j).property

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedProperInfiniteProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable copies of a full projection

Blackadar, *Operator Algebras*, III.1.3.6 (author PDF, printed p.243),
asserts that a full projection in a properly infinite, locally countably
 decomposable von Neumann algebra admits a countable orthogonal family of
 equivalent projections with strong sum one. Separably acting algebras are
 countably decomposable. The input below is only this projection assertion.

The projection's central support is the already constructed orbit-closure
projection. Proper infiniteness is expressed by two isometries with
orthogonal ranges. No trace, corner type, or perturbation conclusion is part
of this published input.

Primary source: https://bruceblackadar.com/Mathematics/Cycr.pdf
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- Finiteness is preserved by Murray--von Neumann equivalence. -/
theorem finiteProjectionIn_of_equivalent (p q : AlgebraProjection M)
    (hfinite : FiniteProjectionIn M p.val) (v : Algebra M)
    (hvi : star v * v = p.val) (hvf : v * star v = q.val) :
    FiniteProjectionIn M q.val := by
  let V : PartialIsometry M := ⟨p, v, hvi⟩
  have hvp : v * p.val = v := V.mul_support
  have hqv : q.val * v = v := by
    have ht := V.target_mul
    change (v * star v) * v = v at ht
    rwa [hvf] at ht
  have hps : p.val * star v = star v := by
    simpa only [star_mul, star_star, p.property.isSelfAdjoint.star_eq] using
      congrArg star hvp
  have hsq : star v * q.val = star v := by
    simpa only [star_mul, star_star, q.property.isSelfAdjoint.star_eq] using
      congrArg star hqv
  intro w hwi hqw
  have hws : star w * q.val = star w := by
    simpa only [star_mul, q.property.isSelfAdjoint.star_eq] using congrArg star hqw
  let a : Algebra M := star v * w * v
  have hai : star a * a = p.val := by
    change star (star v * w * v) * (star v * w * v) = p.val
    rw [star_mul, star_mul, star_star]
    calc
      _ = star v * star w * (v * star v) * w * v := by noncomm_ring
      _ = star v * (star w * q.val) * w * v := by rw [hvf]; noncomm_ring
      _ = star v * (star w * w) * v := by rw [hws]; noncomm_ring
      _ = p.val := by rw [hwi, hsq, hvi]
  have hpa : p.val * a = a := by
    change p.val * (star v * w * v) = star v * w * v
    rw [← mul_assoc, ← mul_assoc, hps]
  have haa := hfinite a hai hpa
  have hrec : v * (a * star a) * star v = w * star w := by
    change v * ((star v * w * v) * star (star v * w * v)) * star v = w * star w
    rw [star_mul, star_mul, star_star]
    calc
      _ = (v * star v) * w * (v * star v) * star w * (v * star v) := by noncomm_ring
      _ = q.val * w * q.val * star w * q.val := by rw [hvf]
      _ = w * (q.val * star w) * q.val := by rw [hqw]; noncomm_ring
      _ = w * star w := by
        have hwq : w * q.val = w := (show PartialIsometry M from ⟨q, w, hwi⟩).mul_support
        rw [← mul_assoc, hwq, mul_assoc, hws]
  calc
    w * star w = v * (a * star a) * star v := hrec.symm
    _ = q.val := by rw [haa, hvp, hvf]

namespace CountableProjectionCopies

variable {p : AlgebraProjection M} (D : CountableProjectionCopies M p)

theorem fullMatrixCorner_mem (i j : ℕ) : D.fullMatrixCorner.entry i j ∈ M :=
  FullMatrixCorner.ofEquivalentProjectionFamily_entry_mem _ D.projection D.rebasedPartial
    D.rebased_initial D.rebased_final D.orthogonal
    (typeIIIInitialSpace_projection (D.projection 0)) D.total i j

theorem first_nonzero (hp : p.val ≠ 0) : (D.projection 0).val ≠ 0 := by
  intro hz
  have hv : D.witness 0 = 0 :=
    (CStarRing.mul_star_self_eq_zero_iff _).mp ((D.final 0).trans hz)
  have hi := D.initial 0
  rw [hv, star_zero, zero_mul] at hi
  exact hp hi.symm

theorem first_finite (hfinite : FiniteProjectionIn M p.val) :
    FiniteProjectionIn M (D.projection 0).val :=
  finiteProjectionIn_of_equivalent p (D.projection 0) hfinite
    (D.witness 0) (D.initial 0) (D.final 0)

end CountableProjectionCopies

/-- A chosen finite nonzero full projection produces a finite full matrix corner. -/
theorem exists_finite_fullMatrixCorner_of_full_projection
    [TopologicalSpace.SeparableSpace H]
    (hPublished : PublishedProperInfiniteProjectionCopies.{u})
    (hInfinite : ProperlyInfiniteIdentity M) (p : AlgebraProjection M)
    (hfull : (centralSupport p).val = 1) (hp : p.val ≠ 0)
    (hfinite : FiniteProjectionIn M p.val) :
    ∃ q : AlgebraProjection M, q.val ≠ 0 ∧ FiniteProjectionIn M q.val ∧
      ∃ F : FullMatrixCorner (typeIIIInitialSpace q), ∀ i j, F.entry i j ∈ M := by
  obtain ⟨D⟩ := hPublished H M hInfinite p hfull
  exact ⟨D.projection 0, D.first_nonzero hp, D.first_finite hfinite,
    D.fullMatrixCorner, D.fullMatrixCorner_mem⟩

/-- In a factor, nonzeroness supplies the full-central-support hypothesis. -/
theorem exists_finite_fullMatrixCorner_of_factor
    [TopologicalSpace.SeparableSpace H]
    (hPublished : PublishedProperInfiniteProjectionCopies.{u})
    (hInfinite : ProperlyInfiniteIdentity M) (hfactor : ScalarCenter M)
    (p : AlgebraProjection M) (hp : p.val ≠ 0) (hfinite : FiniteProjectionIn M p.val) :
    ∃ q : AlgebraProjection M, q.val ≠ 0 ∧ FiniteProjectionIn M q.val ∧
      ∃ F : FullMatrixCorner (typeIIIInitialSpace q), ∀ i j, F.entry i j ∈ M := by
  apply exists_finite_fullMatrixCorner_of_full_projection hPublished hInfinite p ?_ hp hfinite
  apply centralSupport_eq_one_of_factor
  · intro c hc
    obtain ⟨z, hz⟩ := hfactor c.val c.property (fun a ha =>
      congrArg Subtype.val (hc ⟨a, ha⟩))
    exact ⟨z, Subtype.ext hz⟩
  · exact hp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SemifiniteFactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite matrix corners in semifinite diffuse factors

The type-II-infinity predicate uses scalar center, two orthogonal isometries,
projection semifiniteness, and diffuseness. Choosing one finite nonzero
projection and applying the countable-copy theorem constructs the
matrix corner and its II₁ factor structure. There is no trace or stability
conclusion in the type predicate. Projection semifiniteness is exactly the
criterion in Blackadar III.1.4.2; III.1.4.6 identifies the properly infinite
continuous semifinite part as type II∞.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- One finite nonzero projection is selected from projection semifiniteness. -/
theorem TypeIIInfinityFactor.exists_nonzero_finite_projection (hM : TypeIIInfinityFactor M) :
    ∃ p : AlgebraProjection M, p.val ≠ 0 ∧ FiniteProjectionIn M p.val := by
  let p : AlgebraProjection M := ⟨1, IsStarProjection.one (Algebra M)⟩
  have hp : p.val ≠ 0 := by
    intro hz
    exact hM.properlyInfinite.nonzero (congrArg Subtype.val hz)
  obtain ⟨q, _, hq, hqfinite⟩ := hM.semifinite p hp
  exact ⟨q, hq, hqfinite⟩

/-- A type II∞ factor has the concrete finite full matrix-corner data needed
for semifinite perturbation. -/
theorem TypeIIInfinityFactor.nonempty_finiteMatrixCornerData_oai
    [TopologicalSpace.SeparableSpace H] (hM : TypeIIInfinityFactor M)
    (hCopies : PublishedProperInfiniteProjectionCopies.{u}) :
    Nonempty (FiniteFullMatrixCornerData M) := by
  obtain ⟨p, hp, hpfinite⟩ := hM.exists_nonzero_finite_projection
  obtain ⟨q, hq, hqfinite, F, hF⟩ := exists_finite_fullMatrixCorner_of_factor
    hCopies hM.properlyInfinite hM.factor p hp hpfinite
  have hE0 : (typeIIIInitialSpace q).starProjection ≠ (0 : H →L[ℂ] H) := by
    intro hz
    apply hq
    apply Subtype.ext
    exact (typeIIIInitialSpace_projection q).trans hz
  have hFinite : FiniteProjectionIn M
      ⟨(typeIIIInitialSpace q).starProjection, F.zero_zero ▸ hF 0 0⟩ := by
    have he : (⟨(typeIIIInitialSpace q).starProjection,
        F.zero_zero ▸ hF 0 0⟩ : Algebra M) = q.val :=
      Subtype.ext (typeIIIInitialSpace_projection q).symm
    rw [he]
    exact hqfinite
  exact ⟨{
    projection := q
    projection_nonzero := hq
    projection_finite := hqfinite
    matrix := F
    matrix_mem := hF
    corner_isII1 := F.representedCorner_isII1 M hF hM.factor hE0 hFinite hM.diffuse }⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.TypeIIInfinityFactor.nonempty_finiteMatrixCornerData_oai.{u} := @OAI.KadisonKastler.TypeIIInfinityFactor.nonempty_finiteMatrixCornerData_oai.{u}
