-- Prove2me | solution 1 for OAI.KadisonKastler.publishedBlockCommutantApproximation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:10:12.476534+00:00
-- url     : https://prove2.me/submissions/d483631d-6999-4551-860d-a4994df81ec3

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
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
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
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Definitions.Def_Q260K013
import Definitions.Def_Q260K015
import Theorems.Thm_OAI_KadisonKastler_exists_near_algebra_of_finite_orbit_bound

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FaithfulRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Faithful representations are completely isometric

Injective star-algebra homomorphisms preserve C⋆-norms at each square
matrix level. The isometric corner embedding then gives the same statement
for every rectangular matrix size used in the perturbation estimates.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

/-- Faithfulness preserves the norm of each square amplification. -/
theorem injective_starAlgHom_matrix_norm (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    {n : Type*} [Fintype n] (X : CStarMatrix n n A) :
    ‖CStarMatrix.mapₗ φ.toAlgHom.toLinearMap X‖ = ‖X‖ := by
  change ‖CStarMatrix.mapₙₐ φ.toNonUnitalStarAlgHom X‖ = ‖X‖
  exact NonUnitalStarAlgHom.norm_map _ (injective_starAlgHom_matrix φ hφ) X

/-- Every faithful star representation preserves all rectangular matrix norms. -/
theorem injective_starAlgHom_completelyIsometric (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ) : CompletelyIsometric φ.toAlgHom.toLinearMap := by
  intro p q X
  calc
    ‖CStarMatrix.mapₗ φ.toAlgHom.toLinearMap X‖ =
        ‖rectangularCorner (CStarMatrix.mapₗ φ.toAlgHom.toLinearMap X)‖ :=
      (norm_rectangularCorner _).symm
    _ = ‖CStarMatrix.mapₗ φ.toAlgHom.toLinearMap (rectangularCorner X)‖ := by
      rw [rectangularCorner_map]
    _ = ‖rectangularCorner X‖ := injective_starAlgHom_matrix_norm φ hφ _
    _ = ‖X‖ := norm_rectangularCorner X

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCorrection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Rectangular matrix estimates for multiplication correction

The inverse and corrected-map bounds used in the UCP criterion hold at
every rectangular C⋆-matrix size. The source and target may be represented
in a third ambient C⋆-algebra.
-/

namespace KadisonKastler

variable {A B C : Type*}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder C] [StarOrderedRing C] in
/-- Entrywise application respects composition on rectangular matrices. -/
theorem matrix_map_comp (F : A →ₗ[ℂ] B) (G : B →ₗ[ℂ] C) {p q : ℕ}
    (X : CStarMatrix (Fin p) (Fin q) A) :
    CStarMatrix.mapₗ (G.comp F) X = CStarMatrix.mapₗ G (CStarMatrix.mapₗ F X) := by
  ext i j
  rfl

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CStarCommutatorClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial commutator bounds pass to the represented bicommutant

Spectral clipping lifts each represented contraction to an actual source
contraction. Kaplansky density then passes its commutator bound to the
unit ball of the represented von Neumann closure.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_source_contraction (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (b : π.range) (hb : ‖(b : H →L[ℂ] H)‖ ≤ 1) :
    ∃ a : A, π a = b ∧ ‖a‖ ≤ 1 := by
  obtain ⟨a, ha⟩ := b.property
  change π a = (b : H →L[ℂ] H) at ha
  refine ⟨spectralClip 1 a, ?_, spectralClip_norm_le zero_lt_one a⟩
  rw [map_spectralClip_eq π zero_lt_one a (by simpa only [ha] using hb), ha]

theorem commutator_bound_generated_contraction
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) {e : ℝ} (he : 0 ≤ e)
    (hsource : ∀ a : A, ‖T * π a - π a * T‖ ≤ e * ‖a‖)
    (b : H →L[ℂ] H)
    (hb : b ∈ generatedVonNeumannAlgebra π.range) (hbn : ‖b‖ ≤ 1) :
    ‖T * b - b * T‖ ≤ e := by
  classical
  have hb' : b ∈ Set.centralizer (Set.centralizer (π.range : Set (H →L[ℂ] H))) := by
    rwa [← generatedVonNeumannAlgebra_coe]
  obtain ⟨a, ha, ht⟩ := publishedKaplanskyDensity.exists_strong_contraction_net
    π.range b hb' hbn
  have hbound (d : Finset H × ℕ) : ‖T * (a d : H →L[ℂ] H) - (a d : H →L[ℂ] H) * T‖ ≤ e := by
    obtain ⟨x, hx, hxn⟩ := exists_source_contraction π (a d) (ha d)
    rw [← hx]
    exact (hsource x).trans (mul_le_of_le_one_right he hxn)
  apply ContinuousLinearMap.opNorm_le_bound _ he
  intro x
  have hlim : Tendsto (fun d =>
      (T * (a d : H →L[ℂ] H) - (a d : H →L[ℂ] H) * T) x) atTop
      (𝓝 ((T * b - b * T) x)) := by
    change Tendsto (fun d => T ((a d : H →L[ℂ] H) x) - (a d : H →L[ℂ] H) (T x))
      atTop (𝓝 (T (b x) - b (T x)))
    exact (T.continuous.continuousAt.tendsto.comp (ht x)).sub (ht (T x))
  exact le_of_tendsto hlim.norm (Eventually.of_forall fun d =>
    (ContinuousLinearMap.le_opNorm _ x).trans
      (mul_le_mul_of_nonneg_right (hbound d) (norm_nonneg x)))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AmplifiedCommutatorClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Complete commutator estimates on finite represented closures -/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [PartialOrder A] [StarOrderedRing A] in
theorem finiteAmplifiedRepresentation_range (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    (finiteAmplifiedRepresentation (ι := ι) π).range = matrixOperatorAlgebra π.range := by
  apply le_antisymm
  · rintro T ⟨X, rfl⟩
    refine ⟨coefficientMatrixMap π X, ?_, rfl⟩
    intro i j
    exact ⟨X i j, rfl⟩
  · rintro T ⟨Y, hY, rfl⟩
    have hex : ∀ i j, ∃ a : A, π a = Y i j := fun i j => hY i j
    choose X hX using hex
    refine ⟨CStarMatrix.ofMatrix X, ?_⟩
    change hilbertMatrix (coefficientMatrixMap π (CStarMatrix.ofMatrix X)) = hilbertMatrix Y
    congr 1
    apply CStarMatrix.ext
    intro i j
    exact hX i j

omit [PartialOrder A] [StarOrderedRing A] in
theorem finiteAmplifiedRepresentation_apply (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (X : CStarMatrix ι ι A) (x : FiniteHilbert ι H) (i : ι) :
    finiteAmplifiedRepresentation π X x i = ∑ j, π (X i j) (x j) := by
  change hilbertMatrix (coefficientMatrixMap π X) x i = _
  rw [hilbertMatrix_apply]
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem finiteAmplifiedRepresentation_commutator
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (X : CStarMatrix ι ι A) :
    diagonalOperator T * finiteAmplifiedRepresentation π X -
        finiteAmplifiedRepresentation π X * diagonalOperator T =
      hilbertMatrix (CStarMatrix.mapₗ
        ((innerDerivation T).comp π.toAlgHom.toLinearMap) X) := by
  ext x i
  simp only [sub_apply, mul_apply_eq_comp, WithLp.ofLp_sub, Pi.sub_apply,
    diagonalOperator_apply, finiteAmplifiedRepresentation_apply, hilbertMatrix_apply]
  change T (∑ j, π (X i j) (x j)) - (∑ j, π (X i j) (T (x j))) =
    ∑ j, (T (π (X i j) (x j)) - π (X i j) (T (x j)))
  rw [map_sum, Finset.sum_sub_distrib]

theorem completelyBounded_commutator_generated
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) {e : ℝ} (he : 0 ≤ e)
    (hcb : CompletelyBoundedBy ((innerDerivation T).comp π.toAlgHom.toLinearMap) e)
    (n : ℕ) (b : FiniteHilbert (Fin n) H →L[ℂ] FiniteHilbert (Fin n) H)
    (hb : b ∈ matrixVonNeumann (generatedVonNeumannAlgebra π.range)) (hbn : ‖b‖ ≤ 1) :
    ‖diagonalOperator T * b - b * diagonalOperator T‖ ≤ e := by
  apply commutator_bound_generated_contraction (finiteAmplifiedRepresentation π)
    (diagonalOperator T) he _ b _ hbn
  · intro X
    rw [finiteAmplifiedRepresentation_commutator, norm_hilbertMatrix]
    exact hcb n n X
  · rwa [finiteAmplifiedRepresentation_range, generated_matrixOperatorAlgebra]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompleteCommutantDistance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CompletelyBoundedBy.toContinuousLinearMap_apply _root_.OAI.KadisonKastler.finiteDiagonalMap_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The complete commutator-distance formula

The reflection in each simultaneous commutant orbit has norm at most one.
Its commutator is twice the missing orbit component. Finite coefficient
duality and weak operator separation therefore give the sharp factor one half.
-/

namespace KadisonKastler

open Generator
open scoped InnerProductSpace

noncomputable section

theorem projection_reflection_norm_le_one {B : Type*} [CStarAlgebra B]
    (P : B) (hP : IsStarProjection P) : ‖1 - P - P‖ ≤ 1 := by
  let U := 1 - P - P
  have hs : star U = U := by simp only [U, star_sub, star_one, hP.isSelfAdjoint.star_eq]
  have hp : P * P = P := hP.isIdempotentElem.eq
  have hu : star U * U = 1 := by
    rw [hs]
    simp only [U, sub_mul, mul_sub, one_mul, mul_one, hp]
    abel
  have hn : ‖U‖ * ‖U‖ = ‖(1 : B)‖ := by rw [← CStarRing.norm_star_mul_self, hu]
  have ho : ‖(1 : B)‖ * ‖(1 : B)‖ = ‖(1 : B)‖ := by
    rw [← CStarRing.norm_star_mul_self]
    simp
  have hone : ‖(1 : B)‖ ≤ 1 := by nlinarith [norm_nonneg (1 : B)]
  nlinarith [norm_nonneg U]

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem complete_commutator_orbit_bound
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) {e : ℝ} (he : 0 ≤ e)
    (hcb : CompletelyBoundedBy ((innerDerivation T).comp π.toAlgHom.toLinearMap) e)
    (n : ℕ) (x : FiniteHilbert (Fin n) H) :
    ‖diagonalOperator T x -
        (tupleOrbitClosure (generatedVonNeumannAlgebra π.range).commutant.toStarSubalgebra x).starProjection
          (diagonalOperator T x)‖ ≤ (e / 2) * ‖x‖ := by
  let M := generatedVonNeumannAlgebra π.range
  let V := tupleOrbitClosure M.commutant.toStarSubalgebra x
  let P : FiniteHilbert (Fin n) H →L[ℂ] FiniteHilbert (Fin n) H := V.starProjection
  let U : FiniteHilbert (Fin n) H →L[ℂ] FiniteHilbert (Fin n) H := 1 - P - P
  have hP : IsStarProjection P := isStarProjection_starProjection
  have hPm : P ∈ matrixVonNeumann M := by
    apply (mem_matrixVonNeumann_iff_diagonal M P).mpr
    intro a
    exact tupleOrbitProjection_commutes M.commutant.toStarSubalgebra x a
  have hUm : U ∈ matrixVonNeumann M :=
    (matrixVonNeumann M).sub_mem ((matrixVonNeumann M).sub_mem
      (matrixVonNeumann M).one_mem hPm) hPm
  have hUn : ‖U‖ ≤ 1 := projection_reflection_norm_le_one P hP
  have hb := completelyBounded_commutator_generated π T he hcb n U hUm hUn
  let C : FiniteHilbert (Fin n) H →L[ℂ] FiniteHilbert (Fin n) H :=
    diagonalOperator T * U - U * diagonalOperator T
  change ‖C‖ ≤ e at hb
  have hx : P x = x :=
    V.starProjection_eq_self_iff.mpr (mem_tupleOrbitClosure M.commutant.toStarSubalgebra x)
  have heq : C x =
      (-2 : ℂ) • (diagonalOperator T x - P (diagonalOperator T x)) := by
    simp only [C, U, sub_apply, one_apply_eq_self, mul_apply_eq_comp, hx,
      sub_self, zero_sub, map_neg]
    module
  have hn := (C.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg x))
  rw [heq, norm_smul] at hn
  norm_num at hn
  change ‖diagonalOperator T x - P (diagonalOperator T x)‖ ≤ _
  linarith

/-- The sharp strict commutant approximation, for a possibly nonfaithful
star representation of a unital C-star algebra on any Hilbert space. -/
theorem exists_commutant_of_completelyBounded
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) {e : ℝ} (he : 0 ≤ e)
    (hcb : CompletelyBoundedBy ((innerDerivation T).comp π.toAlgHom.toLinearMap) e)
    {r : ℝ} (hr : e / 2 < r) :
    ∃ D : H →L[ℂ] H, (∀ a, D * π a = π a * D) ∧ ‖D - T‖ < r := by
  let M := generatedVonNeumannAlgebra π.range
  obtain ⟨D, hD, hn⟩ := exists_near_algebra_of_finite_orbit_bound
    M.commutant.toStarSubalgebra (Generator.Tracial.vonNeumann_wotClosed M.commutant)
    T (div_nonneg he (by norm_num)) (complete_commutator_orbit_bound π T he hcb) hr
  refine ⟨D, ?_, hn⟩
  intro a
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hD (π a)
    (subset_generatedVonNeumannAlgebra π.range ⟨a, rfl⟩)).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BlockCommutantConstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Commutant distance for paired representations

This is the exact two-by-two specialization used by the stability proof.
The general represented estimate is transported through the faithful
finite Hilbert-sum matrix representation, preserving its constant.
-/

namespace KadisonKastler

noncomputable section

variable (A K : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

attribute [local instance] OAI.KadisonKastler.blockDistanceBaseOrder
local instance blockDistanceBaseStarOrder : StarOrderedRing (K →L[ℂ] K) :=
  CStarAlgebra.spectralOrderedRing _

/-- Arveson--Christensen commutant distance for a pair of representations. -/
theorem publishedBlockCommutantApproximation_oai : PublishedBlockCommutantApproximation A K := by
  intro π T e he hcb r hr
  let H := Generator.FiniteHilbert (Fin 2) K
  let φ : CStarMatrix (Fin 2) (Fin 2) (K →L[ℂ] K) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
    hilbertMatrixHom
  let ρ := φ.comp π
  have hid : (innerDerivation (φ T)).comp ρ.toAlgHom.toLinearMap =
      φ.toAlgHom.toLinearMap.comp ((innerDerivation T).comp π.toAlgHom.toLinearMap) := by
    apply LinearMap.ext
    intro a
    change φ T * φ (π a) - φ (π a) * φ T = φ (T * π a - π a * T)
    rw [map_sub, map_mul, map_mul]
  have hc : CompletelyBoundedBy ((innerDerivation (φ T)).comp ρ.toAlgHom.toLinearMap) e := by
    rw [hid]
    intro p q X
    rw [matrix_map_comp,
      injective_starAlgHom_completelyIsometric φ hilbertMatrixHom_injective p q]
    exact hcb p q X
  obtain ⟨D, hD, hn⟩ := exists_commutant_of_completelyBounded ρ (φ T) he hc hr
  let B : CStarMatrix (Fin 2) (Fin 2) (K →L[ℂ] K) :=
    CStarMatrix.ofMatrix (fun i j => Generator.operatorEntry D i j)
  have hB : φ B = D := hilbertMatrix_operatorEntries D
  refine ⟨B, ?_, ?_⟩
  · intro a
    apply hilbertMatrixHom_injective
    change φ (B * π a) = φ (π a * B)
    rw [map_mul, map_mul, hB]
    exact hD a
  · rw [← norm_hilbertMatrix]
    change ‖φ (B - T)‖ < r
    rw [map_sub, hB]
    exact hn

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.publishedBlockCommutantApproximation_oai.{u_1, u_2} := @OAI.KadisonKastler.publishedBlockCommutantApproximation_oai.{u_1, u_2}
