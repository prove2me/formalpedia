-- Prove2me | solution 1 for OAI.KadisonKastler.exists_bounded_rescaledGraph_signal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:56:43.336549+00:00
-- url     : https://prove2.me/submissions/e3709693-e8aa-4def-8bb8-1ea0ee119d63

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
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
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
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
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
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K035
import Theorems.Thm_OAI_KadisonKastler_exists_rescaledGraph_orbit_signal_and_cost
import Theorems.Thm_OAI_KadisonKastler_norm_rescaledGraph_spectralClip_128_discard_le

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralClipping
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Norm clipping with preserved support and quotient image

The cutoff multiplies an element on the right by a continuous function of
its absolute value. Both the clipped part and the discarded part have
star squares bounded by the original star square.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

theorem clippingFunction_nonneg {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    0 ≤ clippingFunction β t :=
  div_nonneg hβ.le (hβ.le.trans (le_max_left β t))

theorem clippingFunction_le_one {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    clippingFunction β t ≤ 1 :=
  (div_le_one (hβ.trans_le (le_max_left β t))).mpr (le_max_left β t)

theorem clippingFunction_square_le {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) :
    (t * clippingFunction β t) ^ 2 ≤ t ^ 2 := by
  have h0 := clippingFunction_nonneg hβ t
  have h1 := clippingFunction_le_one hβ t
  have ht0 : 0 ≤ t * clippingFunction β t := mul_nonneg ht h0
  have ht1 : t * clippingFunction β t ≤ t := by nlinarith
  nlinarith

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Clipping does not increase the star square. -/
theorem spectralClip_star_mul_self_le {β : ℝ} (hβ : 0 < β) (x : A) :
    star (spectralClip β x) * spectralClip β x ≤ star x * x := by
  rw [spectralClip_star_mul_self hβ,
    ← CFC.abs_mul_abs x, ← pow_two, ← cfc_pow_id (R := ℝ) (CFC.abs x) 2]
  apply (cfc_le_iff _ _ _ (by exact
    ((continuous_id.mul (clippingFunction_continuous hβ)).pow 2).continuousOn)).mpr
  intro t ht
  exact clippingFunction_square_le hβ (spectrum_nonneg_of_nonneg (CFC.abs_nonneg x) ht)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VectorStateFourthMoment
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nontracial fourth moments of independent signs

The three-pairing sign identity holds for the actual vector functional.
The crossed pairing is bounded after summing the two orders of its
indices. This avoids applying a tracial fourth-moment theorem to the
nontracial vector state in the modular graph argument.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Positivity of the vector functional is a Hilbert norm identity. -/
theorem realVectorState_star_mul_self (Ω : H) (x : H →L[ℂ] H) :
    realVectorState Ω (star x * x) = ‖x Ω‖ ^ 2 := by
  simp only [realVectorState_apply, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  norm_cast

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RescaledTomitaGraph
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixCentralVectorSpace_complete _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Rescaled Tomita graphs in a fixed two-coordinate Hilbert space

A fixed conjugation identifies the conjugate copy of the Hilbert space
with the original one. In these coordinates the graph vector is
`(x Ω, c J (x* Ω))`. The same identification is used for both algebras.
No closability or modular spectral theorem is needed for the closed
linear graph subspace or the elementary projection comparison below.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The defining weighted graph norm, with no restriction on the scale. -/
theorem norm_rescaledGraphVector_sq (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (x : H →L[ℂ] H) :
    ‖rescaledGraphVector J Ω c x‖ ^ 2 = ‖x Ω‖ ^ 2 + c ^ 2 * ‖star x Ω‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_two, rescaledGraphVector_zero, rescaledGraphVector_one,
    norm_smul, J.norm_map, Real.norm_eq_abs, mul_pow, sq_abs]

/-- A bound on the defining graph vectors extends to their actual closure. -/
theorem rescaledGraph_bound_on_closure
    (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (B : ℝ)
    (hB : ∀ x : Algebra P,
      ‖T (rescaledGraphVector J Ω c x.val)‖ ≤ B * ‖rescaledGraphVector J Ω c x.val‖)
    {ξ : TomitaGraphHilbert H} (hξ : ξ ∈ rescaledGraphSubspace P J Ω c) :
    ‖T ξ‖ ≤ B * ‖ξ‖ := by
  have hc : IsClosed {ξ : TomitaGraphHilbert H | ‖T ξ‖ ≤ B * ‖ξ‖} :=
    isClosed_le T.continuous.norm (continuous_const.mul continuous_norm)
  exact closure_minimal (by rintro _ ⟨x, rfl⟩; exact hB x) hc hξ

/-- A graph-vector estimate bounds the operator after graph projection. -/
theorem norm_comp_rescaledGraphProjection_le
    (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ x : Algebra P,
      ‖T (rescaledGraphVector J Ω c x.val)‖ ≤ B * ‖rescaledGraphVector J Ω c x.val‖) :
    ‖T * rescaledGraphProjection P J Ω c‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro ξ
  change ‖T ((rescaledGraphSubspace P J Ω c).starProjection ξ)‖ ≤ B * ‖ξ‖
  exact (rescaledGraph_bound_on_closure P J Ω c T B hv
    ((rescaledGraphSubspace P J Ω c).starProjection_apply_mem ξ)).trans
    (mul_le_mul_of_nonneg_left
      ((rescaledGraphSubspace P J Ω c).norm_starProjection_apply_le ξ) hB)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RescaledGraphSignal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Selecting a normalized vector in a rescaled graph

If a nonzero operator is supported on the closed graph, one of the
defining graph vectors retains more than half its operator norm. The
algebra element can then be rescaled to make its graph vector a unit
vector. This is the signal-selection step used before finite averaging.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A graph-supported nonzero operator has a normalized defining graph
vector on which it retains more than half its norm. -/
theorem exists_normalized_rescaledGraph_signal
    (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (hT : T ≠ 0)
    (hsupport : T * rescaledGraphProjection P J Ω c = T) :
    ∃ x : Algebra P, ‖rescaledGraphVector J Ω c x.val‖ = 1 ∧
      ‖T‖ / 2 < ‖T (rescaledGraphVector J Ω c x.val)‖ := by
  have hnorm : 0 < ‖T‖ := norm_pos_iff.mpr hT
  have hlarge : ¬ ∀ x : Algebra P,
      ‖T (rescaledGraphVector J Ω c x.val)‖ ≤
        (‖T‖ / 2) * ‖rescaledGraphVector J Ω c x.val‖ := by
    intro hb
    have hh := norm_comp_rescaledGraphProjection_le P J Ω c T (by positivity) hb
    rw [hsupport] at hh
    linarith
  push Not at hlarge
  obtain ⟨x, hx⟩ := hlarge
  let v := rescaledGraphVector J Ω c x.val
  have hv : 0 < ‖v‖ := by
    by_contra hn
    have hz : v = 0 := norm_eq_zero.mp (le_antisymm (le_of_not_gt hn) (norm_nonneg v))
    change (‖T‖ / 2) * ‖v‖ < ‖T v‖ at hx
    have hfalse : (0 : ℝ) < 0 := by
      simpa only [hz, norm_zero, map_zero, mul_zero] using hx
    exact (lt_irrefl 0) hfalse
  let a : ℝ := ‖v‖⁻¹
  let y : Algebra P := (a : ℂ) • x
  have he : rescaledGraphVector J Ω c y.val = (a : ℂ) • v := by
    exact (rescaledGraphMap P J Ω c).map_smul (a : ℂ) x
  have ha : 0 < a := inv_pos.mpr hv
  have hanorm : ‖(a : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hnormalize : a * ‖v‖ = 1 := inv_mul_cancel₀ (ne_of_gt hv)
  refine ⟨y, ?_, ?_⟩
  · rw [he, norm_smul, hanorm]
    exact hnormalize
  · have hh := mul_lt_mul_of_pos_left hx ha
    change a * ((‖T‖ / 2) * ‖v‖) < a * ‖T v‖ at hh
    rw [he, map_smul, norm_smul, hanorm]
    calc
      ‖T‖ / 2 = a * ((‖T‖ / 2) * ‖v‖) := by
        calc
          _ = (‖T‖ / 2) * (a * ‖v‖) := by rw [hnormalize, mul_one]
          _ = _ := by ring
      _ < a * ‖T v‖ := hh

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RecoveryJointLaw
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Equality of the actual recovery expression for free pairs

Continuous clipping stays in the closed algebra generated by the
projection and the Haar unitary. The finite normal-word trace law therefore
applies to the concrete recovery contraction, without a spectral premise.
-/

namespace KadisonKastler

noncomputable section

universe u v

variable {B : Type u} [CStarAlgebra B]

attribute [local instance] OAI.KadisonKastler.recoveryJointLawOrder
attribute [local instance] OAI.KadisonKastler.recoveryJointLawStarOrder
theorem spectralClip_mem_closedStarSubalgebra (S : StarSubalgebra ℂ B)
    (hS : IsClosed (S : Set B)) (β : ℝ) {x : B} (hx : x ∈ S) :
    spectralClip β x ∈ S := by
  let : IsClosed (S : Set B) := hS
  have hxx : star x * x ∈ S := S.mul_mem (S.star_mem' hx) hx
  have ha : CFC.abs x ∈ S := by
    rw [CFC.abs, CFC.sqrt_eq_real_sqrt _ (star_mul_self_nonneg x), cfcₙ_eq_cfc]
    exact cfc_mem (𝕜' := ℂ) (S := StarSubalgebra ℂ B) (s := S) Real.sqrt hxx
  exact S.mul_mem hx (cfc_mem (𝕜' := ℂ) (S := StarSubalgebra ℂ B) (s := S) (clippingFunction β) ha)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralClipStar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.pairedRepresentation_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Adjoint compatibility of the continuous spectral cutoff

A two-by-two block argument transports continuous functional calculus
through an intertwiner between selfadjoint elements. Applied twice to
`xx*` and `x*x`, it shows that the cutoff commutes with adjoints. This
provides the left-sided fourth-moment estimate from the right-sided one.
-/

namespace KadisonKastler

noncomputable section

open scoped CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local instance clipPiComplexCFC : ContinuousFunctionalCalculus ℂ (Fin 2 → A) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus
attribute [local instance] OAI.KadisonKastler.clipBlockComplexCFC
local instance clipPiCFC : ContinuousFunctionalCalculus ℝ (Fin 2 → A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

attribute [local instance] OAI.KadisonKastler.clipBlockCFC
local instance clipBlockOrder_rdf7c4b_1 : PartialOrder (CStarMatrix (Fin 2) (Fin 2) A) :=
  CStarAlgebra.spectralOrder _
local instance clipBlockStarOrder_rdf7c4b_1 : StarOrderedRing (CStarMatrix (Fin 2) (Fin 2) A) :=
  CStarAlgebra.spectralOrderedRing _
private theorem cfc_blockDiagonal (f : ℝ → ℝ) (hf : Continuous f)
    (a b : A) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    cfc f (blockDiagonal a b) = blockDiagonal (cfc f a) (cfc f b) := by
  have hp : IsSelfAdjoint (![a, b] : Fin 2 → A) := by
    funext i
    fin_cases i
    · change star a = a
      exact ha.star_eq
    · change star b = b
      exact hb.star_eq
  have hpd : IsSelfAdjoint (diagonalStarAlgHom (Fin 2) (![a, b] : Fin 2 → A)) := by
    change star (diagonalStarAlgHom (Fin 2) (![a, b] : Fin 2 → A)) = _
    rw [← map_star, hp.star_eq]
  have hc : Continuous (diagonalStarAlgHom (A := A) (Fin 2)) :=
    (NonUnitalStarAlgHom.isometry (diagonalStarAlgHom (A := A) (Fin 2))
      (diagonalStarAlgHom_injective (Fin 2))).continuous
  have hm := (diagonalStarAlgHom (A := A) (Fin 2)).map_cfc f (![a, b] : Fin 2 → A)
    hf.continuousOn hc hp hpd
  rw [blockDiagonal, ← hm]
  have he := cfc_map_pi (S := ℂ) f (![a, b] : Fin 2 → A) hf.continuousOn hp
    (by intro i; fin_cases i; exact ha; exact hb)
  rw [he]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Continuous real functional calculus respects an intertwiner of two
selfadjoint elements. -/
theorem cfc_selfAdjoint_intertwines (a b x : A)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hx : a * x = x * b)
    (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f a * x = x * cfc f b := by
  let D : CStarMatrix (Fin 2) (Fin 2) A := blockDiagonal a b
  let X : CStarMatrix (Fin 2) (Fin 2) A := blockOffDiagonal x 0
  have hDX : Commute D X := by
    change D * X = X * D
    ext i j
    simp only [D, X, CStarMatrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [blockDiagonal, blockOffDiagonal, hx]
  have hfc := hDX.cfc_real f
  rw [show D = blockDiagonal a b from rfl, cfc_blockDiagonal f hf a b ha hb] at hfc
  have he := congrArg (fun T : CStarMatrix (Fin 2) (Fin 2) A => T 0 1) hfc.eq
  simp only [CStarMatrix.mul_apply, Fin.sum_univ_two, X] at he
  simpa [blockDiagonal, blockOffDiagonal] using he

/-- The absolute values satisfy the usual polar intertwining identity,
without requiring the existence of a polar partial isometry. -/
theorem abs_star_intertwines (x : A) : CFC.abs (star x) * x = x * CFC.abs x := by
  have h := cfc_selfAdjoint_intertwines (x * star x) (star x * x) x
    (by simpa only [star_star] using (star_mul_self_nonneg (star x)).isSelfAdjoint)
    (star_mul_self_nonneg x).isSelfAdjoint (by noncomm_ring)
    Real.sqrt Real.continuous_sqrt
  simp only [CFC.abs, star_star]
  rw [CFC.sqrt_eq_real_sqrt _ (by simpa only [star_star] using star_mul_self_nonneg (star x)),
    CFC.sqrt_eq_real_sqrt _ (star_mul_self_nonneg x), cfcₙ_eq_cfc, cfcₙ_eq_cfc]
  exact h

/-- Clipping an adjoint is the adjoint of the same continuous cutoff. -/
theorem star_spectralClip {β : ℝ} (hβ : 0 < β) (x : A) :
    star (spectralClip β x) = spectralClip β (star x) := by
  have h := cfc_selfAdjoint_intertwines (CFC.abs (star x)) (CFC.abs x) x
    (CFC.abs_nonneg _).isSelfAdjoint (CFC.abs_nonneg _).isSelfAdjoint
    (abs_star_intertwines x) (clippingFunction β) (clippingFunction_continuous hβ)
  have hs := congrArg star h
  have hr : star (cfc (clippingFunction β) (CFC.abs x)) =
      cfc (clippingFunction β) (CFC.abs x) :=
    (cfc_predicate (clippingFunction β) (CFC.abs x)).star_eq
  have hl : star (cfc (clippingFunction β) (CFC.abs (star x))) =
      cfc (clippingFunction β) (CFC.abs (star x)) :=
    (cfc_predicate (clippingFunction β) (CFC.abs (star x))).star_eq
  simp only [star_mul, hr, hl] at hs
  simpa only [spectralClip, star_mul, hr] using hs.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphClipping
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spectral clipping of a rescaled graph vector

The positive vector state can be applied to the two C*-order tail
bounds. Adjoint compatibility gives the same cutoff on both graph
coordinates. No traciality of the vector state is used.
-/

namespace KadisonKastler

noncomputable section

open scoped CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.graphClippingOrder
attribute [local instance] OAI.KadisonKastler.graphClippingStarOrder
/-- A positive vector functional is monotone in the C*-order. -/
theorem realVectorState_mono (Ω : H) {x y : H →L[ℂ] H} (hxy : x ≤ y) :
    realVectorState Ω x ≤ realVectorState Ω y := by
  obtain ⟨z, hz⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hxy)
  have h : 0 ≤ realVectorState Ω (star z * z) := by
    rw [realVectorState_star_mul_self]
    positivity
  rw [← hz, map_sub] at h
  linarith

/-- Right vector-state variance decreases under clipping. -/
theorem vectorState_spectralClip_right_le (Ω : H) {β : ℝ} (hβ : 0 < β)
    (x : H →L[ℂ] H) :
    ‖spectralClip β x Ω‖ ^ 2 ≤ ‖x Ω‖ ^ 2 := by
  simpa only [realVectorState_star_mul_self] using
    realVectorState_mono Ω (spectralClip_star_mul_self_le hβ x)

/-- The adjoint coordinate has the same variance decrease. -/
theorem vectorState_spectralClip_left_le (Ω : H) {β : ℝ} (hβ : 0 < β)
    (x : H →L[ℂ] H) :
    ‖star (spectralClip β x) Ω‖ ^ 2 ≤ ‖star x Ω‖ ^ 2 := by
  simpa only [star_spectralClip hβ] using vectorState_spectralClip_right_le Ω hβ (star x)

/-- The clipped graph remains bounded by the sampled second and fourth
moment cost. -/
theorem norm_rescaledGraph_spectralClip_sq_le_cost
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) {β : ℝ} (hβ : 0 < β)
    (x : H →L[ℂ] H) :
    ‖rescaledGraphVector J Ω c (spectralClip β x)‖ ^ 2 ≤
      graphMomentCost Ω (c ^ 2) x := by
  rw [norm_rescaledGraphVector_sq]
  have hr := vectorState_spectralClip_right_le Ω hβ x
  have hl := mul_le_mul_of_nonneg_left
    (vectorState_spectralClip_left_le Ω hβ x) (sq_nonneg c)
  have hp : 0 ≤ realVectorState Ω ((star x * x) ^ 2) := by
    have he : (star x * x) ^ 2 = star (star x * x) * (star x * x) := by
      simp only [star_mul, star_star, pow_two]
    rw [he, realVectorState_star_mul_self]
    positivity
  have hq : 0 ≤ realVectorState Ω ((x * star x) ^ 2) := by
    have he : (x * star x) ^ 2 = star (x * star x) * (x * star x) := by
      simp only [star_mul, star_star, pow_two]
    rw [he, realVectorState_star_mul_self]
    positivity
  unfold graphMomentCost
  rw [realVectorState_star_mul_self]
  have he : realVectorState Ω (x * star x) = ‖star x Ω‖ ^ 2 := by
    simpa only [star_star] using realVectorState_star_mul_self Ω (star x)
  rw [he]
  nlinarith [mul_nonneg (sq_nonneg c) hq]

/-- Clipping respects the actual concrete von Neumann algebra. -/
theorem spectralClip_mem_vonNeumannAlgebra (M : VonNeumannAlgebra H)
    (β : ℝ) {x : H →L[ℂ] H} (hx : x ∈ M) : spectralClip β x ∈ M :=
  spectralClip_mem_closedStarSubalgebra M.toStarSubalgebra (isClosed_algebra M) β hx

/-- The signal lost in clipping is at most the operator norm times the
graph-tail norm. -/
theorem graphSignal_spectralClip_loss_le
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
    (β : ℝ) (x : H →L[ℂ] H) :
    ‖T (rescaledGraphVector J Ω c x)‖ ≤
      ‖T (rescaledGraphVector J Ω c (spectralClip β x))‖ +
        ‖T‖ * ‖rescaledGraphVector J Ω c (x - spectralClip β x)‖ := by
  have he := (rescaledGraphOperatorMap J Ω c).map_sub x (spectralClip β x)
  change rescaledGraphVector J Ω c (x - spectralClip β x) =
    rescaledGraphVector J Ω c x - rescaledGraphVector J Ω c (spectralClip β x) at he
  have hd := T.le_opNorm (rescaledGraphVector J Ω c (x - spectralClip β x))
  rw [he, map_sub] at hd
  rw [← he] at hd
  have ht := norm_le_norm_add_norm_sub
    (T (rescaledGraphVector J Ω c (spectralClip β x))) (T (rescaledGraphVector J Ω c x))
  rw [norm_sub_rev] at ht
  exact ht.trans (add_le_add le_rfl hd)

/-- A sampled vector with the retained squared signal admits an actual
bounded clipping that still retains a uniform fraction of that signal. -/
theorem graphSignal_spectralClip_128_lower_bound
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (x : H →L[ℂ] H)
    (hcost : graphMomentCost Ω (c ^ 2) x ≤ 240)
    (hsignal : ‖T‖ ^ 2 / 8 ≤ ‖T (rescaledGraphVector J Ω c x)‖ ^ 2) :
    ‖T‖ / 8 ≤ ‖T (rescaledGraphVector J Ω c (spectralClip 128 x))‖ := by
  have ht := graphSignal_spectralClip_loss_le J Ω c T 128 x
  have he := norm_rescaledGraph_spectralClip_128_discard_le J Ω c x hcost
  have hs : ‖T‖ / 3 ≤ ‖T (rescaledGraphVector J Ω c x)‖ := by
    nlinarith [norm_nonneg T, norm_nonneg (T (rescaledGraphVector J Ω c x))]
  have hm := mul_le_mul_of_nonneg_left he (norm_nonneg T)
  nlinarith [norm_nonneg T]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FlattenedGraphVector
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.Generator.orthonormalMatrixUnits_entry_apply _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.PointedMatrixSites.wordOperator_cons _root_.OAI.KadisonKastler.PointedMatrixSites.wordVector_cons _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.centralVectorDefect_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.conjugateMatrixUnits_entry _root_.OAI.KadisonKastler.conjugateOperatorMap_apply _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.graphCoordinateScale_one _root_.OAI.KadisonKastler.graphCoordinateScale_zero _root_.OAI.KadisonKastler.graphIsometry_one _root_.OAI.KadisonKastler.graphIsometry_zero _root_.OAI.KadisonKastler.graphReciprocalFlip_norm _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rightVectorLinear_apply _root_.OAI.KadisonKastler.spatialMatrixAmplification_apply _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaGraphFirst_adjoint_apply _root_.OAI.KadisonKastler.tomitaGraphFirst_apply _root_.OAI.KadisonKastler.tomitaGraphFlip_one _root_.OAI.KadisonKastler.tomitaGraphFlip_zero _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A bounded operator retaining the rescaled graph defect

The defining graph vector is normalized, averaged over the actual
finite matrix orbits, sampled with independent signs, and spectrally
clipped. All bounds concern the same resulting algebra element.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.flattenedGraphOrder
local instance flattenedGraphStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

private theorem normalizedSignSum_mem
    (M : VonNeumannAlgebra H) {ι : Type*} [Fintype ι]
    (a : ι → H →L[ℂ] H) (ha : ∀ i, a i ∈ M) (ε : ι → Bool) :
    normalizedFiniteSignSum a ε ∈ M := by
  change normalizedFiniteSignSum a ε ∈ M.toStarSubalgebra.restrictScalars ℝ
  unfold normalizedFiniteSignSum finiteSignSum
  apply (M.toStarSubalgebra.restrictScalars ℝ).smul_mem
  apply (M.toStarSubalgebra.restrictScalars ℝ).sum_mem
  intro i _
  exact (M.toStarSubalgebra.restrictScalars ℝ).smul_mem (ha i) _

private theorem matrixOrbitSample_mem
    (M : VonNeumannAlgebra H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hE : E.algebra ≤ M.toStarSubalgebra) (x : H →L[ℂ] H) (hx : x ∈ M)
    (g : MatrixOrbitIndex d) : matrixOrbitSample E x g ∈ M := by
  change (matrixUnitSignedRepresentation E g.1 : H →L[ℂ] H) * x *
    star (matrixUnitSignedRepresentation E g.2 : H →L[ℂ] H) ∈ M
  exact M.mul_mem (M.mul_mem (hE (matrixUnitSignedRepresentation_mem E g.1)) hx)
    (M.toStarSubalgebra.star_mem' (hE (matrixUnitSignedRepresentation_mem E g.2)))

/-- A nonzero graph-supported operator has one uniformly bounded algebra
vector which retains a fixed fraction of its norm. The matrix actions
are the actual common left/right actions on the graph. -/
theorem exists_bounded_rescaledGraph_signal_oai
    (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ A ∈ M, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hc : ∀ n a, a ∈ (E n).algebra → ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    {k : ℝ} (hk : 1 ≤ k)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (hT : T ≠ 0)
    (hsupport : T * rescaledGraphProjection M J Ω (Real.sqrt k) = T)
    (hcomm : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ M.commutant)
    (hvector : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) Ω = a Ω)
    (hinvariant : ∀ j (u v : unitary (H →L[ℂ] H)),
      (u : H →L[ℂ] H) ∈ (E j).algebra → (v : H →L[ℂ] H) ∈ (E j).algebra →
      T * (rescaledGraphAction J hJ u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) =
        (rescaledGraphAction J hJ u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) * T) :
    ∃ z : Algebra M, ‖z‖ ≤ 128 ∧
      ‖rescaledGraphVector J Ω (Real.sqrt k) z.val‖ ^ 2 ≤ 240 ∧
      ‖T‖ / 8 ≤ ‖T (rescaledGraphVector J Ω (Real.sqrt k) z.val)‖ := by
  obtain ⟨x, hxunit, hxsignal⟩ :=
    exists_normalized_rescaledGraph_signal M J Ω (Real.sqrt k) T hT hsupport
  have hk0 : 0 ≤ k := zero_le_one.trans hk
  have hxnorm : ‖x.val Ω‖ ^ 2 + k * ‖star x.val Ω‖ ^ 2 = 1 := by
    have hn := norm_rescaledGraphVector_sq J Ω (Real.sqrt k) x.val
    rw [hxunit, Real.sq_sqrt hk0] at hn
    simpa only [one_pow] using hn.symm
  have hpos : 0 < ‖T (rescaledGraphVector J Ω (Real.sqrt k) x.val)‖ :=
    (div_pos (norm_pos_iff.mpr hT) (by norm_num)).trans hxsignal
  obtain ⟨j, m, ω, ε, _, hs, hcost⟩ :=
    exists_rescaledGraph_orbit_signal_and_cost M Ω hΩ d E hmono hEM hirr hc
      x.val x.property J hJ hk hxnorm T hpos hcomm hvector hinvariant
  let y : H →L[ℂ] H := normalizedFiniteSignSum
    (fun i => matrixOrbitSample (E j) x.val (ω i)) ε
  have hy : y ∈ M := normalizedSignSum_mem M _
    (fun i => matrixOrbitSample_mem M (E j) (hEM j) x.val x.property (ω i)) ε
  have hcost' : graphMomentCost Ω ((Real.sqrt k) ^ 2) y ≤ 240 := by
    simpa only [Real.sq_sqrt hk0] using hcost
  have hsignal : ‖T‖ ^ 2 / 8 ≤ ‖T (rescaledGraphVector J Ω (Real.sqrt k) y)‖ ^ 2 := by
    change ‖T (rescaledGraphVector J Ω (Real.sqrt k) x.val)‖ ^ 2 / 2 ≤ _ at hs
    nlinarith [norm_nonneg T]
  refine ⟨⟨spectralClip 128 y, spectralClip_mem_vonNeumannAlgebra M 128 hy⟩, ?_, ?_, ?_⟩
  · exact spectralClip_norm_le (by norm_num) y
  · exact (norm_rescaledGraph_spectralClip_sq_le_cost J Ω (Real.sqrt k)
      (by norm_num : (0 : ℝ) < 128) y).trans hcost'
  · exact graphSignal_spectralClip_128_lower_bound J Ω (Real.sqrt k) T y hcost' hsignal

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_bounded_rescaledGraph_signal_oai.{u_1} := @OAI.KadisonKastler.exists_bounded_rescaledGraph_signal_oai.{u_1}
