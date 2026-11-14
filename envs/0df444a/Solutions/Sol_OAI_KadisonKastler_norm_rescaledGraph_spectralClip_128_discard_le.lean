-- Prove2me | solution 1 for OAI.KadisonKastler.norm_rescaledGraph_spectralClip_128_discard_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:54:29.833205+00:00
-- url     : https://prove2.me/submissions/716b63a1-e239-4708-858f-a419f33610e2

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
import Definitions.Def_Q260K031

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FourthMomentClipping
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourth-moment control of the clipping error

The continuous cutoff already used for quotient lifts also supplies the
tracial tail estimate needed to test bimodular operators on bounded balls.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

theorem discardedFunction_square_le_fourth {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) :
    (t * (1 - clippingFunction β t)) ^ 2 ≤ t ^ 4 / β ^ 2 := by
  rw [mul_sub, mul_one, mul_clippingFunction hβ]
  by_cases htβ : t ≤ β
  · rw [min_eq_left htβ, sub_self, zero_pow (by decide)]
    exact div_nonneg (pow_nonneg ht _) (sq_nonneg β)
  · have hβt : β ≤ t := (lt_of_not_ge htβ).le
    rw [min_eq_right hβt]
    apply (le_div_iff₀ (sq_pos_of_pos hβ)).mpr
    have hprod : β * (t - β) ≤ t * t :=
      mul_le_mul hβt (sub_le_self t hβ.le) (sub_nonneg.mpr hβt) ht
    have hs := (sq_le_sq₀ (mul_nonneg hβ.le (sub_nonneg.mpr hβt))
      (mul_nonneg ht ht)).mpr hprod
    nlinarith only [hs]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The discarded square is bounded by the fourth power divided by the
square of the cutoff, in the C*-algebra order. -/
theorem spectralClip_discard_fourth_bound {β : ℝ} (hβ : 0 < β) (x : A) :
    star (x - spectralClip β x) * (x - spectralClip β x) ≤
      (β ^ 2)⁻¹ • (star x * x) ^ 2 := by
  have hcut : x - spectralClip β x =
      x * cfc (fun t => 1 - clippingFunction β t) (CFC.abs x) := by
    rw [cfc_sub (fun _ : ℝ => 1) (clippingFunction β) _ (by fun_prop)
      (clippingFunction_continuous hβ).continuousOn, cfc_const_one ℝ (CFC.abs x),
      mul_sub, mul_one]
    rfl
  have hfour : cfc (fun t : ℝ => t ^ 4) (CFC.abs x) = (star x * x) ^ 2 := by
    rw [cfc_pow_id (R := ℝ) (CFC.abs x) 4 (CFC.abs_nonneg x).isSelfAdjoint]
    calc
      CFC.abs x ^ 4 = (CFC.abs x ^ 2) ^ 2 := by rw [← pow_mul]
      _ = (star x * x) ^ 2 := by rw [pow_two (CFC.abs x), CFC.abs_mul_abs]
  have hright : cfc (fun t : ℝ => t ^ 4 / β ^ 2) (CFC.abs x) =
      (β ^ 2)⁻¹ • (star x * x) ^ 2 := by
    simp_rw [div_eq_mul_inv, mul_comm (_ ^ 4)]
    rw [cfc_const_mul _ (fun t : ℝ => t ^ 4) _ (by fun_prop), hfour]
  rw [hcut, star_mul_cfc_abs x (fun t : ℝ => 1 - clippingFunction β t)
    (continuous_const.sub (clippingFunction_continuous hβ)), ← hright]
  apply (cfc_le_iff _ _ _
    ((continuous_id.mul (continuous_const.sub (clippingFunction_continuous hβ))).pow 2).continuousOn
    (by fun_prop)).mpr
  intro t ht
  exact discardedFunction_square_le_fourth hβ
    (spectrum_nonneg_of_nonneg (CFC.abs_nonneg x) ht)

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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralClipStar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
local instance clipBlockOrder_r6d6706_1 : PartialOrder (CStarMatrix (Fin 2) (Fin 2) A) :=
  CStarAlgebra.spectralOrder _
local instance clipBlockStarOrder_r6d6706_1 : StarOrderedRing (CStarMatrix (Fin 2) (Fin 2) A) :=
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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.graphReciprocalFlip_norm _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.tomitaGraphFirst_adjoint_apply _root_.OAI.KadisonKastler.tomitaGraphFirst_apply _root_.OAI.KadisonKastler.tomitaGraphFlip_one _root_.OAI.KadisonKastler.tomitaGraphFlip_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-- The right-coordinate clipping tail is controlled by the actual
fourth moment of the original vector state. -/
theorem vectorState_spectralClip_discard_right_le (Ω : H) {β : ℝ} (hβ : 0 < β)
    (x : H →L[ℂ] H) :
    ‖(x - spectralClip β x) Ω‖ ^ 2 ≤
      realVectorState Ω ((star x * x) ^ 2) / β ^ 2 := by
  have h := realVectorState_mono Ω (spectralClip_discard_fourth_bound hβ x)
  simpa only [realVectorState_star_mul_self, map_smul, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using h

/-- The same tail estimate holds on the adjoint coordinate. -/
theorem vectorState_spectralClip_discard_left_le (Ω : H) {β : ℝ} (hβ : 0 < β)
    (x : H →L[ℂ] H) :
    ‖star (x - spectralClip β x) Ω‖ ^ 2 ≤
      realVectorState Ω ((x * star x) ^ 2) / β ^ 2 := by
  simpa only [star_sub, star_spectralClip hβ, star_star] using
    vectorState_spectralClip_discard_right_le Ω hβ (star x)

/-- The weighted graph tail is controlled uniformly in the rescaling. -/
theorem norm_rescaledGraph_spectralClip_discard_sq_le
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) {β : ℝ} (hβ : 0 < β)
    (x : H →L[ℂ] H) :
    ‖rescaledGraphVector J Ω c (x - spectralClip β x)‖ ^ 2 ≤
      (realVectorState Ω ((star x * x) ^ 2) +
        c ^ 2 * realVectorState Ω ((x * star x) ^ 2)) / β ^ 2 := by
  rw [norm_rescaledGraphVector_sq]
  have hr := vectorState_spectralClip_discard_right_le Ω hβ x
  have hl := mul_le_mul_of_nonneg_left
    (vectorState_spectralClip_discard_left_le Ω hβ x) (sq_nonneg c)
  exact (add_le_add hr hl).trans_eq (by ring)

/-- The full cost also bounds the weighted fourth-moment tail. -/
theorem norm_rescaledGraph_spectralClip_discard_sq_le_cost
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) {β : ℝ} (hβ : 0 < β)
    (x : H →L[ℂ] H) :
    ‖rescaledGraphVector J Ω c (x - spectralClip β x)‖ ^ 2 ≤
      graphMomentCost Ω (c ^ 2) x / β ^ 2 := by
  refine (norm_rescaledGraph_spectralClip_discard_sq_le J Ω c hβ x).trans ?_
  apply div_le_div_of_nonneg_right _ (sq_nonneg β)
  unfold graphMomentCost
  have hr : 0 ≤ realVectorState Ω (star x * x) := by
    rw [realVectorState_star_mul_self]; positivity
  have hl : 0 ≤ realVectorState Ω (x * star x) := by
    simpa only [star_star] using
      (show 0 ≤ realVectorState Ω (star (star x) * star x) from by
        rw [realVectorState_star_mul_self]; positivity)
  nlinarith [mul_nonneg (sq_nonneg c) hl]

/-- The concrete cutoff 128 makes the graph-tail norm at most one eighth
whenever the sampled graph cost is at most 240. -/
theorem norm_rescaledGraph_spectralClip_128_discard_le_oai
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) (x : H →L[ℂ] H)
    (hcost : graphMomentCost Ω (c ^ 2) x ≤ 240) :
    ‖rescaledGraphVector J Ω c (x - spectralClip 128 x)‖ ≤ 1 / 8 := by
  have h := (norm_rescaledGraph_spectralClip_discard_sq_le_cost J Ω c
    (by norm_num : (0 : ℝ) < 128) x).trans
      (div_le_div_of_nonneg_right hcost (by norm_num : (0 : ℝ) ≤ 128 ^ 2))
  nlinarith [norm_nonneg (rescaledGraphVector J Ω c (x - spectralClip 128 x))]

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.norm_rescaledGraph_spectralClip_128_discard_le_oai.{u_1} := @OAI.KadisonKastler.norm_rescaledGraph_spectralClip_128_discard_le_oai.{u_1}
