-- Prove2me | solution 1 for OAI.KadisonKastler.projectionStrataCoordinates_operator_action
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:24:36.753139+00:00
-- url     : https://prove2.me/submissions/4ea3f140-3121-4fe4-992c-4d072535069c

import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Nat.Nth
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Definitions.Def_Q260K023

section
-- module Solutions.OAIQ075_KS.KadisonKastler_IsometryRangeCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Coordinates from two isometric embeddings with the same range -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

variable {E F K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace E] in
theorem isometryRangeCoordinates_intertwines (J : E →ₗᵢ[ℂ] K) (W : F →ₗᵢ[ℂ] K)
    (h : LinearMap.range J.toLinearMap = LinearMap.range W.toLinearMap) (v : E) :
    W (isometryRangeCoordinates J W h v) = J v := by
  obtain ⟨w, hw⟩ := show J v ∈ LinearMap.range W.toLinearMap from h ▸ ⟨v, rfl⟩
  have hw' : W w = J v := hw
  rw [isometryRangeCoordinates_apply, ← hw', isometry_adjoint_self_apply]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2ProjectionSynthesis
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # L² synthesis on a projection-rank stratum

The measurable orthonormal coordinates provide actual isometric inclusions
from the fixed-coordinate L² spaces into the original coefficient space.
-/

namespace KadisonKastler

open MeasureTheory
open scoped lp

noncomputable section

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

theorem projectionStratumAnalysis_synthesis (n : ℕ)
    (x : projectionRankStratum P b n) (v : ℓ²(projectionDimensionIndex n, ℂ)) :
    projectionStratumAnalysis P hP b hb n x
      (projectionStratumSynthesis P hP b hb n x v) = v := by
  apply (projectionStratumSynthesis P hP b hb n x).injective
  rw [projectionStratumSynthesis_analysis, projectionStratumSynthesis_fixed]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionStrataCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unitary coordinates for the original spectral subspace

The original isometric embedding and the assembled measurable rank strata
have the same range. Their comparison is the required genuine unitary.
-/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity
open scoped lp

noncomputable section

variable {X H E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (μ : Measure X) (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)
  (hPm : ∀ v, Measurable fun x => P x v)

theorem projectionStrataSynthesis_restrict (f : ProjectionStrataSpace μ P b) (n : ℕ) :
    l2Restrict μ (projectionRankStratum P b n)
        (measurableSet_projectionRankStratum P b hPm n)
        (projectionStrataSynthesis μ P hP b hb hPm f) =
      l2ProjectionStratumSynthesis P hP b hb hPm n (projectionStratumMeasure μ P b n) (f n) := by
  rw [← l2StrataCoordinates_apply μ (projectionRankStratum P b)
    (measurableSet_projectionRankStratum P b hPm)
    (projectionRankStratum_pairwise P b) (iUnion_projectionRankStratum P b)]
  change (projectionPartitionCoordinates μ P b hPm
    ((projectionPartitionCoordinates μ P b hPm).symm (hilbertSumIsometryMap _ f))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

variable (hPn : ∀ x, ‖P x‖ ≤ 1) (J : E →ₗᵢ[ℂ] Lp H 2 μ)
  (hJ : ∀ f : Lp H 2 μ, isometricExtension J 1 f =ᵐ[μ] fun x => P x (f x))

theorem projectionStrataCoordinates_intertwines (v : E) :
    projectionStrataSynthesis μ P hP b hb hPm
      (projectionStrataCoordinates μ P hP b hb hPm hPn J hJ v) = J v :=
  isometryRangeCoordinates_intertwines J _ _ v

theorem projectionStrataCoordinates_fiber_ae (v : E) (n : ℕ) :
    ∀ᵐ x : projectionRankStratum P b n ∂projectionStratumMeasure μ P b n,
      projectionStratumSynthesis P hP b hb n x
        (projectionStrataCoordinates μ P hP b hb hPm hPn J hJ v n x) = J v x.val := by
  let f := projectionStrataCoordinates μ P hP b hb hPm hPn J hJ v
  have hr := projectionStrataSynthesis_restrict μ P hP b hb hPm f n
  rw [projectionStrataCoordinates_intertwines] at hr
  filter_upwards [l2ProjectionStratumSynthesis_ae P hP b hb hPm n
      (projectionStratumMeasure μ P b n) (f n),
    l2Restrict_apply_ae μ (projectionRankStratum P b n)
      (measurableSet_projectionRankStratum P b hPm n) (J v)] with x hs hx
  exact hs.symm.trans ((congrArg (fun g => g x) hr).symm.trans hx)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionStratumFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transporting actual operator fields to the fixed-coordinate strata -/

namespace KadisonKastler

open MeasureTheory
open scoped lp

noncomputable section

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

variable [MeasurableSpace X] [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace.SeparableSpace H]

attribute [local instance] OAI.KadisonKastler.compressedCoordinateMeasurable
local instance compressedCoordinateBorel_r4a9c39_1 (n : ℕ) : BorelSpace ℓ²(projectionDimensionIndex n, ℂ) := ⟨rfl⟩
local instance compressedCoordinateSeparable_r4a9c39_1 (n : ℕ) :
    TopologicalSpace.SeparableSpace ℓ²(projectionDimensionIndex n, ℂ) :=
  separable_scalarHilbertCoordinates
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (μ : Measure X) (hPm : ∀ v, Measurable fun x => P x v) (hPn : ∀ x, ‖P x‖ ≤ 1)
  (J : E →ₗᵢ[ℂ] Lp H 2 μ)
  (hJ : ∀ f : Lp H 2 μ, KadisonSimilarity.isometricExtension J 1 f =ᵐ[μ]
    fun x => P x (f x))

theorem projectionStrataCoordinates_operator_action_oai
    (T : E →L[ℂ] E) (R : X → H →L[ℂ] H)
    (hRT : ∀ v : E, J (T v) =ᵐ[μ] fun x => R x (J v x)) (v : E) (n : ℕ) :
    ∀ᵐ x : projectionRankStratum P b n ∂projectionStratumMeasure μ P b n,
      projectionStrataCoordinates μ P hP b hb hPm hPn J hJ (T v) n x =
        compressedStratumField P hP b hb R n x
          (projectionStrataCoordinates μ P hP b hb hPm hPn J hJ v n x) := by
  have hr := (ae_restrict_iff_subtype (measurableSet_projectionRankStratum P b hPm n)).mp
    (ae_restrict_of_ae (hRT v))
  filter_upwards [projectionStrataCoordinates_fiber_ae μ P hP b hb hPm hPn J hJ (T v) n,
    projectionStrataCoordinates_fiber_ae μ P hP b hb hPm hPn J hJ v n, hr] with x ht hv hr
  let A := projectionStratumAnalysis P hP b hb n x
  calc
    _ = A (projectionStratumSynthesis P hP b hb n x
        (projectionStrataCoordinates μ P hP b hb hPm hPn J hJ (T v) n x)) :=
      (projectionStratumAnalysis_synthesis P hP b hb n x _).symm
    _ = A (J (T v) x.val) := congrArg A ht
    _ = A (R x.val (J v x.val)) := congrArg A hr
    _ = A (R x.val (projectionStratumSynthesis P hP b hb n x
        (projectionStrataCoordinates μ P hP b hb hPm hPn J hJ v n x))) :=
      congrArg (fun z => A (R x.val z)) hv.symm
    _ = _ := rfl

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonKastler.projectionStrataCoordinates_operator_action_oai.{u_1, u_2, u_3} := @OAI.KadisonKastler.projectionStrataCoordinates_operator_action_oai.{u_1, u_2, u_3}
