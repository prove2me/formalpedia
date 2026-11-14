-- Prove2me | solution 1 for OAI.KadisonKastler.quadraticCochainSolver_of_modular_rows
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T19:08:46.878842+00:00
-- url     : https://prove2.me/submissions/d78c90be-44db-4aa8-aa56-ff2ee4d473ee

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Q260K020
import Theorems.Thm_OAI_KadisonKastler_HaagerupBound_finiteCochainAverage
import Theorems.Thm_OAI_KadisonKastler_HaagerupBound_right_slice
import Theorems.Thm_OAI_KadisonKastler_HaagerupBound_smul
import Theorems.Thm_OAI_KadisonKastler_cochainSymmetrize_bound
import Theorems.Thm_OAI_KadisonKastler_cochainSymmetrize_residual_bound
import Theorems.Thm_OAI_KadisonKastler_cochainSymmetrize_star
import Theorems.Thm_OAI_KadisonKastler_cochain_coboundary_weak_limit
import Theorems.Thm_OAI_KadisonKastler_exists_completelyBounded_weak_ultralimit
import Theorems.Thm_OAI_KadisonKastler_finiteAveragedDifferential_defect_bound
import Theorems.Thm_OAI_KadisonKastler_finiteCochainModuleDefect_as_average
import Theorems.Thm_OAI_KadisonKastler_haagerupBound_of_weak_operator_ultralimit

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AsymptoticRowCochain
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.conjugateLinear_one _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe _root_.OAI.UltrapowerBridge.quotientMap_smul _root_.OAI.UltrapowerBridge.quotientMap_star _root_.OAI.UltrapowerBridge.quotientTrace_mk _root_.OAI.UltrapowerBridge.quotientTrace_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Passage from asymptotically modular row averages to a quadratic cochain.
The asymptotic modularity hypothesis is explicit; its general construction is
not asserted by this adapter. -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.asymptoticRowAlgebraOrder
attribute [local instance] OAI.KadisonKastler.asymptoticRowAlgebraStarOrder
/-- Asymptotically right-modular normalized rows produce the exact local
cochain estimate used by the Newton iteration. -/
theorem quadratic_cochain_of_asymptotic_rows (M : VonNeumannAlgebra H)
    (m : Algebra M →ₗ[ℂ] Algebra M →ₗ[ℂ] Algebra M)
    (hm : ∀ x y z, m (m x y) z = m x (m y z))
    (hstar : ∀ x y, star (m x y) = m (star y) (star x))
    {c : ℝ} (hc : 0 ≤ c) (hf : HaagerupBound (m - LinearMap.mul ℂ (Algebra M)) c)
    {ι : Type*} (ω : Ultrafilter ι) (n : ι → ℕ) (r : (i : ι) → Fin (n i) → Algebra M)
    (hr : ∀ i, ∑ k, r i k * star (r i k) = 1)
    (hmod : ∀ a b ξ η, Tendsto
      (fun i => inner ℂ η ((finiteCochainModuleDefect (r i)
        (m - LinearMap.mul ℂ (Algebra M)) a b : H →L[ℂ] H) ξ))
      (ω : Filter ι) (𝓝 0)) :
    ∃ D : Algebra M →ₗ[ℂ] Algebra M, CompletelyBoundedBy D c ∧
      (∀ x, D (star x) = star (D x)) ∧
      HaagerupBound (m - LinearMap.mul ℂ (Algebra M) - linearCoboundary D) (2 * c ^ 2) := by
  let f := m - LinearMap.mul ℂ (Algebra M)
  let F (i : ι) := finiteCochainAverage (r i) f
  have hF (i : ι) : CompletelyBoundedBy (F i) c := hf.finiteCochainAverage hc (r i) (hr i)
  obtain ⟨L, hL, ht⟩ := exists_completelyBounded_weak_ultralimit M ω F hc hF
  have hd := cochain_coboundary_weak_limit M ω F L ht
  let G (i : ι) := -finiteAveragedDifferential (r i) f
  have hG (i : ι) : HaagerupBound (G i) (2 * c ^ 2) := by
    have h := (finiteAveragedDifferential_defect_bound (r i) (hr i) m hm hc hf).smul (-1 : ℂ)
    have he : (-1 : ℂ) • finiteAveragedDifferential (r i) f = G i := by
      apply LinearMap.ext
      intro a
      apply LinearMap.ext
      intro b
      change (-1 : ℂ) • finiteAveragedDifferential (r i) f a b =
        -finiteAveragedDifferential (r i) f a b
      rw [neg_smul, one_smul]
    change HaagerupBound ((-1 : ℂ) • finiteAveragedDifferential (r i) f)
      (‖(-1 : ℂ)‖ * (2 * c ^ 2)) at h
    rw [he] at h
    simpa only [norm_neg, norm_one, one_mul] using h
  have htG (a b : Algebra M) (ξ η : H) :
      Tendsto (fun i => inner ℂ η ((G i a b : H →L[ℂ] H) ξ))
        (ω : Filter ι) (𝓝 (inner ℂ η (((f - linearCoboundary L) a b : H →L[ℂ] H) ξ))) := by
    have he (i : ι) : G i a b = f a b - linearCoboundary (F i) a b -
        finiteCochainModuleDefect (r i) f a b := by
      change -(finiteCochainModuleDefect (r i) f a b -
        (f a b - linearCoboundary (F i) a b)) = _
      abel
    simp_rw [he]
    have hconst : Tendsto (fun _ : ι => inner ℂ η ((f a b : H →L[ℂ] H) ξ))
        (ω : Filter ι) (𝓝 (inner ℂ η ((f a b : H →L[ℂ] H) ξ))) := tendsto_const_nhds
    have h := (hconst.sub (hd a b ξ η)).sub (hmod a b ξ η)
    simpa [f, inner_sub_right] using h
  have hres := haagerupBound_of_weak_operator_ultralimit M ω G (f - linearCoboundary L)
    (by positivity) hG htG
  have hs : ∀ x y, star (f x y) = f (star y) (star x) := by
    intro x y
    simp [f, hstar, star_sub, star_mul]
  exact ⟨cochainSymmetrize L, cochainSymmetrize_bound hL, cochainSymmetrize_star L,
    cochainSymmetrize_residual_bound hs L hres⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MultiplicationCorrectionFromRows
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Multiplication correction from Christensen--Sinclair row averaging

A modular row limit supplies the cochain estimate for multiplication correction.
-/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.correctionRowsOrder
attribute [local instance] OAI.KadisonKastler.correctionRowsStarOrder
private theorem cochain_module_defect_tendsto (M : VonNeumannAlgebra H)
    {ι : Type*} (ω : Ultrafilter ι) (n : ι → ℕ)
    (r : (i : ι) → Fin (n i) → Algebra M)
    (f : Algebra M →ₗ[ℂ] Algebra M →ₗ[ℂ] Algebra M) {c : ℝ}
    (hc : 0 ≤ c) (hf : HaagerupBound f c)
    (hav : ∀ (F : Algebra M →ₗ[ℂ] Algebra M) (c : ℝ), 0 ≤ c → CompletelyBoundedBy F c →
      ∃ z : Algebra M, ∀ y ξ η, Tendsto
        (fun i => inner ℂ η ((finiteRightAverage (r i) F y : H →L[ℂ] H) ξ))
        (ω : Filter ι) (𝓝 (inner ℂ η (((z * y : Algebra M) : H →L[ℂ] H) ξ))))
    (a b : Algebra M) (ξ η : H) :
    Tendsto (fun i => inner ℂ η ((finiteCochainModuleDefect (r i) f a b : H →L[ℂ] H) ξ))
      (ω : Filter ι) (𝓝 0) := by
  obtain ⟨z, hz⟩ := hav (f a) (c * ‖a‖) (mul_nonneg hc (norm_nonneg a))
    (hf.right_slice hc a)
  have h := (hz b ξ η).sub (hz 1 ((b : H →L[ℂ] H) ξ) η)
  simp_rw [finiteCochainModuleDefect_as_average]
  simpa only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, sub_apply,
    mul_apply_eq_comp, inner_sub_right, mul_one, sub_self] using h

theorem quadraticCochainSolver_of_modular_rows_oai (M : VonNeumannAlgebra H)
    {ι : Type*} (ω : Ultrafilter ι) (n : ι → ℕ)
    (r : (i : ι) → Fin (n i) → Algebra M)
    (hr : ∀ i, ∑ k, r i k * star (r i k) = 1)
    (hav : ∀ (F : Algebra M →ₗ[ℂ] Algebra M) (c : ℝ), 0 ≤ c → CompletelyBoundedBy F c →
      ∃ z : Algebra M, ∀ y ξ η, Tendsto
        (fun i => inner ℂ η ((finiteRightAverage (r i) F y : H →L[ℂ] H) ξ))
        (ω : Filter ι) (𝓝 (inner ℂ η (((z * y : Algebra M) : H →L[ℂ] H) ξ)))) :
    QuadraticCochainSolver (Algebra M) := by
  intro c hc _ m
  exact quadratic_cochain_of_asymptotic_rows M m.mul m.assoc m.star_mul hc m.bound ω n r hr
    (cochain_module_defect_tendsto M ω n r (m.mul - LinearMap.mul ℂ (Algebra M)) hc m.bound hav)

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.quadraticCochainSolver_of_modular_rows_oai.{u_1, u_2} := @OAI.KadisonKastler.quadraticCochainSolver_of_modular_rows_oai.{u_1, u_2}
