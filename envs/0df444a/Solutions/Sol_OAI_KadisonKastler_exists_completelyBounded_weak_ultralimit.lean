-- Prove2me | solution 1 for OAI.KadisonKastler.exists_completelyBounded_weak_ultralimit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:07:05.141985+00:00
-- url     : https://prove2.me/submissions/d8508ff7-6a06-473d-91bf-2b620a8698fe

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
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
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Q260K014

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FaithfulRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakMatrixLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Uniform rectangular matrix bounds are closed under entrywise weak limits. -/

namespace KadisonKastler

noncomputable section

open Filter Generator
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.weakMatrixStarOrder
theorem weak_operator_ultralimit_norm_le {ι : Type*} (ω : Ultrafilter ι)
    (F : ι → H →L[ℂ] H) (T : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ i, ‖F i‖ ≤ c)
    (ht : ∀ ξ η, Tendsto (fun i => inner ℂ η (F i ξ)) (ω : Filter ι)
      (𝓝 (inner ℂ η (T ξ)))) : ‖T‖ ≤ c := by
  obtain ⟨S, hS, hs⟩ := Tracial.exists_weak_operator_ultralimit ω F c hc hF
  have he : S = T := by
    ext ξ
    apply ext_inner_left ℂ
    intro η
    exact tendsto_nhds_unique (hs ξ η) (ht ξ η)
  rwa [he] at hS

attribute [local instance] OAI.KadisonKastler.weakMatrixOrder
theorem square_matrix_ultralimit_norm_le {ι n : Type*} [Fintype n] [DecidableEq n]
    (ω : Ultrafilter ι) (F : ι → CStarMatrix n n (H →L[ℂ] H))
    (T : CStarMatrix n n (H →L[ℂ] H)) {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ i, ‖F i‖ ≤ c)
    (ht : ∀ a b ξ η, Tendsto (fun i => inner ℂ η (F i a b ξ)) (ω : Filter ι)
      (𝓝 (inner ℂ η (T a b ξ)))) : ‖T‖ ≤ c := by
  rw [← norm_hilbertMatrix]
  apply weak_operator_ultralimit_norm_le ω (fun i => hilbertMatrix (F i)) _ hc
  · intro i
    rw [norm_hilbertMatrix]
    exact hF i
  · intro ξ η
    simp only [PiLp.inner_apply, hilbertMatrix_apply, inner_sum]
    exact tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ =>
      ht a b (ξ b) (η a)

theorem rectangular_matrix_ultralimit_norm_le {ι m n : Type*} [Fintype m] [Fintype n]
    (ω : Ultrafilter ι) (F : ι → CStarMatrix m n (H →L[ℂ] H))
    (T : CStarMatrix m n (H →L[ℂ] H)) {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ i, ‖F i‖ ≤ c)
    (ht : ∀ a b ξ η, Tendsto (fun i => inner ℂ η (F i a b ξ)) (ω : Filter ι)
      (𝓝 (inner ℂ η (T a b ξ)))) : ‖T‖ ≤ c := by
  classical
  rw [← norm_rectangularCorner]
  apply square_matrix_ultralimit_norm_le ω (fun i => rectangularCorner (F i)) _ hc
  · intro i
    rw [norm_rectangularCorner]
    exact hF i
  · intro a b ξ η
    rcases a with a | a <;> rcases b with b | b
    · simpa only [rectangularCorner] using
        (tendsto_const_nhds : Tendsto (fun _ : ι => inner ℂ η ((0 : H →L[ℂ] H) ξ))
          (ω : Filter ι) (𝓝 (inner ℂ η ((0 : H →L[ℂ] H) ξ))))
    · exact ht a b ξ η
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompleteWeakLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.conjugateLinear_one _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe _root_.OAI.UltrapowerBridge.quotientMap_smul _root_.OAI.UltrapowerBridge.quotientMap_star _root_.OAI.UltrapowerBridge.quotientTrace_mk _root_.OAI.UltrapowerBridge.quotientTrace_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Completely bounded maps into a concrete von Neumann algebra have weak ultralimits. -/

namespace KadisonKastler

noncomputable section

open Filter Generator
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.completeWeakOperatorOrder
local instance completeWeakOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

attribute [local instance] OAI.KadisonKastler.completeWeakAlgebraOrder
attribute [local instance] OAI.KadisonKastler.completeWeakAlgebraStarOrder
theorem completelyBoundedBy_of_weak_operator_ultralimit (M : VonNeumannAlgebra H)
    {ι : Type*} (ω : Ultrafilter ι) (F : ι → Algebra M →ₗ[ℂ] Algebra M)
    (L : Algebra M →ₗ[ℂ] Algebra M) {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ i, CompletelyBoundedBy (F i) c)
    (ht : ∀ a ξ η, Tendsto (fun i => inner ℂ η ((F i a : H →L[ℂ] H) ξ))
      (ω : Filter ι) (𝓝 (inner ℂ η ((L a : H →L[ℂ] H) ξ)))) :
    CompletelyBoundedBy L c := by
  let e := M.toStarSubalgebra.subtype
  have he := injective_starAlgHom_completelyIsometric e Subtype.val_injective
  intro p q X
  have h := rectangular_matrix_ultralimit_norm_le ω
    (fun i => CStarMatrix.mapₗ e.toAlgHom.toLinearMap (CStarMatrix.mapₗ (F i) X))
    (CStarMatrix.mapₗ e.toAlgHom.toLinearMap (CStarMatrix.mapₗ L X))
    (mul_nonneg hc (norm_nonneg X))
    (fun i => by rw [he]; exact hF i p q X)
    (fun a b ξ η => ht (X a b) ξ η)
  rwa [he] at h

/-- Pointwise weak compactness preserves the full matrix norm bound. -/
theorem exists_completelyBounded_weak_ultralimit_oai (M : VonNeumannAlgebra H)
    {ι : Type*} (ω : Ultrafilter ι) (F : ι → Algebra M →ₗ[ℂ] Algebra M)
    {c : ℝ} (hc : 0 ≤ c) (hF : ∀ i, CompletelyBoundedBy (F i) c) :
    ∃ L : Algebra M →ₗ[ℂ] Algebra M, CompletelyBoundedBy L c ∧
      ∀ a ξ η, Tendsto (fun i => inner ℂ η ((F i a : H →L[ℂ] H) ξ))
        (ω : Filter ι) (𝓝 (inner ℂ η ((L a : H →L[ℂ] H) ξ))) := by
  choose E hE ht using fun a : Algebra M => Tracial.exists_weak_operator_ultralimit ω
    (fun i => (F i a : H →L[ℂ] H)) (c * ‖a‖) (mul_nonneg hc (norm_nonneg a))
    (fun i => (hF i).apply_norm_le a)
  have hmem (a : Algebra M) : E a ∈ M :=
    Tracial.weak_operator_limit_mem M (fun i => F i a) (E a) (ht a)
  have hadd (a b : Algebra M) : E (a + b) = E a + E b := by
    ext ξ
    apply ext_inner_left ℂ
    intro η
    apply tendsto_nhds_unique (ht (a + b) ξ η)
    simpa [inner_add_right] using (ht a ξ η).add (ht b ξ η)
  have hsmul (z : ℂ) (a : Algebra M) : E (z • a) = z • E a := by
    ext ξ
    apply ext_inner_left ℂ
    intro η
    apply tendsto_nhds_unique (ht (z • a) ξ η)
    simpa [inner_smul_right] using (ht a ξ η).const_mul z
  let L : Algebra M →ₗ[ℂ] Algebra M :=
    { toFun := fun a => ⟨E a, hmem a⟩
      map_add' := fun a b => Subtype.ext (hadd a b)
      map_smul' := fun z a => Subtype.ext (hsmul z a) }
  exact ⟨L, completelyBoundedBy_of_weak_operator_ultralimit M ω F L hc hF ht, ht⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.exists_completelyBounded_weak_ultralimit_oai.{u_1, u_2} := @OAI.KadisonKastler.exists_completelyBounded_weak_ultralimit_oai.{u_1, u_2}
