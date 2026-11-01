-- Prove2me | solution 1 for OAI.KadisonSimilarity.finite_standard_bound_of_local_free_corner
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T15:03:20.594549+00:00
-- url     : https://prove2.me/submissions/f2775121-4016-46ef-89aa-8f114829b1dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A036
import Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_exists_smallFreeCornerData_of_normal_matrix_tower
import Theorems.Thm_OAI_KadisonSimilarity_canonicalFreeFactorComparison
import Theorems.Thm_OAI_KadisonSimilarity_finite_standard_estimate_of_centered_tests
import Theorems.Thm_OAI_KadisonSimilarity_original_symmetry_bound_of_free_corner

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Constants
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical constants fixed by the manuscript. -/

noncomputable section

namespace KadisonSimilarity

theorem rowConstant_pos : 0 < rowConstant := by unfold rowConstant; positivity

theorem cyclicConstant_pos : 0 < cyclicConstant := by
  unfold cyclicConstant
  have := rowConstant_pos
  positivity

theorem cornerConstant_pos : 0 < cornerConstant := by
  unfold cornerConstant
  have := cyclicConstant_pos
  positivity

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralStepDischarge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete spectral cut projections

We construct the spectral cuts from the closed range of the positive part.
The construction takes place in the represented Hilbert space; bicommutant
closure proves membership in the given von Neumann algebra.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem rangeSupport_isStarProjection (B : H →L[ℂ] H) :
    IsStarProjection (rangeSupport B) :=
  ⟨Submodule.isIdempotentElem_starProjection _, isSelfAdjoint_starProjection _⟩

theorem rangeSupport_mul (B : H →L[ℂ] H) : rangeSupport B * B = B := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr
    (Submodule.le_topologicalClosure _ ⟨x, rfl⟩)

theorem mul_rangeSupport (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) :
    B * rangeSupport B = B := by
  have h := congrArg star (rangeSupport_mul B)
  simpa only [star_mul, hB.star_eq, (rangeSupport_isStarProjection B).isSelfAdjoint.star_eq]
    using h

/-- Annihilating the range also annihilates its orthogonal support. -/
theorem mul_rangeSupport_eq_zero (B C : H →L[ℂ] H) (h : C * B = 0) :
    C * rangeSupport B = 0 := by
  have hh : operatorRangeClosure B ≤ C.ker := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨x, rfl⟩
      exact congrArg (fun S : H →L[ℂ] H => S x) h
    · exact C.isClosed_ker
  ext x
  exact hh ((operatorRangeClosure B).starProjection_apply_mem x)

/-- Multiplication by a cut removes the negative part of the shifted operator. -/
theorem shifted_mul_upperSpectralCut (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    (A - t • 1) * upperSpectralCut A t = (A - t • 1)⁺ := by
  let B := A - t • (1 : H →L[ℂ] H)
  have hB : IsSelfAdjoint B := by
    dsimp [B]
    exact hA.sub ((IsSelfAdjoint.all t).smul (IsSelfAdjoint.one (H →L[ℂ] H)))
  change B * rangeSupport B⁺ = B⁺
  nth_rw 1 [← CFC.posPart_sub_negPart B hB]
  rw [sub_mul]
  rw [mul_rangeSupport B⁺ (CFC.posPart_nonneg B).isSelfAdjoint,
    mul_rangeSupport_eq_zero B⁺ B⁻ (CFC.negPart_mul_posPart B), sub_zero]

theorem shifted_mul_complement_upperSpectralCut (A : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (t : ℝ) :
    (A - t • 1) * (1 - upperSpectralCut A t) = -(A - t • 1)⁻ := by
  rw [mul_sub, mul_one, shifted_mul_upperSpectralCut A hA t]
  have hB : IsSelfAdjoint (A - t • (1 : H →L[ℂ] H)) :=
    hA.sub ((IsSelfAdjoint.all t).smul (IsSelfAdjoint.one (H →L[ℂ] H)))
  nth_rw 1 [← CFC.posPart_sub_negPart _ hB]
  abel


end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixVonNeumannRange
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete von Neumann algebra of finite operator matrices

The commutant of the diagonally amplified commutant consists exactly of
operator matrices with entries in the original von Neumann algebra. This
constructs the normal matrix realization used by spectral rounding.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Pointwise

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Represented
variable {A : Type*} [CStarAlgebra A]

/-- A faithful representation remains faithful on finite matrices. -/
theorem representedMatrixHom_injective (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : Function.Injective σ) (n : ℕ) : Function.Injective (representedMatrixHom σ n) := by
  intro X Y h
  ext i j
  apply hσ
  calc
    σ (X i j) = matrixEntryCompression i j (representedMatrixHom σ n X) :=
      (matrixEntryCompression_matrixOperator (fun k l => σ (X k l)) i j).symm
    _ = matrixEntryCompression i j (representedMatrixHom σ n Y) :=
      congrArg (matrixEntryCompression i j) h
    _ = σ (Y i j) :=
      matrixEntryCompression_matrixOperator (fun k l => σ (Y k l)) i j


end Represented

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialSubalgebraModels
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal algebra generated inside the ultrapower is represented on
its own tracial GNS space. Restriction of the positive trace and its exact
Hilbert-space identification require no further analytic input. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {P : Type*} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (L : StarSubalgebra ℂ P) [IsClosed (L : Set P)]

/-- Its range is exactly the completed algebra-vector subspace. -/
theorem restrictedTracialGNSInclusion_range
    (htr : ∀ a b : P, τ (a * b) = τ (b * a)) :
    Set.range (restrictedTracialGNSInclusion τ L) =
      ((gnsTracialGeometry τ htr).baseSpace L : Set τ.GNS) := by
  let J := restrictedTracialGNSInclusion τ L
  have hc : IsClosed (Set.range J) := J.isometry.isClosedEmbedding.isClosed_range
  apply Set.Subset.antisymm
  · rintro _ ⟨ξ, rfl⟩
    refine (gnsTracialVector_dense (restrictedPositiveTrace τ L)).induction_on ξ
      (((gnsTracialGeometry τ htr).baseSpace L).isClosed.preimage J.continuous) ?_
    intro a
    rw [restrictedTracialGNSInclusion_vector]
    exact ((gnsTracialGeometry τ htr).baseVector L a).property
  · change closure (Set.range ((gnsTracialGeometry τ htr).baseAlgebraVectors L)) ⊆ _
    apply closure_minimal _ hc
    rintro _ ⟨a, rfl⟩
    exact ⟨gnsTracialVector (restrictedPositiveTrace τ L) a,
      restrictedTracialGNSInclusion_vector τ L a⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialL2Closure
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded elements in the L² closure of a star subalgebra form an
actual norm-closed star subalgebra. Multiplication is obtained from the
commuting left and right tracial actions, rather than assumed as a property
of a proposed generated algebra. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

open scoped CStarAlgebra ComplexOrder

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

/-- Inclusion of algebras induces inclusion of their closed Hilbert spans. -/
theorem baseSpace_mono {S T : StarSubalgebra ℂ P} (hST : S ≤ T) :
    G.baseSpace S ≤ G.baseSpace T := by
  change closure (Set.range (G.baseAlgebraVectors S)) ⊆
    closure (Set.range (G.baseAlgebraVectors T))
  apply closure_mono
  rintro x ⟨a, rfl⟩
  exact ⟨⟨(a : P), hST a.property⟩, rfl⟩

/-- Taking the norm closure of the algebra does not change its L² span. -/
theorem baseSpace_topologicalClosure (S : StarSubalgebra ℂ P) :
    G.baseSpace S.topologicalClosure = G.baseSpace S := by
  apply le_antisymm
  · change closure (Set.range (G.baseAlgebraVectors S.topologicalClosure)) ⊆
      (G.baseSpace S : Set H)
    apply closure_minimal _ (G.baseSpace S).isClosed
    rintro x ⟨a, rfl⟩
    have hc : closure (S : Set P) ⊆ G.vector ⁻¹' (G.baseSpace S : Set H) := by
      apply closure_minimal _ ((G.baseSpace S).isClosed.preimage G.vector_continuous)
      intro b hb
      exact (G.baseVector S ⟨b, hb⟩).property
    exact hc a.property
  · exact G.baseSpace_mono S.le_topologicalClosure

section ClosedSeed

variable (S : StarSubalgebra ℂ P) [hSclosed : IsClosed (S : Set P)]

/-- Passing to the constructed bounded algebra leaves the Hilbert space
unchanged. -/
theorem baseSpace_l2ClosureAlgebra : G.baseSpace (G.l2ClosureAlgebra S) = G.baseSpace S := by
  apply le_antisymm
  · change closure (Set.range (G.baseAlgebraVectors (G.l2ClosureAlgebra S))) ⊆
      (G.baseSpace S : Set H)
    apply closure_minimal _ (G.baseSpace S).isClosed
    rintro x ⟨a, rfl⟩
    exact a.property
  · exact G.baseSpace_mono (G.le_l2ClosureAlgebra S)

end ClosedSeed

/-- The generated algebra has precisely the original seed's Hilbert span. -/
theorem baseSpace_l2GeneratedAlgebra (S : StarSubalgebra ℂ P) :
    G.baseSpace (G.l2GeneratedAlgebra S) = G.baseSpace S := by
  have : IsClosed (S.topologicalClosure : Set P) := S.isClosed_topologicalClosure
  exact (G.baseSpace_l2ClosureAlgebra S.topologicalClosure).trans
    (G.baseSpace_topologicalClosure S)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialSmallCornerTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small-corner commutator estimate transports along a partial isometry
in the algebra commuting with the implementing operator. Projection
comparison then supplies that partial isometry in the prescribed factor. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

/-- A partial isometry is contractive, including when its initial projection
is zero. -/
theorem norm_le_one_of_initial_projection (v f : P) (hf : IsStarProjection f)
    (hv : star v * v = f) : ‖v‖ ≤ 1 := by
  have hfn : ‖f‖ * ‖f‖ = ‖f‖ := by
    rw [← CStarRing.norm_star_mul_self, hf.isSelfAdjoint.star_eq, hf.isIdempotentElem.eq]
  have hfn' : ‖f‖ ≤ 1 := by nlinarith [norm_nonneg f]
  have hvn : ‖v‖ * ‖v‖ = ‖f‖ := by rw [← CStarRing.norm_star_mul_self, hv]
  nlinarith [norm_nonneg v]

/-- The original corner element is recovered exactly. -/
theorem partialIsometryCornerMap_recover (e f : P)
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (v : P) (hv : star v * v = f) (hev : e * (v * star v) = v * star v)
    (z : CStarCorner f hf) :
    star v * (partialIsometryCornerMap e f he hf v hv hev z : P) * v = z := by
  change star v * (v * (z : P) * star v) * v = z
  calc
    _ = (star v * v) * (z : P) * (star v * v) := by noncomm_ring
    _ = z := by rw [hv, z.property.1, z.property.2]

theorem norm_partialIsometryCornerMap_le (e f : P)
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (v : P) (hv : star v * v = f) (hev : e * (v * star v) = v * star v)
    (z : CStarCorner f hf) :
    ‖partialIsometryCornerMap e f he hf v hv hev z‖ ≤ ‖z‖ := by
  have hn := norm_le_one_of_initial_projection v f hf hv
  change ‖v * (z : P) * star v‖ ≤ ‖(z : P)‖
  calc
    _ ≤ (‖v‖ * ‖(z : P)‖) * ‖star v‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖(z : P)‖) * 1 := by rw [norm_star]; gcongr
    _ = ‖(z : P)‖ := by ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Algebraic transport, before using any projection comparison theorem. -/
theorem corner_commutator_bound_of_partial_isometry
    (L : P →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (e f : P) (he : IsStarProjection e) (hf : IsStarProjection f)
    (v : P) (hv : star v * v = f) (hev : e * (v * star v) = v * star v)
    (hTv : T * L v = L v * T) (hTvs : T * L (star v) = L (star v) * T)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ x : CStarCorner e he, ‖commutator T (L (x : P))‖ ≤ ε * ‖x‖) :
    ∀ z : CStarCorner f hf, ‖commutator T (L (z : P))‖ ≤ ε * ‖z‖ := by
  intro z
  let x := partialIsometryCornerMap e f he hf v hv hev z
  have hz : L (z : P) = L (star v) * L (x : P) * L v := by
    rw [← map_mul, ← map_mul]
    exact congrArg L (partialIsometryCornerMap_recover e f he hf v hv hev z).symm
  have hc : commutator T (L (z : P)) =
      L (star v) * commutator T (L (x : P)) * L v := by
    rw [hz]
    unfold commutator
    calc
      _ = (T * L (star v)) * L (x : P) * L v -
          L (star v) * L (x : P) * (L v * T) := by noncomm_ring
      _ = (L (star v) * T) * L (x : P) * L v -
          L (star v) * L (x : P) * (T * L v) := by rw [hTvs, ← hTv]
      _ = _ := by noncomm_ring
  have hvn : ‖L v‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le L v).trans (norm_le_one_of_initial_projection v f hf hv)
  have hvsn : ‖L (star v)‖ ≤ 1 := by
    rw [map_star, norm_star]
    exact hvn
  rw [hc]
  calc
    _ ≤ (‖L (star v)‖ * ‖commutator T (L (x : P))‖) * ‖L v‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * (ε * ‖x‖)) * 1 := by gcongr; exact hbound x
    _ ≤ ε * ‖z‖ := by
      simpa only [one_mul, mul_one] using
        mul_le_mul_of_nonneg_left (norm_partialIsometryCornerMap_le e f he hf v hv hev z) hε

/-- Projection comparison can be performed in a separate included factor;
the resulting partial isometry is then mapped into the represented algebra. -/
theorem corner_commutator_bound_of_hom_comparison
    {A : Type*} [CStarAlgebra A] (φ : A →⋆ₐ[ℂ] P)
    (L : P →⋆ₐ[ℂ] (H →L[ℂ] H))
    (τ : A → ℝ) (comparison : FiniteFactorProjectionComparison τ)
    (e f : A) (he : IsStarProjection e) (hf : IsStarProjection f)
    (htrace : τ f ≤ τ e) (T : H →L[ℂ] H)
    (hcomm : ∀ a : A, T * L (φ a) = L (φ a) * T)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ z : CStarCorner (φ e) (he.map φ),
      ‖commutator T (L (z : P))‖ ≤ ε * ‖z‖) :
    ∀ z : CStarCorner (φ f) (hf.map φ),
      ‖commutator T (L (z : P))‖ ≤ ε * ‖z‖ := by
  obtain ⟨v, hv, hev⟩ := comparison e f he hf htrace
  have hvP : star (φ v) * φ v = φ f := by rw [← map_star, ← map_mul, hv]
  have hevP : φ e * (φ v * star (φ v)) = φ v * star (φ v) := by
    simpa only [map_mul, map_star] using congrArg φ hev
  exact corner_commutator_bound_of_partial_isometry L T (φ e) (φ f) (he.map φ)
    (hf.map φ) (φ v) hvP hevP (hcomm v) (by simpa only [map_star] using hcomm (star v))
    hε hbound

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralRoundingDischarge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The one-half spectral rounding inequality

The cutoff is the support of the positive part of `2a-1`.  Its polynomial
order inequality implies the required L² inequality for every positive
functional on a concrete von Neumann algebra.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem halfSpectralProjection_isStarProjection (a : H →L[ℂ] H) :
    IsStarProjection (halfSpectralProjection a) := rangeSupport_isStarProjection _

theorem halfSpectralProjection_commutes (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    Commute (halfSpectralProjection a) a := by
  have h : Commute (2 * a - 1) a := by
    change (2 * a - 1) * a = a * (2 * a - 1)
    noncomm_ring
  have hp : Commute (2 * a - 1)⁺ a := by
    rw [CFC.posPart_def]
    exact h.cfcₙ_real _
  exact rangeSupport_commutes _ a hp (by simpa only [ha.star_eq] using hp)

/-- Pure operator order form of the scalar cutoff estimate. -/
theorem halfSpectralProjection_square_le (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    (halfSpectralProjection a - a) ^ 2 ≤ 4 * (a * a - a) ^ 2 := by
  let p := halfSpectralProjection a
  let q := 1 - p
  let x := 2 * a - 1
  have hp : IsStarProjection p := halfSpectralProjection_isStarProjection a
  have hpa : Commute p a := halfSpectralProjection_commutes a ha
  have hpp : p * p = p := hp.isIdempotentElem.eq
  have hppt (b : H →L[ℂ] H) : p * (p * b) = p * b := by rw [← mul_assoc, hpp]
  have hxt : IsSelfAdjoint x := by
    change star (2 * a - 1) = 2 * a - 1
    simp only [star_sub, star_mul, star_ofNat, star_one, ha.star_eq]
    noncomm_ring
  have hxpos : 0 ≤ x * p := by
    have he := shifted_mul_upperSpectralCut x hxt 0
    have he' : x * p = x⁺ := by simpa only [zero_smul, sub_zero, upperSpectralCut, p,
      halfSpectralProjection, x] using he
    rw [he']
    exact CFC.posPart_nonneg x
  have hxneg : 0 ≤ (-x) * q := by
    have he := shifted_mul_complement_upperSpectralCut x hxt 0
    have he' : x * q = -x⁻ := by simpa only [zero_smul, sub_zero, upperSpectralCut, p, q,
      halfSpectralProjection, x] using he
    simpa only [neg_mul, he', neg_neg] using CFC.negPart_nonneg x
  have hfirst : 0 ≤ 4 * a ^ 2 * p - p := by
    have hid : 4 * a ^ 2 * p - p = (x * p) ^ 2 + 2 • (x * p) := by
      dsimp [x]
      noncomm_ring [hpa.eq, hpa.left_comm, hpp, hppt]
    rw [hid]
    exact add_nonneg hxpos.isSelfAdjoint.sq_nonneg (nsmul_nonneg hxpos 2)
  have hsecond : 0 ≤ 4 * (a - 1) ^ 2 * q - q := by
    have hid : 4 * (a - 1) ^ 2 * q - q = ((-x) * q) ^ 2 + 2 • ((-x) * q) := by
      dsimp [x, q]
      noncomm_ring [hpa.eq, hpa.left_comm, hpp, hppt]
    rw [hid]
    exact add_nonneg hxneg.isSelfAdjoint.sq_nonneg (nsmul_nonneg hxneg 2)
  have h1 := star_left_conjugate_nonneg hfirst (a - 1)
  have h2 := star_left_conjugate_nonneg hsecond a
  have heq : star (a - 1) * (4 * a ^ 2 * p - p) * (a - 1) +
      star a * (4 * (a - 1) ^ 2 * q - q) * a =
      4 * (a * a - a) ^ 2 - (p - a) ^ 2 := by
    simp only [star_sub, ha.star_eq, star_one]
    dsimp [q]
    noncomm_ring [hpa.eq, hpa.left_comm, hpp, hppt]
  apply sub_nonneg.mp
  rw [← heq]
  exact add_nonneg h1 h2

/-- Passing the polynomial order estimate through a positive functional. -/
theorem preGNS_rounding_norm_le {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (τ : A →ₚ[ℂ] ℂ) (a p : A)
    (ha : IsSelfAdjoint a) (hp : IsSelfAdjoint p)
    (horder : (p - a) ^ 2 ≤ 4 * (a * a - a) ^ 2) :
    ‖τ.toPreGNS (p - a)‖ ≤ 2 * ‖τ.toPreGNS (a * a - a)‖ := by
  have hτ := τ.monotone horder
  have hpa : IsSelfAdjoint (p - a) := hp.sub ha
  have hdef : IsSelfAdjoint (a * a - a) := by
    simpa only [sq] using (ha.pow 2).sub ha
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow]
  have hleft : ‖τ.toPreGNS (p - a)‖ ^ 2 = (τ ((p - a) ^ 2)).re := by
    simp only [norm_sq_eq_re_inner (𝕜 := ℂ), PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS, hpa.star_eq, sq]
    rfl
  have hright : ‖τ.toPreGNS (a * a - a)‖ ^ 2 = (τ ((a * a - a) ^ 2)).re := by
    simp only [norm_sq_eq_re_inner (𝕜 := ℂ), PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS, hdef.star_eq, sq]
    rfl
  rw [hleft, hright]
  have hmap : τ (4 * (a * a - a) ^ 2) = 4 * τ ((a * a - a) ^ 2) := by
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using map_nsmul τ 4 ((a * a - a) ^ 2)
  change τ ((p - a) ^ 2) ≤ τ (4 * (a * a - a) ^ 2) at hτ
  rw [hmap] at hτ
  convert hτ.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

theorem isStarProjection_subtype_of_coe {R S : Type*} [Mul R] [Star R]
    [SetLike S R] [MulMemClass S R] [StarMemClass S R] {s : S}
    (x : s) (hp : IsStarProjection (x : R)) : IsStarProjection x := by
  constructor
  · exact Subtype.ext hp.isIdempotentElem.eq
  · exact Subtype.ext hp.isSelfAdjoint.star_eq

section VonNeumann
variable (P : VonNeumannAlgebra H)

theorem halfSpectralProjectionElement_isStarProjection (a : P.toStarSubalgebra) :
    IsStarProjection (halfSpectralProjectionElement P a) := by
  have he : (halfSpectralProjectionElement P a : H →L[ℂ] H) =
      halfSpectralProjection (a : H →L[ℂ] H) := rfl
  apply isStarProjection_subtype_of_coe
  rw [he]
  exact halfSpectralProjection_isStarProjection (H := H) (a : H →L[ℂ] H)

theorem halfSpectralProjectionElement_square_le (a : P.toStarSubalgebra)
    (ha : IsSelfAdjoint a) :
    (halfSpectralProjectionElement P a - a) ^ 2 ≤ 4 * (a * a - a) ^ 2 := by
  change (halfSpectralProjection (a : H →L[ℂ] H) - a) ^ 2 ≤ 4 * (a * a - a) ^ 2
  exact halfSpectralProjection_square_le (H := H) (a : H →L[ℂ] H)
    (show IsSelfAdjoint (a : H →L[ℂ] H) from congrArg Subtype.val ha.star_eq)

attribute [local instance] OAI.KadisonSimilarity.roundingCStar
attribute [local instance] OAI.KadisonSimilarity.roundingOrder
attribute [local instance] OAI.KadisonSimilarity.roundingStarOrder
local instance roundingCFC_rdd2ea6_1 :
    NonUnitalContinuousFunctionalCalculus ℝ P.toStarSubalgebra IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
local instance roundingDecompose_rdd2ea6_1 : SelfAdjointDecompose P.toStarSubalgebra where
  exists_nonneg_sub_nonneg {a} ha :=
    ⟨a⁺, a⁻, CFC.posPart_nonneg a, CFC.negPart_nonneg a, (CFC.posPart_sub_negPart a ha).symm⟩
variable (τ : P.toStarSubalgebra →ₚ[ℂ] ℂ)

attribute [local instance] OAI.KadisonSimilarity.roundingPreGNSNorm
theorem halfSpectralProjectionElement_norm_le (a : P.toStarSubalgebra)
    (ha : IsSelfAdjoint a) :
    ‖τ.toPreGNS (halfSpectralProjectionElement P a - a)‖ ≤
      2 * ‖τ.toPreGNS (a * a - a)‖ :=
  preGNS_rounding_norm_le τ a (halfSpectralProjectionElement P a) ha
    (halfSpectralProjectionElement_isStarProjection P a).isSelfAdjoint
    (halfSpectralProjectionElement_square_le P a ha)

/-- The tracial-ultrapower rounding input follows from the concrete spectral
projection. In fact positivity of the functional is enough for this step. -/
theorem spectralProjectionRoundingInput :
    @SpectralProjectionRoundingInput P.toStarSubalgebra (roundingCStar P)
      (roundingOrder P) (roundingStarOrder P) τ :=
  fun a ha => ⟨halfSpectralProjectionElement P a,
    halfSpectralProjectionElement_isStarProjection P a,
    halfSpectralProjectionElement_norm_le P τ a ha⟩

end VonNeumann

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialInputTransport
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transport of the discharged tracial inputs

These are coordinate changes through actual star algebra equivalences.
The concrete normal representation is retained as algebraic data; neither
rounding nor existence of a right support is assumed in the concrete model.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

section Equivalence
variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Rounding is invariant under a trace-preserving star equivalence. -/
theorem spectralProjectionRoundingInput_of_equiv
    (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ) (e : A ≃⋆ₐ[ℂ] B)
    (hτ : ∀ a, τB (e a) = τA a) (rounding : SpectralProjectionRoundingInput τB) :
    SpectralProjectionRoundingInput τA := by
  intro a ha
  obtain ⟨p, hp, hbound⟩ := rounding (e a) (ha.map e)
  refine ⟨e.symm p, hp.map e.symm, ?_⟩
  calc
    ‖τA.toPreGNS (e.symm p - a)‖ = ‖τB.toPreGNS (e (e.symm p - a))‖ :=
      (preGNS_norm_map_eq τA τB e.toStarAlgHom hτ _).symm
    _ = ‖τB.toPreGNS (p - e a)‖ := by rw [map_sub, e.apply_symm_apply]
    _ ≤ 2 * ‖τB.toPreGNS (e a * e a - e a)‖ := hbound
    _ = 2 * ‖τA.toPreGNS (a * a - a)‖ := by
      rw [← map_mul e, ← map_sub e]
      exact congrArg (fun t : ℝ => 2 * t)
        (preGNS_norm_map_eq τA τB e.toStarAlgHom hτ (a * a - a))

end Equivalence

section Concrete
variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : VonNeumannAlgebra H)

local instance transportModel_closed : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed P.carrier
  rw [← P.centralizer_centralizer']
  exact Set.isClosed_centralizer _

/-- The concrete spectral theorem discharges rounding after an actual
faithful normal realization of the abstract algebra. -/
theorem spectralProjectionRoundingInput_of_concrete_equiv
    (τ : A →ₚ[ℂ] ℂ) (e : A ≃⋆ₐ[ℂ] P.toStarSubalgebra) :
    SpectralProjectionRoundingInput τ :=
  spectralProjectionRoundingInput_of_equiv τ (transportedPositiveTrace τ e) e
    (transportedPositiveTrace_map τ e)
    (spectralProjectionRoundingInput P (transportedPositiveTrace τ e))

/-- A faithful representation whose range is the stated von Neumann
algebra supplies all the coordinates needed for spectral rounding. -/
theorem spectralProjectionRoundingInput_of_concrete_range
    (τ : A →ₚ[ℂ] ℂ) (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hinj : Function.Injective ρ) (hrange : ρ.range = P.toStarSubalgebra) :
    SpectralProjectionRoundingInput τ :=
  spectralProjectionRoundingInput_of_concrete_equiv P τ
    (equivalenceOfConcreteRange P ρ hinj hrange)

end Concrete
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixTracialGNS
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.normalizedMatrixTrace_diagonal _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized matrix traces and their actual GNS Hilbert spaces. The GNS
space of `M_n(A)` is identified with the square array of copies of the GNS
space of `A`; its algebra vectors have entries `n^(-1/2) V(a_ij)`. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {n : ℕ} [NeZero n]

/-- The normalized trace of one diagonal entry has weight `1/n`. -/
theorem normalizedMatrixTrace_single (τ : A →ₚ[ℂ] ℂ) (i : Fin n) (a : A) :
    normalizedMatrixTrace τ n (CStarMatrix.ofMatrix (Matrix.single i i a)) =
      τ a / (n : ℂ) := by
  simp [normalizedMatrixTrace_apply, Matrix.single_apply, apply_ite]

theorem normalizedMatrixTrace_matrixUnit (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (i : Fin n) :
    normalizedMatrixTrace τ n (CStarMatrix.ofMatrix (Matrix.single i i (1 : A))) =
      (n : ℂ)⁻¹ := by
  rw [normalizedMatrixTrace_single, h1, one_div]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixSmallCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.BoundedHochschild.WeakSubspace.preannihilator_closed_instance _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCStarQuotient.starSubalgebra_closed _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.corner_closed _root_.OAI.HochschildMatrixSystems.MatrixSystem.commutant_closed _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerClosed _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.algebra_closed _root_.OAI.PopaCorner.instNormedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.hilbertArrayFlatten_apply _root_.OAI.KadisonSimilarity.hilbertFourfoldFlatten_apply _root_.OAI.KadisonSimilarity.hilbertTripleFlatten_apply _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.KadisonSimilarity.vonNeumannInnerDerivation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished scalar matrix corner has the original algebra's
commutator estimate on a finite standard multiplicity. The proof uses
actual coordinate insertion/projection and then transports the estimate
to the normalized matrix GNS space. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A diagonal coordinate placement is contractive. -/
theorem norm_coordinateCornerOperator_le {n : ℕ} (i : Fin n) (T : H →L[ℂ] H) :
    ‖coordinateCornerOperator i T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro ξ
  rw [coordinateCornerOperator_apply, PiLp.norm_single]
  exact (T.le_opNorm (ξ i)).trans
    (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le ξ i) (norm_nonneg T))

/-- A diagonal amplification preserves each coordinate corner. -/
theorem commutator_coordinateCornerOperator {n : ℕ} (i : Fin n)
    (Y T : H →L[ℂ] H) :
    commutator (amplify Y n) (coordinateCornerOperator i T) =
      coordinateCornerOperator i (commutator Y T) := by
  ext ξ j
  by_cases h : j = i
  · subst j
    simp [commutator, coordinateCornerOperator_apply, amplify_apply]
  · simp [commutator, coordinateCornerOperator_apply, amplify_apply, h]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {n : ℕ} [NeZero n]

omit [PartialOrder A] [StarOrderedRing A] [NeZero n] in
theorem matrixCornerProjection_sandwich (i : Fin n)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    matrixCornerProjection i * X * matrixCornerProjection i =
      CStarMatrix.ofMatrix (Matrix.single i i (X i i)) := by
  apply CStarMatrix.ofMatrix.symm.injective
  change Matrix.single i i (1 : A) * CStarMatrix.ofMatrix.symm X * Matrix.single i i 1 =
    Matrix.single i i (X i i)
  simpa only [one_mul, mul_one, CStarMatrix.ofMatrix_symm_apply] using
    (Matrix.single_mul_mul_single i i i i (1 : A) (CStarMatrix.ofMatrix.symm X) 1)

omit [NeZero n] in
/-- There is only one possibly nonzero entry in the distinguished corner. -/
theorem matrixCorner_eq_single (i : Fin n)
    (X : CStarCorner (matrixCornerProjection (A := A) i)
      (matrixCornerProjection_isStarProjection i)) :
    (X : CStarMatrix (Fin n) (Fin n) A) = CStarMatrix.ofMatrix (Matrix.single i i (X.val i i)) := by
  have hs := matrixCornerProjection_sandwich (A := A) i
    (X : CStarMatrix (Fin n) (Fin n) A)
  rw [X.property.1, X.property.2] at hs
  exact hs

omit [NeZero n] in
theorem matrixLeftArray_single (τ : A →ₚ[ℂ] ℂ) (i : Fin n) (a : A) :
    matrixLeftArray τ (CStarMatrix.ofMatrix (Matrix.single i i a)) =
      coordinateCornerOperator i (amplify (τ.gnsStarAlgHom a) n) := by
  ext ξ j k
  by_cases h : j = i
  · subst j
    simp [matrixLeftArray_apply, Matrix.single_apply, apply_ite, ite_apply, amplify_apply,
      coordinateCornerOperator_apply]
  · simp [matrixLeftArray_apply, coordinateCornerOperator_apply, h, Ne.symm h]

omit [NeZero n] in
/-- The concrete distinguished corner estimate on ordinary Hilbert arrays. -/
theorem matrix_array_small_corner_bound (τ : A →ₚ[ℂ] ℂ) (i : Fin n)
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ a : A, ‖commutator Y (amplify (τ.gnsStarAlgHom a) n)‖ ≤ ε * ‖a‖)
    (X : CStarCorner (matrixCornerProjection (A := A) i)
      (matrixCornerProjection_isStarProjection i)) :
    ‖commutator (amplify Y n) (matrixLeftArray τ (X : CStarMatrix (Fin n) (Fin n) A))‖ ≤
      ε * ‖X‖ := by
  rw [matrixCorner_eq_single i X, matrixLeftArray_single, commutator_coordinateCornerOperator]
  calc
    _ ≤ ‖commutator Y (amplify (τ.gnsStarAlgHom (X.val i i)) n)‖ :=
      norm_coordinateCornerOperator_le i _
    _ ≤ ε * ‖X.val i i‖ := hbound _
    _ ≤ ε * ‖X‖ := mul_le_mul_of_nonneg_left
      (CStarMatrix.norm_entry_le_norm (M := X.val)) hε

theorem matrixGNSLiftOperator_apply (τ : A →ₚ[ℂ] ℂ)
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n)
    (ξ : (normalizedMatrixTrace τ n).GNS) :
    matrixGNSUnitary τ n (matrixGNSLiftOperator τ Y ξ) =
      amplify Y n (matrixGNSUnitary τ n ξ) := by
  simp only [matrixGNSLiftOperator, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.apply_symm_apply]

/-- The transported commutator has precisely the array action. -/
theorem matrixGNSLiftOperator_commutator (τ : A →ₚ[ℂ] ℂ)
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n)
    (X : CStarMatrix (Fin n) (Fin n) A) (ξ : (normalizedMatrixTrace τ n).GNS) :
    matrixGNSUnitary τ n
      (commutator (matrixGNSLiftOperator τ Y) ((normalizedMatrixTrace τ n).gnsStarAlgHom X) ξ) =
    commutator (amplify Y n) (matrixLeftArray τ X) (matrixGNSUnitary τ n ξ) := by
  simp only [commutator, sub_apply, mul_apply_eq_comp,
    map_sub, matrixGNSLiftOperator_apply, matrixGNSUnitary_left]

/-- The distinguished-corner estimate on the actual normalized matrix GNS space. -/
theorem matrix_gns_small_corner_bound (τ : A →ₚ[ℂ] ℂ) (i : Fin n)
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ a : A, ‖commutator Y (amplify (τ.gnsStarAlgHom a) n)‖ ≤ ε * ‖a‖)
    (X : CStarCorner (matrixCornerProjection (A := A) i)
      (matrixCornerProjection_isStarProjection i)) :
    ‖commutator (matrixGNSLiftOperator τ Y)
      ((normalizedMatrixTrace τ n).gnsStarAlgHom (X : CStarMatrix (Fin n) (Fin n) A))‖ ≤
      ε * ‖X‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hε (norm_nonneg X))
  intro ξ
  calc
    _ = ‖matrixGNSUnitary τ n
        (commutator (matrixGNSLiftOperator τ Y)
          ((normalizedMatrixTrace τ n).gnsStarAlgHom (X : CStarMatrix (Fin n) (Fin n) A)) ξ)‖ :=
      ((matrixGNSUnitary τ n).norm_map _).symm
    _ = ‖commutator (amplify Y n) (matrixLeftArray τ X) (matrixGNSUnitary τ n ξ)‖ :=
      congrArg norm (matrixGNSLiftOperator_commutator τ Y X ξ)
    _ ≤ ‖commutator (amplify Y n) (matrixLeftArray τ X)‖ * ‖matrixGNSUnitary τ n ξ‖ :=
      (commutator (amplify Y n) (matrixLeftArray τ X)).le_opNorm _
    _ ≤ (ε * ‖X‖) * ‖ξ‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (matrix_array_small_corner_bound τ i Y hε hbound X)
        (norm_nonneg ξ)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixSubfactorTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.CStarCorner.mem_subalgebra _root_.OAI.KadisonSimilarity.CStarCorner.normalizedTrace_apply _root_.OAI.KadisonSimilarity.DihedralSpectralArc.corner_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.cornerStarAlgHom_coe _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.haarCornerLetter_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_mul _root_.OAI.KadisonSimilarity.haarCornerPower_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_zero _root_.OAI.KadisonSimilarity.hilbertArrayFlatten_apply _root_.OAI.KadisonSimilarity.hilbertFourfoldFlatten_apply _root_.OAI.KadisonSimilarity.hilbertTripleFlatten_apply _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.matrixEntryHom_single _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.mul_haarCornerPower _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.normalizedMatrixTrace_diagonal _root_.OAI.KadisonSimilarity.star_haarCornerLetter _root_.OAI.KadisonSimilarity.star_haarCornerPower _root_.OAI.KadisonSimilarity.support_mul_haarCornerLetter _root_.OAI.KadisonSimilarity.vonNeumannInnerDerivation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The matrix amplification of an included subfactor acts entrywise.
Commutation with the original subfactor therefore gives commutation with
the full matrix subfactor on the square array of standard copies. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  (φ : A →⋆ₐ[ℂ] B) {n : ℕ}

/-- The common scalar matrix units belong to the included matrix subfactor. -/
theorem matrixEntryHom_cornerProjection (i : Fin n) :
    matrixEntryHom φ (matrixCornerProjection (A := A) i) =
      matrixCornerProjection (A := B) i := by
  ext j k
  simp only [matrixEntryHom_apply, matrixCornerProjection, CStarMatrix.ofMatrix_apply,
    Matrix.single_apply]
  split_ifs <;> simp only [map_one, map_zero]

variable [PartialOrder B] [StarOrderedRing B] [NeZero n]
  (τ : B →ₚ[ℂ] ℂ)

omit [NeZero n] in
/-- The array action can be read as a finite sum of operators on whole rows. -/
theorem matrixLeftArray_row (X : CStarMatrix (Fin n) (Fin n) B)
    (ξ : MatrixGNSArray τ n) (i : Fin n) :
    matrixLeftArray τ X ξ i = ∑ k, amplify (τ.gnsStarAlgHom (X i k)) n (ξ k) := by
  ext j
  simp only [matrixLeftArray_apply, WithLp.ofLp_sum, Finset.sum_apply, amplify_apply]

omit [NeZero n] in
/-- Entrywise commutation gives the full matrix-subfactor commutation. -/
theorem matrix_array_commutes_subfactor
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n)
    (hY : ∀ a : A, Y.comp (amplify (τ.gnsStarAlgHom (φ a)) n) =
      (amplify (τ.gnsStarAlgHom (φ a)) n).comp Y)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    (amplify Y n).comp (matrixLeftArray τ (matrixEntryHom φ X)) =
      (matrixLeftArray τ (matrixEntryHom φ X)).comp (amplify Y n) := by
  ext ξ i j
  change (Y (matrixLeftArray τ (matrixEntryHom φ X) ξ i)) j = _
  rw [matrixLeftArray_row, map_sum]
  change (∑ k, Y (amplify (τ.gnsStarAlgHom (φ (X i k))) n (ξ k))) j = _
  have he (k : Fin n) :
      Y (amplify (τ.gnsStarAlgHom (φ (X i k))) n (ξ k)) =
        amplify (τ.gnsStarAlgHom (φ (X i k))) n (Y (ξ k)) :=
    congrArg (fun T : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n => T (ξ k))
      (hY (X i k))
  simp_rw [he]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, amplify_apply, ContinuousLinearMap.comp_apply,
    matrixLeftArray_apply, matrixEntryHom_apply]

/-- The same commutation holds on the actual normalized matrix GNS space. -/
theorem matrix_gns_commutes_subfactor
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n)
    (hY : ∀ a : A, Y.comp (amplify (τ.gnsStarAlgHom (φ a)) n) =
      (amplify (τ.gnsStarAlgHom (φ a)) n).comp Y)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    (matrixGNSLiftOperator τ Y).comp
      ((normalizedMatrixTrace τ n).gnsStarAlgHom (matrixEntryHom φ X)) =
    ((normalizedMatrixTrace τ n).gnsStarAlgHom (matrixEntryHom φ X)).comp
      (matrixGNSLiftOperator τ Y) := by
  ext ξ
  apply (matrixGNSUnitary τ n).injective
  simp only [ContinuousLinearMap.comp_apply, matrixGNSLiftOperator_apply,
    matrixGNSUnitary_left]
  exact congrArg (fun T : MatrixGNSArray τ n →L[ℂ] MatrixGNSArray τ n =>
    T (matrixGNSUnitary τ n ξ)) (matrix_array_commutes_subfactor φ τ Y hY X)

/-- Projection comparison in the matrix subfactor extends the one-row
estimate to every projection of trace at most one over the matrix size. -/
theorem matrix_gns_all_small_corners
    [PartialOrder A] [StarOrderedRing A]
    (τA : A →ₚ[ℂ] ℂ) (hA : τA 1 = 1)
    (comparison : FiniteFactorProjectionComparison
      (fun X : CStarMatrix (Fin n) (Fin n) A => (normalizedMatrixTrace τA n X).re))
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n)
    (hY : ∀ a : A, Y.comp (amplify (τ.gnsStarAlgHom (φ a)) n) =
      (amplify (τ.gnsStarAlgHom (φ a)) n).comp Y)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ b : B, ‖commutator Y (amplify (τ.gnsStarAlgHom b) n)‖ ≤ ε * ‖b‖)
    (f : CStarMatrix (Fin n) (Fin n) A) (hf : IsStarProjection f)
    (ht : (normalizedMatrixTrace τA n f).re ≤ (n : ℝ)⁻¹) :
    ∀ z : CStarCorner (matrixEntryHom φ f) (hf.map (matrixEntryHom φ)),
      ‖commutator (matrixGNSLiftOperator τ Y)
        ((normalizedMatrixTrace τ n).gnsStarAlgHom (z : CStarMatrix (Fin n) (Fin n) B))‖ ≤
        ε * ‖z‖ := by
  let i : Fin n := 0
  have hetrace : (normalizedMatrixTrace τA n (matrixCornerProjection (A := A) i)).re =
      (n : ℝ)⁻¹ := by
    change (normalizedMatrixTrace τA n (CStarMatrix.ofMatrix (Matrix.single i i 1))).re = _
    rw [normalizedMatrixTrace_matrixUnit τA hA i]
    simp
  apply corner_commutator_bound_of_hom_comparison (matrixEntryHom φ)
    (normalizedMatrixTrace τ n).gnsStarAlgHom
    (fun X => (normalizedMatrixTrace τA n X).re) comparison
    (matrixCornerProjection i) f (matrixCornerProjection_isStarProjection i) hf
    (by rwa [hetrace]) (matrixGNSLiftOperator τ Y)
    (fun X => matrix_gns_commutes_subfactor φ τ Y hY X) hε
  intro z
  have he := matrixEntryHom_cornerProjection φ i
  let z' : CStarCorner (matrixCornerProjection (A := B) i)
      (matrixCornerProjection_isStarProjection i) :=
    ⟨z, ⟨by simpa only [← he] using z.property.1,
      by simpa only [← he] using z.property.2⟩⟩
  exact matrix_gns_small_corner_bound τ i Y hε hbound z'

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_RestrictedNormality
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical GNS model of a bounded L²-generated algebra is normal.
The proof uses the actual inclusion of its trace vectors in the ambient
GNS space. -/

noncomputable section
namespace KadisonSimilarity
open TracialCornerGeometry
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (htr : ∀ a b : A, τ (a * b) = τ (b * a))

theorem restricted_generated_trace_balls_closed
    (hc : ∀ C : ℝ, IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : A) C))
    (S : StarSubalgebra ℂ A) (C : ℝ) :
    let L := (gnsTracialGeometry τ htr).l2GeneratedAlgebra S
    IsClosed (gnsTracialVector (restrictedPositiveTrace τ L) '' Metric.closedBall (0 : L) C) := by
  let G := gnsTracialGeometry τ htr
  let L := G.l2GeneratedAlgebra S
  let J := restrictedTracialGNSInclusion τ L
  change IsClosed (gnsTracialVector (restrictedPositiveTrace τ L) '' Metric.closedBall (0 : L) C)
  have heq : gnsTracialVector (restrictedPositiveTrace τ L) '' Metric.closedBall (0 : L) C =
      J ⁻¹' (gnsTracialVector τ '' Metric.closedBall (0 : A) C) := by
    ext ξ
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(a : A), ha, (restrictedTracialGNSInclusion_vector τ L a).symm⟩
    · rintro ⟨a, ha, hξ⟩
      have hJξ : J ξ ∈ G.baseSpace L := by
        change J ξ ∈ ((gnsTracialGeometry τ htr).baseSpace L : Set τ.GNS)
        rw [← restrictedTracialGNSInclusion_range τ L htr]
        exact ⟨ξ, rfl⟩
      have hmem : a ∈ L := by
        change G.vector a ∈ G.baseSpace S.topologicalClosure
        change G.vector a = J ξ at hξ
        rw [hξ, G.baseSpace_topologicalClosure]
        exact (le_of_eq (G.baseSpace_l2GeneratedAlgebra S)) hJξ
      refine ⟨⟨a, hmem⟩, ha, ?_⟩
      apply J.injective
      exact (restrictedTracialGNSInclusion_vector τ L ⟨a, hmem⟩).trans hξ
  rw [heq]
  exact (hc C).preimage J.continuous

theorem restricted_generated_normal_range
    (hc : ∀ C : ℝ, IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : A) C))
    (S : StarSubalgebra ℂ A) :
    let L := (gnsTracialGeometry τ htr).l2GeneratedAlgebra S
    (restrictedPositiveTrace τ L).gnsStarAlgHom.range =
      (representationVonNeumannAlgebra (restrictedPositiveTrace τ L).gnsStarAlgHom).toStarSubalgebra := by
  dsimp only
  exact (gnsTracialGeometry _ (restrictedPositiveTrace_tracial τ _ htr)).normal_range_of_closed_trace_balls
    (restricted_generated_trace_balls_closed τ htr hc S)

variable {B R : Type*} [CStarAlgebra B] [CStarAlgebra R]

theorem canonicalGenerated_normal_range
    (hc : ∀ C : ℝ, IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : A) C))
    (φ : B →⋆ₐ[ℂ] A) (ψ : R →⋆ₐ[ℂ] A) :
    (canonicalGeneratedGeometry τ htr φ ψ).left.range =
      (representationVonNeumannAlgebra (canonicalGeneratedGeometry τ htr φ ψ).left).toStarSubalgebra :=
  restricted_generated_normal_range τ htr hc (factorAlgebra φ.range ψ.range)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_PopaConjugatePosition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conjugacy form of Popa's free-position construction: a unitary in
an irreducibly included subfactor's tracial ultrapower conjugates a prescribed
constant subfactor to a copy free from the ambient constant algebra.
The conjugating unitary remains in the prescribed subfactor ultrapower, and
trace preservation transports the matrix presentation to its conjugated copy.
-/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder

variable {A B R : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra R]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b : A, τA (a * b) = τA (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

/-- Its range lies inside the included A-ultrapower, as required by the
coordinate small-corner transfer. -/
theorem conjugatedConstantEmbedding_range_le (ρ : R →⋆ₐ[ℂ] A)
    (u : unitary (Ultrapower τA hA ω trA)) :
    (conjugatedConstantEmbedding τA τB hA hB ω trA trB φ hφ ρ u).range ≤
      (tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ).range := by
  rintro x ⟨y, rfl⟩
  exact ⟨_, rfl⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_UltrapowerTraceBalls
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.generatedGNSInclusion_vector _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.KadisonSimilarity.tracialUltrapowerMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal bounded representatives in the tracial ultrapower. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower TracialUltrapower Filter
open scoped Topology BoundedContinuousFunction ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
  (htr : ∀ a b : A, τ (a * b) = τ (b * a))

private theorem trace_sequence_norm_tendsto (z : ℕ →ᵇ A) :
    Tendsto (fun i => ‖τ.toPreGNS (z i)‖) (ω : Filter ℕ)
      (𝓝 ‖gnsTracialVector (quotientTrace τ h1 ω htr) (quotientHom τ h1 ω htr z)‖) := by
  rw [gnsTracialVector_apply, UniformSpace.Completion.norm_coe, quotientTrace_preGNS_norm]
  change Tendsto (fun i => ‖τ.toPreGNS (z i)‖) (ω : Filter ℕ)
    (𝓝 (sequenceTwoNorm (traceHilbertMap τ h1) ω z))
  simpa only [traceHilbertMap_apply] using
    tendsto_sequenceTwoNorm (traceHilbertMap τ h1) ω z

/-- A rapidly converging sequence of uniformly bounded representatives has
one bounded diagonal representative for its Hilbert-space limit. -/
theorem exists_bounded_diagonal_trace_limit
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (x : ℕ → (ℕ →ᵇ A)) (C : ℝ) (hC : 0 ≤ C) (hx : ∀ n, ‖x n‖ ≤ C)
    (ξ : (quotientTrace τ h1 ω htr).GNS)
    (hξ : ∀ n, dist (gnsTracialVector (quotientTrace τ h1 ω htr)
      (quotientHom τ h1 ω htr (x n))) ξ ≤ (1 / 2 : ℝ) ^ n) :
    ∃ y : ℕ →ᵇ A, ‖y‖ ≤ C ∧
      gnsTracialVector (quotientTrace τ h1 ω htr) (quotientHom τ h1 ω htr y) = ξ := by
  classical
  let V := gnsTracialVector (quotientTrace τ h1 ω htr)
  let q := quotientHom τ h1 ω htr
  let r : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  have hr (n : ℕ) : 0 < r n := pow_pos (by norm_num) _
  let P : ℕ → ℕ → Prop := fun i n => ∀ j ≤ n,
    ‖τ.toPreGNS (x n i - x j i)‖ ≤ 3 * r j
  have hP (n : ℕ) : ∀ᶠ i in (ω : Filter ℕ), P i n := by
    have hb (j : ℕ) (hjn : j ≤ n) : ‖V (q (x n - x j))‖ < 3 * r j := by
      have hn : r n ≤ r j := pow_le_pow_of_le_one (by norm_num) (by norm_num) hjn
      calc
        ‖V (q (x n - x j))‖ = dist (V (q (x n))) (V (q (x j))) := by
          rw [dist_eq_norm, map_sub, map_sub]
        _ ≤ dist (V (q (x n))) ξ + dist ξ (V (q (x j))) := dist_triangle _ _ _
        _ ≤ r n + r j := add_le_add (hξ n) (by simpa only [dist_comm] using hξ j)
        _ < 3 * r j := by linarith [hr j]
    have hall : ∀ᶠ i in (ω : Filter ℕ), ∀ j ∈ Finset.range (n + 1),
        ‖τ.toPreGNS (x n i - x j i)‖ ≤ 3 * r j := by
      rw [eventually_all_finset]
      intro j hj
      have ht := (trace_sequence_norm_tendsto τ h1 ω htr (x n - x j)).eventually_lt_const
        (hb j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      exact ht.mono fun i hi => hi.le
    filter_upwards [hall] with i hi j hj
    exact hi j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hP0 (i : ℕ) : P i 0 := by
    intro j hj
    have : j = 0 := by omega
    subst j
    simp only [sub_self, map_zero, norm_zero]
    positivity
  let k : ℕ → ℕ := fun i => Nat.findGreatest (P i) i
  have hkP (i : ℕ) : P i (k i) := Nat.findGreatest_spec (Nat.zero_le i) (hP0 i)
  have hk (j : ℕ) : ∀ᶠ i in (ω : Filter ℕ), j ≤ k i := by
    have hji : ∀ᶠ i in (ω : Filter ℕ), j ≤ i :=
      (eventually_ge_atTop j).filter_mono (hω.trans_eq Nat.cofinite_eq_atTop)
    filter_upwards [hji, hP j] with i hji hi
    exact Nat.le_findGreatest hji hi
  let y : ℕ →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun i => x (k i) i) C (fun i => (x (k i)).norm_coe_le_norm i |>.trans (hx (k i)))
  have hy : ‖y‖ ≤ C := (BoundedContinuousFunction.norm_le hC).mpr
    (fun i => (x (k i)).norm_coe_le_norm i |>.trans (hx (k i)))
  refine ⟨y, hy, ?_⟩
  have hdist (j : ℕ) : dist (V (q y)) ξ ≤ 4 * r j := by
    have hj : ‖V (q (y - x j))‖ ≤ 3 * r j := by
      apply le_of_tendsto (trace_sequence_norm_tendsto τ h1 ω htr (y - x j))
      filter_upwards [hk j] with i hi
      exact hkP i j hi
    calc
      dist (V (q y)) ξ ≤ dist (V (q y)) (V (q (x j))) + dist (V (q (x j))) ξ :=
        dist_triangle _ _ _
      _ ≤ 3 * r j + r j := by
        apply add_le_add _ (hξ j)
        simpa only [dist_eq_norm, map_sub] using hj
      _ = 4 * r j := by ring
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  have ht : Tendsto (fun j => 4 * r j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul 4
  exact ge_of_tendsto ht (Eventually.of_forall hdist)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_UltrapowerNormality
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.generatedGNSInclusion_vector _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.KadisonSimilarity.tracialUltrapowerMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual tracial ultrapower has closed bounded trace-vector balls,
hence its faithful GNS representation is a von Neumann algebra. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower TracialUltrapower Filter
open scoped Topology BoundedContinuousFunction ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
  (htr : ∀ a b : A, τ (a * b) = τ (b * a))
  (hω : (ω : Filter ℕ) ≤ Filter.cofinite)

include hω in
theorem ultrapower_trace_balls_closed (C : ℝ) :
    IsClosed (gnsTracialVector (quotientTrace τ h1 ω htr) ''
      Metric.closedBall (0 : Ultrapower τ h1 ω htr) C) := by
  classical
  let V := gnsTracialVector (quotientTrace τ h1 ω htr)
  let q := quotientHom τ h1 ω htr
  apply IsSeqClosed.isClosed
  intro u ξ hu hlim
  choose X hX hXu using hu
  have hXC (n : ℕ) : ‖X n‖ ≤ C := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hX n
  have hC : 0 ≤ C := (norm_nonneg (X 0)).trans (hXC 0)
  have happrox (k : ℕ) : ∃ n, dist (u n) ξ ≤ (1 / 2 : ℝ) ^ k := by
    have hk : 0 < (1 / 2 : ℝ) ^ k := pow_pos (by norm_num) _
    obtain ⟨n, hn⟩ := (hlim.eventually (Metric.ball_mem_nhds ξ hk)).exists
    exact ⟨n, hn.le⟩
  choose n hn using happrox
  have hrep (ε : ℝ) (hε : 0 < ε) :
      ∃ a : Ultrapower τ h1 ω htr, ‖a‖ ≤ C + ε ∧ V a = ξ := by
    choose x hx hxn using fun k =>
      HochschildCStarQuotient.norm_mk_lt (ideal τ h1 ω htr) (X (n k)) hε
    have hxC (k : ℕ) : ‖x k‖ ≤ C + ε := (hxn k).le.trans (add_le_add (hXC _) le_rfl)
    have htrace (k : ℕ) : V (q (x k)) = u (n k) := by
      change V (Ideal.Quotient.mk (ideal τ h1 ω htr) (x k)) = _
      rw [hx k]
      exact hXu _
    obtain ⟨y, hy, hlimit⟩ := exists_bounded_diagonal_trace_limit τ h1 ω htr hω x
      (C + ε) (by positivity) hxC ξ (fun k => by rw [htrace]; exact hn k)
    exact ⟨q y, (NonUnitalStarAlgHom.norm_apply_le q y).trans hy, hlimit⟩
  obtain ⟨a, _, ha⟩ := hrep 1 zero_lt_one
  refine ⟨a, ?_, ha⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨b, hb, hbeq⟩ := hrep ε hε
  have hab : a = b := gnsTracialVector_injective (quotientTrace τ h1 ω htr)
    (quotientTrace_faithful τ h1 ω htr) (ha.trans hbeq.symm)
  simpa only [hab] using hb

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_CanonicalFreeCornerEstimate
attribute [-instance] _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original operator is recovered after applying the local free-corner
argument in the actual generated GNS model. All generation, faithfulness,
and compression requirements are proved here; the remaining local hypotheses
are the explicitly cited published structural inputs. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open TracialCornerGeometry
open scoped ComplexOrder

variable {A B R : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra R]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder R] [StarOrderedRing R]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ) (τR : R →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b : A, τA (a * b) = τA (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

local notation "τQ" => quotientTrace τB hB ω trB
local notation "trQ" => quotientTrace_tracial τB hB ω trB
local notation "ι" => constant τB hB ω trB

variable (ψ : R →⋆ₐ[ℂ] Ultrapower τB hB ω trB)
  (hψτ : ∀ r, quotientTrace τB hB ω trB (ψ r) = τR r)
  (hfB : ∀ a : B, τB (star a * a) = 0 → a = 0)
  (hψ : Function.Injective ψ)

local notation "G" => canonicalGeneratedGeometry τQ trQ ι ψ

variable {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR))

include hfB in
/-- The generated-factor comparison used by the local application is proved
from the normal source, rather than supplied independently. -/
theorem canonicalFreeCornerInput_of_normal_source
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hf : ScalarFree (quotientTrace τB hB ω trB).toLinearMap
      (constant τB hB ω trB).range ψ.range)
    (hsource : τR.gnsStarAlgHom.range =
      (representationVonNeumannAlgebra τR.gnsStarAlgHom).toStarSubalgebra)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    {b : ℝ} (Q : CanonicalSecondFrame τB hB ω trB ψ hψ b)
    (x : B) (hxsq : x * x = 1) :
    CanonicalFreeCornerInput τB τR hB ω trB ψ hψτ hψ M Q x hxsq := by
  change (G).LocalFreeCornerPublishedInputs
  exact canonicalFreeFactorComparison τQ trQ ι ψ
    (constant_injective τB hB ω trB hfB) hψ τR hψτ M
    (quotientTrace_one τB hB ω trB) (quotientTrace_faithful τB hB ω trB)
    hf hsource hsize ⟨_, canonicalGenerated_normal_range τQ trQ
      (ultrapower_trace_balls_closed τB hB ω trB hω) ι ψ⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixPopaPosition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed source factor is conjugated diagonally inside the prescribed
matrix-subfactor ultrapower. Trace and inclusion properties follow from the
concrete maps, with no operator-estimate hypothesis. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder

variable {R B : Type*} [CStarAlgebra R] [CStarAlgebra B]
  [PartialOrder R] [StarOrderedRing R] [PartialOrder B] [StarOrderedRing B]
  (τR : R →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hR : τR 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trR : ∀ a b : R, τR (a * b) = τR (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (ρ : R →⋆ₐ[ℂ] B) (hρτ : ∀ a, τB (ρ a) = τR a)
  (n : ℕ) [NeZero n]

local notation "τRn" => normalizedMatrixTrace τR n
local notation "τBn" => normalizedMatrixTrace τB n
local notation "hRn" => normalizedMatrixTrace_one τR hR
local notation "hBn" => normalizedMatrixTrace_one τB hB
local notation "trRn" => normalizedMatrixTrace_tracial τR trR
local notation "trBn" => normalizedMatrixTrace_tracial τB trB
local notation "ρn" => matrixEntryHom (n := n) ρ
local notation "hρn" => normalizedMatrixTrace_entryHom τR τB ρ hρτ

theorem matrixConjugatedEmbedding_range_le
    (u : unitary (Ultrapower τRn hRn ω trRn)) :
    (matrixConjugatedEmbedding τR τB hR hB ω trR trB ρ hρτ n u).range ≤
      (tracialUltrapowerMap τRn τBn hRn hBn ω trRn trBn ρn hρn).range :=
  conjugatedConstantEmbedding_range_le τRn τBn hRn hBn ω trRn trBn ρn hρn
    (matrixDiagonalHom n) u

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_MatrixFreeCornerApplication
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The free-corner estimate for an actual matrix GNS operator

The matrix subfactor is the entrywise image of the original inclusion.
Projection comparison transports the scalar bound to all sufficiently small
matrix corners. Popa's local conjugacy input chooses the free copy, while
all native GNS geometry is the canonical generated geometry. The remaining
local input consists exactly of the published structural data for that
geometry; it contains no commutator bound.
-/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder

variable {R B : Type*} [CStarAlgebra R] [CStarAlgebra B]
  [PartialOrder R] [StarOrderedRing R] [PartialOrder B] [StarOrderedRing B]
  (τR : R →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hR : τR 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trR : ∀ a b : R, τR (a * b) = τR (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (ρ : R →⋆ₐ[ℂ] B) (hρτ : ∀ a, τB (ρ a) = τR a)
  (hfR : ∀ a : R, τR (star a * a) = 0 → a = 0)
  (hfB : ∀ a : B, τB (star a * a) = 0 → a = 0)
  (n : ℕ) [NeZero n]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR))
  (Q : SmallFreeCornerData τR.toLinearMap (n : ℝ)⁻¹)

local notation "τRn" => normalizedMatrixTrace τR n
local notation "τBn" => normalizedMatrixTrace τB n
local notation "hRn" => normalizedMatrixTrace_one τR hR
local notation "hBn" => normalizedMatrixTrace_one τB hB
local notation "trRn" => normalizedMatrixTrace_tracial τR trR
local notation "trBn" => normalizedMatrixTrace_tracial τB trB
local notation "ρn" => matrixEntryHom (n := n) ρ
local notation "hρn" => normalizedMatrixTrace_entryHom τR τB ρ hρτ
local notation "ψ" => matrixConjugatedEmbedding τR τB hR hB ω trR trB ρ hρτ n
local notation "hψτ" => matrixConjugatedEmbedding_trace τR τB hR hB ω trR trB ρ hρτ n
local notation "hψ" => matrixConjugatedEmbedding_injective τR τB hR hB ω trR trB ρ hρτ n hfR

include hfB in
/-- Construct the actual matrix free-product comparison from the normal
source and its matrix tower. -/
theorem matrixFreeCornerLocalInput_of_normal_source
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hsource : τR.gnsStarAlgHom.range =
      (representationVonNeumannAlgebra τR.gnsStarAlgHom).toStarSubalgebra)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    (u : unitary (Ultrapower τRn hRn ω trRn))
    (hf : ScalarFree (quotientTrace τBn hBn ω trBn).toLinearMap
      (constant τBn hBn ω trBn).range (ψ u).range)
    (x : CStarMatrix (Fin n) (Fin n) B) (hxsq : x * x = 1) :
    MatrixFreeCornerLocalInput τR τB hR hB ω trR trB ρ hρτ hfR n M Q u x hxsq :=
  canonicalFreeCornerInput_of_normal_source τBn τR hBn ω trBn (ψ u) (hψτ u)
    (normalizedMatrixTrace_faithful τB hfB) (hψ u) M hω hf hsource hsize
    (canonicalGeneratedSmallFrame τBn τR hBn ω trBn (ψ u) (hψτ u) (hψ u) Q) x hxsq

include hfB in
/-- The matrix GNS centered-symmetry estimate, derived from projection
comparison, the free-position input and the structural local bundles. -/
theorem matrix_symmetry_bound_of_local_free_corner
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (popa : Popa1995ConjugateFreenessInput τRn τBn hRn hBn ω trRn trBn
      ρn hρn hω (matrixDiagonalHom n))
    (S : RealTracialSequence τR.toLinearMap)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    (comparison : FiniteFactorProjectionComparison
      (fun X : CStarMatrix (Fin n) (Fin n) R => (τRn X).re))
    (rounding : SpectralProjectionRoundingInput τRn)
    (source_normal : τB.gnsStarAlgHom.range =
      (representationVonNeumannAlgebra τB.gnsStarAlgHom).toStarSubalgebra)
    (published : ∀ (u : unitary (Ultrapower τRn hRn ω trRn)),
      ScalarFree (quotientTrace τBn hBn ω trBn).toLinearMap
        (constant τBn hBn ω trBn).range (ψ u).range →
      ∀ (x : CStarMatrix (Fin n) (Fin n) B), star x = x → ∀ hxsq : x * x = 1,
        MatrixFreeCornerLocalInput τR τB hR hB ω trR trB ρ hρτ hfR n M Q u x hxsq)
    (Y₀ : HilbertCopies τB.GNS n →L[ℂ] HilbertCopies τB.GNS n)
    (hcomm : ∀ a : R, Y₀.comp (amplify (τB.gnsStarAlgHom (ρ a)) n) =
      (amplify (τB.gnsStarAlgHom (ρ a)) n).comp Y₀)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hscalar : ∀ a : B, ‖commutator Y₀ (amplify (τB.gnsStarAlgHom a) n)‖ ≤ ε * ‖a‖)
    (x : CStarMatrix (Fin n) (Fin n) B)
    (hxstar : star x = x) (hxsq : x * x = 1) (hx0 : τBn x = 0) :
    ‖commutator (matrixGNSLiftOperator τB Y₀) ((τBn).gnsStarAlgHom x)‖ ≤
      cornerConstant * ε := by
  obtain ⟨u, hfree⟩ := popa
  have hD := matrixConjugatedEmbedding_range_le τR τB hR hB ω trR trB ρ hρτ n u
  have hcorner := matrix_gns_all_small_corners ρ τB τR hR comparison Y₀ hcomm hε hscalar
  exact original_symmetry_bound_of_free_corner τRn τBn τR hRn hBn ω trRn trBn
    ρn hρn (ψ u) (hψτ u) (normalizedMatrixTrace_faithful τB hfB) (hψ u) M
    hω hD hfree S hsize
    (canonicalGeneratedSmallFrame τBn τR hBn ω trBn (ψ u) (hψτ u) (hψ u) Q)
    x hxstar hxsq hx0
    (matrix_trace_balls_closed τB _ source_normal n hB trB hfB)
    (published u hfree x hxstar hxsq) rounding
    (matrixGNSLiftOperator τB Y₀)
    (fun a => matrix_gns_commutes_subfactor ρ τB Y₀ hcomm a)
    hε hcorner

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixTracialInputTransport
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral rounding for finite matrices in an actual normal representation. -/
noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder
variable {H A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Any faithful normal realization supplies all finite-matrix rounding
inputs, for every positive functional on the matrix algebra. -/
theorem matrix_spectralProjectionRoundingInput_of_concrete_range
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hσ : Function.Injective σ)
    (P : VonNeumannAlgebra H) (hrange : σ.range = P.toStarSubalgebra)
    (n : ℕ) [NeZero n] (τ : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ) :
    SpectralProjectionRoundingInput τ :=
  spectralProjectionRoundingInput_of_concrete_range (matrixVonNeumann P n) τ
    (representedMatrixHom σ n) (representedMatrixHom_injective σ hσ n)
    (representedMatrixHom_range σ P hrange n)


end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialStageCommutation
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Commutation with all matrix stages extends to the represented source
by density of trace vectors in the actual normal ambient algebra. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped CStarAlgebra ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem relativeOperatorCommutant_le (N : VonNeumannAlgebra H) (Z : H →L[ℂ] H) :
    relativeOperatorCommutant N Z ≤ N := by
  intro T hT
  change T ∈ StarSubalgebra.centralizer ℂ ((N.commutant : Set (H →L[ℂ] H)) ∪ {Z}) at hT
  rw [StarSubalgebra.mem_centralizer_iff] at hT
  rw [← N.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro S hS
  exact (hT S (Or.inl hS)).1

private theorem relativeOperatorCommutant_mem (N : VonNeumannAlgebra H)
    (Z T : H →L[ℂ] H) (hT : T ∈ N)
    (hZ : Z * T = T * Z) (hZstar : star Z * T = T * star Z) :
    T ∈ relativeOperatorCommutant N Z := by
  change T ∈ StarSubalgebra.centralizer ℂ ((N.commutant : Set (H →L[ℂ] H)) ∪ {Z})
  rw [StarSubalgebra.mem_centralizer_iff]
  intro S hS
  rcases hS with hS | hS
  · exact ⟨(VonNeumannAlgebra.mem_commutant_iff.mp hS T hT).symm,
      (VonNeumannAlgebra.mem_commutant_iff.mp (star_mem hS) T hT).symm⟩
  · obtain rfl := Set.mem_singleton_iff.mp hS
    exact ⟨hZ, hZstar⟩

private theorem relativeOperatorCommutant_commutes (N : VonNeumannAlgebra H)
    (Z T : H →L[ℂ] H) (hT : T ∈ relativeOperatorCommutant N Z) : Z * T = T * Z := by
  change T ∈ StarSubalgebra.centralizer ℂ ((N.commutant : Set (H →L[ℂ] H)) ∪ {Z}) at hT
  rw [StarSubalgebra.mem_centralizer_iff] at hT
  exact (hT Z (Or.inr (Set.mem_singleton Z))).1

section Source
variable {R B : Type*} [CStarAlgebra R] [CStarAlgebra B]
  [PartialOrder R] [StarOrderedRing R] [PartialOrder B] [StarOrderedRing B]
  (τR : R →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hB : τB 1 = 1) (trB : ∀ a b, τB (a * b) = τB (b * a))
  (hfB : ∀ a, τB (star a * a) = 0 → a = 0)
  (normalB : τB.gnsStarAlgHom.range =
    (representationVonNeumannAlgebra τB.gnsStarAlgHom).toStarSubalgebra)
  (ρ : R →⋆ₐ[ℂ] B) (hρ : ∀ a, τB (ρ a) = τR a)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR))

include hB trB hfB normalB hρ M in
/-- The original GNS action commutes with every operator commuting with the stages. -/
theorem commutes_source_of_matrix_stages (Z : τB.GNS →L[ℂ] τB.GNS)
    (hZ : ∀ j a, Z * τB.gnsStarAlgHom (ρ (M.embedding j a)) =
      τB.gnsStarAlgHom (ρ (M.embedding j a)) * Z) (r : R) :
    Z * τB.gnsStarAlgHom (ρ r) = τB.gnsStarAlgHom (ρ r) * Z := by
  let G := gnsTracialGeometry τB trB
  let NB := representationVonNeumannAlgebra τB.gnsStarAlgHom
  let υ := G.normalTracialRepresentation hB (gnsTracialVector_injective τB hfB) NB normalB
  let e := equivalenceOfConcreteRange NB G.left (G.left_injective (gnsTracialVector_injective τB hfB)) normalB
  let N := relativeOperatorCommutant NB Z
  let J := gnsTracialHomIsometry τR τB ρ hρ
  have hv (b : B) : Generator.Tracial.baseVector υ (e b) = gnsTracialVector τB b := by
    change G.left b (G.vector 1) = G.vector b
    rw [G.left_vector, mul_one]
  have hstage (j : ℕ) (a : Matrix (I j) (I j) ℂ) :
      gnsTracialVector τB (ρ (M.embedding j a)) ∈ subalgebraTraceVectors υ N := by
    refine ⟨e (ρ (M.embedding j a)), ?_, hv _⟩
    apply relativeOperatorCommutant_mem NB Z _ (mem_representationVonNeumannAlgebra _ _)
      (hZ j a)
    simpa only [map_star, star_mul, star_star] using (congrArg star (hZ j (star a))).symm
  have hr : J (gnsTracialVector τR r) ∈ closure (subalgebraTraceVectors υ N) := by
    change gnsTracialVector τR r ∈ J ⁻¹' closure (subalgebraTraceVectors υ N)
    apply closure_minimal (s := ⋃ j, Set.range (fun a => gnsTracialVector τR (M.embedding j a)))
      ?_ (isClosed_closure.preimage J.continuous) (M.dense (gnsTracialVector τR r))
    intro ξ hξ
    obtain ⟨j, a, rfl⟩ := Set.mem_iUnion.mp hξ
    change gnsTracialHomIsometry τR τB ρ hρ (gnsTracialVector τR (M.embedding j a)) ∈
      closure (subalgebraTraceVectors υ N)
    rw [gnsTracialHomIsometry_vector]
    exact subset_closure (hstage j a)
  have hrr : Generator.Tracial.baseVector υ (e (ρ r)) ∈ closure (subalgebraTraceVectors υ N) := by
    rw [hv]
    change gnsTracialHomIsometry τR τB ρ hρ (gnsTracialVector τR r) ∈ _ at hr
    rwa [gnsTracialHomIsometry_vector] at hr
  have hmem := mem_of_traceVector_mem_closure υ (relativeOperatorCommutant_le NB Z)
    (e (ρ r)) hrr
  exact relativeOperatorCommutant_commutes NB Z _ hmem

include hB trB hfB normalB hρ M in
/-- Coordinate compression extends stage commutation at every finite multiplicity. -/
theorem commutes_amplified_source_of_matrix_stages (n : ℕ)
    (Y : HilbertCopies τB.GNS n →L[ℂ] HilbertCopies τB.GNS n)
    (hY : ∀ j a, commutator Y (amplify (τB.gnsStarAlgHom (ρ (M.embedding j a))) n) = 0)
    (r : R) :
    Y.comp (amplify (τB.gnsStarAlgHom (ρ r)) n) =
      (amplify (τB.gnsStarAlgHom (ρ r)) n).comp Y := by
  change Y * amplify (τB.gnsStarAlgHom (ρ r)) n = amplify (τB.gnsStarAlgHom (ρ r)) n * Y
  symm
  apply (amplify_commutes_iff_entries (τB.gnsStarAlgHom (ρ r)) Y).mpr
  intro i j
  symm
  apply commutes_source_of_matrix_stages τR τB hB trB hfB normalB ρ hρ M
    (matrixEntryCompression i j Y) ?_ r
  intro k a
  have hc : Y * amplify (τB.gnsStarAlgHom (ρ (M.embedding k a))) n =
      amplify (τB.gnsStarAlgHom (ρ (M.embedding k a))) n * Y := sub_eq_zero.mp (hY k a)
  exact ((amplify_commutes_iff_entries (τB.gnsStarAlgHom (ρ (M.embedding k a))) Y).mp
    hc.symm i j).symm

end Source
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FiniteFactorApplication
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-factor application of the free-corner argument

The local hypotheses below specify the actual increasing-matrix inclusion,
its normal represented closure, and the published projection and free-product
inputs. The commutator estimates combine Haar averaging, the free-corner
theorem, and the exact
finite and countable amplification transfers.
-/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder Topology

variable {R B : Type*} [CStarAlgebra R] [CStarAlgebra B]
  [PartialOrder R] [StarOrderedRing R] [PartialOrder B] [StarOrderedRing B]
  (τR : R →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hR : τR 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trR : ∀ a b : R, τR (a * b) = τR (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (ρ : R →⋆ₐ[ℂ] B) (hρτ : ∀ a, τB (ρ a) = τR a)
  (hfR : ∀ a : R, τR (star a * a) = 0 → a = 0)
  (hfB : ∀ a : B, τB (star a * a) = 0 → a = 0)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR))

variable (hω : (ω : Filter ℕ) ≤ Filter.cofinite)

include hfR hfB M in
/-- The paper's finite-standard-multiplicity estimate. The centered test is
proved from the local free-corner theorem after extending stage commutation
by the actual trace-vector density. -/
theorem finite_standard_bound_of_local_free_corner_oai
    (inputs : FiniteFactorFreeCornerInputs τR τB hR hB ω trR trB ρ hρτ hω)
    (source_normalR : τR.gnsStarAlgHom.range =
      (representationVonNeumannAlgebra τR.gnsStarAlgHom).toStarSubalgebra)
    (source_normal : τB.gnsStarAlgHom.range =
      (representationVonNeumannAlgebra τB.gnsStarAlgHom).toStarSubalgebra)
    (S : RealTracialSequence τR.toLinearMap)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    {r : ℕ} (Y : HilbertCopies τB.GNS r →L[ℂ] HilbertCopies τB.GNS r)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : ∀ a, ‖commutator Y (amplify (τB.gnsStarAlgHom a) r)‖ ≤ δ * ‖a‖)
    (h : ℕ) (X : CStarMatrix (Fin h) (Fin h) B) :
    ‖commutator (amplify Y h)
      (representedMatrix (amplifiedScalarRepresentation τB.gnsStarAlgHom r) X)‖ ≤
      (3 * cornerConstant + 2) * δ * ‖X‖ := by
  apply finite_standard_estimate_of_centered_tests τB
    (fun j => ρ.comp (M.embedding j)) M.inclusion
    (fun j k h a => congrArg ρ (M.compatible j k h a))
    (le_of_lt cornerConstant_pos) _ Y hδ hscalar h X
  intro m _ Y₀ ε hε hscalar₀ hstage x hxstar hxsq hx0
  have hm : 0 < m := NeZero.pos m
  obtain ⟨Q⟩ := (gnsTracialGeometry τR trR).exists_smallFreeCornerData_of_normal_matrix_tower
    M hR (gnsTracialVector_injective τR hfR) _ source_normalR hsize
    (show 0 < ((4 * m : ℕ) : ℝ)⁻¹ by positivity)
  have hcomm (a : R) :
      Y₀.comp (amplify (τB.gnsStarAlgHom (ρ a)) (4 * m)) =
        (amplify (τB.gnsStarAlgHom (ρ a)) (4 * m)).comp Y₀ := by
    exact commutes_amplified_source_of_matrix_stages τR τB hB trB hfB source_normal
      ρ hρτ M (4 * m) Y₀ hstage a
  exact matrix_symmetry_bound_of_local_free_corner τR τB hR hB ω trR trB
    ρ hρτ hfR hfB (4 * m) M Q hω (inputs.free_position (4 * m)) S hsize
    (matrix_projectionComparison_of_tower τR hR trR hfR M source_normalR (4 * m))
    (matrix_spectralProjectionRoundingInput_of_concrete_range τR.gnsStarAlgHom
      ((gnsTracialGeometry τR trR).left_injective (gnsTracialVector_injective τR hfR))
      _ source_normalR (4 * m) _) source_normal
    (fun u hfree x _ hxsq =>
      matrixFreeCornerLocalInput_of_normal_source τR τB hR hB ω trR trB
        ρ hρτ hfR hfB (4 * m) M Q hω source_normalR hsize u hfree x hxsq) Y₀ hcomm (by positivity) hscalar₀ x hxstar hxsq hx0

end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonSimilarity.finite_standard_bound_of_local_free_corner_oai.{u_1, u_2, u_3} := @OAI.KadisonSimilarity.finite_standard_bound_of_local_free_corner_oai.{u_1, u_2, u_3}
