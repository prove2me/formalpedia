-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialRepeatedWordRealization.propagation_on_base_of_published_inputs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T14:42:15.167755+00:00
-- url     : https://prove2.me/submissions/73b5be73-304e-4a28-861f-b593f06f4ec1

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A018
import Definitions.Def_OAIQ075A029
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_factorization_of_complete_bound
import Theorems.Thm_OAI_KadisonSimilarity_dicksonTwoBound_proved

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_Derivations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The triangular representation of a bounded derivation

Similarity of the upper triangular representation gives an inner implementer
for a bounded derivation.
-/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The orthogonal projection onto a closed subspace invariant under a family
and its adjoints commutes with that family. -/
theorem orthogonal_projection_commutes (U : A → (H →L[ℂ] H))
    (hstar : ∀ a, U (star a) = star (U a)) (M : ClosedSubmodule ℂ H)
    (hM : ∀ a x, x ∈ M → U a x ∈ M) (a : A) :
    Commute M.toSubmodule.starProjection (U a) := by
  change M.toSubmodule.starProjection * U a = U a * M.toSubmodule.starProjection
  ext x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hM a _ (Submodule.starProjection_apply_mem _ _)
  · intro w hw
    simp only [mul_apply_eq_comp]
    have hadj : (U a).adjoint = U (star a) := (hstar a).symm
    have hzero : inner ℂ ((U a) (x - M.toSubmodule.starProjection x)) w = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hadj]
      exact M.toSubmodule.starProjection_inner_eq_zero x _ (hM (star a) w hw)
    simpa only [map_sub, ContinuousLinearMap.coe_coe] using hzero

universe u v

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_CompletelyBounded
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.hilbertArrayFlatten_apply _root_.OAI.KadisonSimilarity.hilbertFourfoldFlatten_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.hilbertTripleFlatten_apply _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_matrixOperator _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.matrixLeftArray_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_apply _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_zero _root_.OAI.KadisonSimilarity.representedDoubleMatrix_apply _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete matrix norms and complete boundedness

The matrix norm used here is `CStarMatrix`'s C-star norm. The representation
on finite Hilbert sums is shown to preserve that norm, connecting the concrete
commutator estimate with the usual notion of complete boundedness.
-/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every entry can be recovered by evaluating on a vector in one coordinate. -/
theorem operatorMatrixRepresentation_injective (n : ℕ) :
    Function.Injective (operatorMatrixRepresentation (H := H) n) := by
  intro X Y h
  apply Matrix.ext
  intro i j
  ext ξ
  have he := congrArg
    (fun T : HilbertCopies H n →L[ℂ] HilbertCopies H n => T (PiLp.single 2 j ξ) i) h
  simpa [operatorMatrixRepresentation, matrixOperator, PiLp.single_apply, apply_ite] using he

/-- The normed matrix action remains injective after the type synonym is changed. -/
theorem matrixRepresentation_injective (n : ℕ) :
    Function.Injective (matrixRepresentation (H := H) n) :=
  (operatorMatrixRepresentation_injective n).comp CStarMatrix.ofMatrixStarAlgEquiv.symm.injective

/-- The abstract C-star matrix norm equals the concrete Hilbert-space operator norm. -/
theorem norm_matrixOperator_eq (n : ℕ)
    (X : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    ‖matrixOperator (CStarMatrix.ofMatrix.symm X)‖ = ‖X‖ :=
  NonUnitalStarAlgHom.norm_map (matrixRepresentation n)
    (matrixRepresentation_injective n) X

section CompletelyBounded

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A star representation is completely contractive. -/
theorem completeBound_starHom (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : CompleteBound σ 1 := by
  intro n X
  let σₙ : CStarMatrix (Fin n) (Fin n) A →⋆ₙₐ[ℂ]
      CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H) :=
    CStarMatrix.mapₙₐ σ.toNonUnitalStarAlgHom
  have hn := NonUnitalStarAlgHom.norm_apply_le σₙ (CStarMatrix.ofMatrix X)
  rw [← norm_matrixOperator_eq n] at hn
  change ‖matrixOperator (X.map σ)‖ ≤ ‖CStarMatrix.ofMatrix X‖ at hn
  simpa only [one_mul] using hn

end CompletelyBounded

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_RectangularDerivations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedHomOrbit_apply _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.hilbertArrayFlatten_apply _root_.OAI.KadisonSimilarity.hilbertFourfoldFlatten_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.hilbertTripleFlatten_apply _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.listOrbitSum_append _root_.OAI.KadisonSimilarity.listOrbitSum_nil _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.matrixLeftArray_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.pairRepresentation_fst _root_.OAI.KadisonSimilarity.pairRepresentation_snd _root_.OAI.KadisonSimilarity.rectangularDiagonalStarHom_apply _root_.OAI.KadisonSimilarity.representedDoubleMatrix_apply _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.sharpHom_apply _root_.OAI.KadisonSimilarity.sharpVectorMap_apply _root_.OAI.KadisonSimilarity.similarityRepresentation_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rectangular derivations and the row/column estimate -/

noncomputable section
namespace KadisonSimilarity

variable {A F K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem rectangularMatrixOperator_smul {p q : ℕ} (c : ℂ)
    (X : Matrix (Fin p) (Fin q) (K →L[ℂ] F)) :
    rectangularMatrixOperator (c • X) = c • rectangularMatrixOperator X := by
  ext ξ i
  simp [rectangularMatrixOperator, Finset.smul_sum]

theorem norm_rectangularInr_le_one : ‖rectangularInr (F := F) (K := K)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖WithLp.toLp 2 (0, x)‖ ≤ 1 * ‖x‖
  simp [WithLp.norm_toLp_snd]

theorem norm_rectangularFst_le_one : ‖WithLp.fstL 2 ℂ F K‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using WithLp.norm_fst_le F x

/-- Matrix amplification respects compression to the upper-right corner. -/
theorem rectangularMatrixOperator_corner {p q : ℕ}
    (X : Matrix (Fin p) (Fin q)
      (RectangularSum F K →L[ℂ] RectangularSum F K)) :
    rectangularMatrixOperator (fun i j => (WithLp.fstL 2 ℂ F K).comp
      ((X i j).comp rectangularInr)) =
      (mapCopies (WithLp.fstL 2 ℂ F K) p).comp
        ((rectangularMatrixOperator X).comp (mapCopies rectangularInr q)) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply PiLp.ext
  intro i
  calc
    _ = ∑ j : Fin q, ((WithLp.fstL 2 ℂ F K).comp
        ((X i j).comp rectangularInr)) (ξ j) :=
      rectangularMatrixOperator_apply (F := F) (K := K) _ ξ i
    _ = (WithLp.fstL 2 ℂ F K)
        (∑ j : Fin q, X i j (rectangularInr (ξ j))) := by
      simp only [ContinuousLinearMap.comp_apply, map_sum]
    _ = _ := by
      change _ = (mapCopies (WithLp.fstL 2 ℂ F K) p
        (rectangularMatrixOperator X (mapCopies rectangularInr q ξ))) i
      rw [mapCopies_apply, rectangularMatrixOperator_apply]
      congr 1

private theorem norm_compression_le
    {E₁ E₂ E₃ E₄ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]
    [NormedAddCommGroup E₄] [NormedSpace ℂ E₄]
    (L : E₃ →L[ℂ] E₄) (T : E₂ →L[ℂ] E₃) (R : E₁ →L[ℂ] E₂)
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) : ‖L.comp (T.comp R)‖ ≤ ‖T‖ := by
  calc
    ‖L.comp (T.comp R)‖ ≤ ‖L‖ * (‖T‖ * ‖R‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖T‖ * ‖R‖) :=
      mul_le_mul_of_nonneg_right hL (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ 1 * (‖T‖ * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR (norm_nonneg _)) zero_le_one
    _ = ‖T‖ := by ring

/-- Compression to the upper-right corner of every entry does not increase
 the norm of a rectangular operator matrix. -/
theorem norm_rectangularCorner_le {p q : ℕ}
    (X : Matrix (Fin p) (Fin q)
      (RectangularSum F K →L[ℂ] RectangularSum F K)) :
    ‖rectangularMatrixOperator (fun i j => (WithLp.fstL 2 ℂ F K).comp
      ((X i j).comp rectangularInr))‖ ≤ ‖rectangularMatrixOperator X‖ := by
  have hleft : ‖mapCopies (WithLp.fstL 2 ℂ F K) p‖ ≤ 1 :=
    (norm_mapCopies_le _ _).trans (norm_rectangularFst_le_one (F := F) (K := K))
  have hright : ‖mapCopies (rectangularInr (F := F) (K := K)) q‖ ≤ 1 :=
    (norm_mapCopies_le _ _).trans (norm_rectangularInr_le_one (F := F) (K := K))
  calc
    _ = ‖(mapCopies (WithLp.fstL 2 ℂ F K) p).comp
        ((rectangularMatrixOperator X).comp (mapCopies rectangularInr q))‖ :=
      congrArg norm (rectangularMatrixOperator_corner X)
    _ ≤ ‖rectangularMatrixOperator X‖ :=
      norm_compression_le _ _ _ hleft hright

/-- Contractive diagonal blocks give a contractive diagonal operator. -/
theorem norm_rectangularDiagonal_le (ρ : F →L[ℂ] F) (σ : K →L[ℂ] K)
    {c : ℝ} (hc : 0 ≤ c) (hρ : ‖ρ‖ ≤ c) (hσ : ‖σ‖ ≤ c) :
    ‖rectangularTriangular ρ 0 σ‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg x))).mp
  simp only [WithLp.prod_norm_sq_eq_of_L2, rectangularTriangular_fst,
    rectangularTriangular_snd, zero_apply, add_zero]
  have h₁ := (ρ.le_opNorm x.fst).trans
    (mul_le_mul_of_nonneg_right hρ (norm_nonneg x.fst))
  have h₂ := (σ.le_opNorm x.snd).trans
    (mul_le_mul_of_nonneg_right hσ (norm_nonneg x.snd))
  have h₁' := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
  have h₂' := pow_le_pow_left₀ (norm_nonneg _) h₂ 2
  calc
    ‖ρ x.fst‖ ^ 2 + ‖σ x.snd‖ ^ 2 ≤
        (c * ‖x.fst‖) ^ 2 + (c * ‖x.snd‖) ^ 2 := add_le_add h₁' h₂'
    _ = c ^ 2 * (‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2) := by ring
    _ = (c * ‖x‖) ^ 2 := by rw [← WithLp.prod_norm_sq_eq_of_L2 x]; ring

/-- The off-diagonal corner has the same norm bound as its sole block. -/
theorem norm_rectangularOffDiagonal_le (δ : K →L[ℂ] F) :
    ‖rectangularTriangular 0 δ 0‖ ≤ ‖δ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg δ)
  intro x
  have heq : rectangularTriangular 0 δ 0 x = WithLp.toLp 2 (δ x.snd, 0) := by
    apply (WithLp.equiv 2 (F × K)).injective
    apply Prod.ext <;> simp
  rw [heq, WithLp.norm_toLp_fst]
  exact (δ.le_opNorm x.snd).trans
    (mul_le_mul_of_nonneg_left (WithLp.norm_snd_le F x) (norm_nonneg δ))

/-- The pointwise triangular estimate used before applying Dickson. -/
theorem norm_rectangularTriangular_le (ρ : F →L[ℂ] F) (δ : K →L[ℂ] F)
    (σ : K →L[ℂ] K) {c : ℝ} (hc : 0 ≤ c) (hρ : ‖ρ‖ ≤ c) (hσ : ‖σ‖ ≤ c) :
    ‖rectangularTriangular ρ δ σ‖ ≤ c + ‖δ‖ := by
  have hsplit : rectangularTriangular ρ δ σ =
      rectangularTriangular ρ 0 σ + rectangularTriangular 0 δ 0 := by
    ext x
    apply (WithLp.equiv 2 (F × K)).injective
    apply Prod.ext <;> simp
  rw [hsplit]
  exact (norm_add_le (rectangularTriangular ρ 0 σ) (rectangularTriangular 0 δ 0)).trans
    (add_le_add (norm_rectangularDiagonal_le ρ σ hc hρ hσ)
      (norm_rectangularOffDiagonal_le δ))

variable [CompleteSpace F] [CompleteSpace K]

open scoped CStarAlgebra

/-- The norm estimate which gives norm at most two after normalization. -/
theorem norm_rectangularRepresentation_apply (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b)) (a : A) :
    ‖(rectangularRepresentation ρ σ δ hδ).1 a‖ ≤ (1 + ‖δ‖) * ‖a‖ := by
  change ‖rectangularTriangular (ρ a) (δ a) (σ a)‖ ≤ (1 + ‖δ‖) * ‖a‖
  calc
    ‖rectangularTriangular (ρ a) (δ a) (σ a)‖ ≤ ‖a‖ + ‖δ a‖ :=
      norm_rectangularTriangular_le _ _ _ (norm_nonneg _)
        (NonUnitalStarAlgHom.norm_apply_le ρ a) (NonUnitalStarAlgHom.norm_apply_le σ a)
    _ ≤ ‖a‖ + ‖δ‖ * ‖a‖ := add_le_add (le_refl _) (δ.le_opNorm a)
    _ = (1 + ‖δ‖) * ‖a‖ := by ring

omit [CompleteSpace F] [CompleteSpace K] in
theorem norm_normalizedRectangularDerivation_le (δ : A →L[ℂ] (K →L[ℂ] F)) :
    ‖normalizedRectangularDerivation δ‖ ≤ 1 := by
  let : SeminormedAddCommGroup (A →L[ℂ] (K →L[ℂ] F)) := inferInstance
  let : NormedSpace ℂ (A →L[ℂ] (K →L[ℂ] F)) := inferInstance
  by_cases h : δ = 0
  · simp [h, normalizedRectangularDerivation]
  · have hn : ‖δ‖ ≠ 0 := (norm_ne_zero_iff (E := A →L[ℂ] (K →L[ℂ] F))).mpr h
    simp [normalizedRectangularDerivation, norm_smul, hn]

/-- The normalized triangular representation meets Dickson's norm-two hypothesis. -/
theorem norm_normalizedRectangularRepresentation_le_two
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b)) (a : A) :
    ‖(rectangularRepresentation ρ σ (normalizedRectangularDerivation δ)
      (normalizedRectangularDerivation_leibniz ρ σ δ hδ)).1 a‖ ≤ 2 * ‖a‖ := by
  refine (norm_rectangularRepresentation_apply ρ σ _ _ a).trans ?_
  have h := norm_normalizedRectangularDerivation_le δ
  nlinarith [norm_nonneg a]

section RowColumn

variable [PartialOrder A] [StarOrderedRing A]

/-- The upper-right corner transfers any matrix estimate for the normalized
triangular representation to the original derivation. -/
theorem rectangularDerivation_matrix_bound_of_triangular
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    {p q : ℕ} (X : Matrix (Fin p) (Fin q) A) {C : ℝ}
    (htri : ‖rectangularMatrixOperator
      (X.map (normalizedRectangularRepresentation ρ σ δ hδ).1)‖ ≤
        C * ‖CStarMatrix.ofMatrix X‖) :
    ‖rectangularMatrixOperator (X.map δ)‖ ≤ (C * ‖δ‖) * ‖CStarMatrix.ofMatrix X‖ := by
  let : SeminormedAddCommGroup (HilbertCopies K q →L[ℂ] HilbertCopies F p) := inferInstance
  let : NormedSpace ℂ (HilbertCopies K q →L[ℂ] HilbertCopies F p) := inferInstance
  by_cases hz : δ = 0
  · have hzero : X.map δ = 0 := by
      apply Matrix.ext
      intro i j
      simp [hz]
    rw [hzero, rectangularMatrixOperator_zero]
    simp [hz, ContinuousLinearMap.opNorm_zero]
  let δ₀ := normalizedRectangularDerivation δ
  let Φ := normalizedRectangularRepresentation ρ σ δ hδ
  have hupper (a : A) : (WithLp.fstL 2 ℂ F K).comp
      ((Φ.1 a).comp rectangularInr) = δ₀ a := by
    ext x
    simp [Φ, normalizedRectangularRepresentation, rectangularRepresentation,
      rectangularTriangular, rectangularInl, rectangularInr, δ₀]
  have hcompress : ‖rectangularMatrixOperator (X.map δ₀)‖ ≤
      ‖rectangularMatrixOperator (X.map Φ.1)‖ := by
    change ‖rectangularMatrixOperator (fun i j => δ₀ (X i j))‖ ≤
      ‖rectangularMatrixOperator (X.map Φ.1)‖
    simpa only [Matrix.map_apply, hupper] using norm_rectangularCorner_le (X.map Φ.1)
  have hn : ‖δ‖ ≠ 0 := (norm_ne_zero_iff (E := A →L[ℂ] (K →L[ℂ] F))).mpr hz
  have hc : (‖δ‖ : ℂ) * ((‖δ‖⁻¹ : ℝ) : ℂ) = 1 := by
    norm_cast
    exact mul_inv_cancel₀ hn
  have hδrecover (a : A) : δ a = (‖δ‖ : ℂ) • δ₀ a := by
    simp only [δ₀, normalizedRectangularDerivation, smul_apply, smul_smul, hc, one_smul]
  have hrecover : rectangularMatrixOperator (X.map δ) =
      (‖δ‖ : ℂ) • rectangularMatrixOperator (X.map δ₀) := by
    have hm : X.map δ = (‖δ‖ : ℂ) • X.map δ₀ := by
      apply Matrix.ext
      intro i j
      exact hδrecover (X i j)
    rw [hm, rectangularMatrixOperator_smul]
  rw [hrecover, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg δ)]
  calc
    ‖δ‖ * ‖rectangularMatrixOperator (X.map δ₀)‖ ≤
        ‖δ‖ * (C * ‖CStarMatrix.ofMatrix X‖) :=
      mul_le_mul_of_nonneg_left (hcompress.trans htri) (norm_nonneg δ)
    _ = (C * ‖δ‖) * ‖CStarMatrix.ofMatrix X‖ := by ring

/-- The manuscript's row/column derivation estimate, conditional only on the
norm-two specialization of the published Dickson estimate. -/
theorem rectangularDerivation_row_column
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    (dickson : DicksonTwoBound (A := A) (RectangularSum F K)) :
    RowBound δ ((4 * Real.sqrt 2) * ‖δ‖) ∧
      ColumnBound δ ((4 * Real.sqrt 2) * ‖δ‖) := by
  have hΦ := dickson (normalizedRectangularRepresentation ρ σ δ hδ)
    (norm_normalizedRectangularRepresentation_le_two ρ σ δ hδ)
  constructor
  · intro n X
    exact rectangularDerivation_matrix_bound_of_triangular ρ σ δ hδ X (hΦ.1 n X)
  · intro n X
    exact rectangularDerivation_matrix_bound_of_triangular ρ σ δ hδ X (hΦ.2 n X)

end RowColumn

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicDerivations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The cyclic-domain completely bounded estimate

Approximate cyclic column factorization and the column Leibniz identity
bound every finite matrix amplification of a derivation.
-/

noncomputable section
namespace KadisonSimilarity

open Filter
open scoped Topology CStarAlgebra

variable {A F K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [PartialOrder A] [StarOrderedRing A]

omit [CompleteSpace F] [CompleteSpace K] in
/-- A column bound controls its value on a unit vector. -/
theorem norm_columnAction_le {n : ℕ} {f : A → (K →L[ℂ] F)} {c : ℝ}
    (hc : ColumnBound f c) (W : Matrix (Fin n) (Fin 1) A) (ζ : K)
    (hζ : ‖ζ‖ = 1) : ‖columnAction f W ζ‖ ≤ c * ‖CStarMatrix.ofMatrix W‖ := by
  calc
    ‖columnAction f W ζ‖ ≤
        ‖rectangularMatrixOperator (W.map f)‖ * ‖(PiLp.single 2 (0 : Fin 1) ζ : HilbertCopies K 1)‖ :=
      (rectangularMatrixOperator (W.map f)).le_opNorm _
    _ = ‖rectangularMatrixOperator (W.map f)‖ := by
      rw [PiLp.norm_single, hζ, mul_one]
    _ ≤ c * ‖CStarMatrix.ofMatrix W‖ := hc n W

omit [PartialOrder A] [StarOrderedRing A] in
/-- The exact matrix-column Leibniz identity. -/
theorem rectangularDerivation_mul_column
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    {n : ℕ} (X : Matrix (Fin n) (Fin n) A)
    (W : Matrix (Fin n) (Fin 1) A) (ζ : K) :
    columnAction δ (X * W) ζ =
      matrixOperator (X.map ρ) (columnAction δ W ζ) +
        rectangularMatrixOperator (X.map δ) (columnAction σ W ζ) := by
  apply PiLp.ext
  intro i
  simp only [PiLp.add_apply, columnAction_apply, Matrix.mul_apply,
    map_sum, sum_apply, hδ, add_apply,
    ContinuousLinearMap.comp_apply, Finset.sum_add_distrib,
    matrixOperator_apply, rectangularMatrixOperator_apply, Matrix.map_apply]

/-- Rectangular C-star matrix multiplication is submultiplicative in the
square-times-column case used below. -/
theorem norm_cstarMatrix_mul_column_le {n : ℕ}
    (X : Matrix (Fin n) (Fin n) A) (W : Matrix (Fin n) (Fin 1) A) :
    ‖CStarMatrix.ofMatrix (X * W)‖ ≤
      ‖CStarMatrix.ofMatrix X‖ * ‖CStarMatrix.ofMatrix W‖ := by
  have hcomp : CStarMatrix.toCLM (CStarMatrix.ofMatrix (X * W)) =
      (CStarMatrix.toCLM (CStarMatrix.ofMatrix W)).comp
        (CStarMatrix.toCLM (CStarMatrix.ofMatrix X)) := by
    apply ContinuousLinearMap.ext
    intro v
    apply (WithCStarModule.equiv A (Fin 1 → A)).injective
    change Matrix.vecMul v (X * W) = Matrix.vecMul (Matrix.vecMul v X) W
    exact (Matrix.vecMul_vecMul v X W).symm
  rw [CStarMatrix.norm_def, hcomp]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)

/-- The column Leibniz identity gives a bound before taking an approximation
limit; only the column bound and the column norm enter. -/
theorem norm_derivation_on_column_le
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    {c : ℝ} (hc : 0 ≤ c) (hcol : ColumnBound δ c)
    {n : ℕ} (X : Matrix (Fin n) (Fin n) A)
    (W : Matrix (Fin n) (Fin 1) A) (hW : ‖CStarMatrix.ofMatrix W‖ ≤ 2)
    (ζ : K) (hζ : ‖ζ‖ = 1) :
    ‖rectangularMatrixOperator (X.map δ) (columnAction σ W ζ)‖ ≤
      (4 * c) * ‖CStarMatrix.ofMatrix X‖ := by
  have heq := rectangularDerivation_mul_column ρ σ δ hδ X W ζ
  have hsolve : rectangularMatrixOperator (X.map δ) (columnAction σ W ζ) =
      columnAction δ (X * W) ζ - matrixOperator (X.map ρ) (columnAction δ W ζ) := by
    exact eq_sub_of_add_eq' heq.symm
  have hρ : ‖matrixOperator (X.map ρ)‖ ≤ ‖CStarMatrix.ofMatrix X‖ := by
    simpa only [one_mul] using completeBound_starHom ρ n X
  calc
    ‖rectangularMatrixOperator (X.map δ) (columnAction σ W ζ)‖ =
        ‖columnAction δ (X * W) ζ -
          matrixOperator (X.map ρ) (columnAction δ W ζ)‖ := congrArg norm hsolve
    _ ≤ ‖columnAction δ (X * W) ζ‖ +
        ‖matrixOperator (X.map ρ) (columnAction δ W ζ)‖ := norm_sub_le _ _
    _ ≤ c * ‖CStarMatrix.ofMatrix (X * W)‖ +
        ‖matrixOperator (X.map ρ)‖ * ‖columnAction δ W ζ‖ :=
      add_le_add (norm_columnAction_le hcol _ ζ hζ) (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ c * (‖CStarMatrix.ofMatrix X‖ * ‖CStarMatrix.ofMatrix W‖) +
        ‖CStarMatrix.ofMatrix X‖ * (c * ‖CStarMatrix.ofMatrix W‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (norm_cstarMatrix_mul_column_le X W) hc
      · exact mul_le_mul hρ (norm_columnAction_le hcol W ζ hζ)
          (norm_nonneg _) (norm_nonneg _)
    _ = (2 * c * ‖CStarMatrix.ofMatrix X‖) * ‖CStarMatrix.ofMatrix W‖ := by ring
    _ ≤ (2 * c * ‖CStarMatrix.ofMatrix X‖) * 2 :=
      mul_le_mul_of_nonneg_left hW (by positivity)
    _ = (4 * c) * ‖CStarMatrix.ofMatrix X‖ := by ring

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_QuantitativeImplementation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.boundedHomOrbit_apply _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.listOrbitSum_append _root_.OAI.KadisonSimilarity.listOrbitSum_nil _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.pairRepresentation_fst _root_.OAI.KadisonSimilarity.pairRepresentation_snd _root_.OAI.KadisonSimilarity.rectangularDiagonalStarHom_apply _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.sharpHom_apply _root_.OAI.KadisonSimilarity.sharpVectorMap_apply _root_.OAI.KadisonSimilarity.similarityRepresentation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative implementation from a triangular similarity

Conjugating an orthogonal projection gives the implementing corner directly.
The norm bound is the condition number of the given similarity.
-/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A fixed similarity gives a commuting projection with norm bounded by its
condition number. -/
theorem exists_commuting_projection_norm (π : BoundedUnitalHom A H)
    (S : (H →L[ℂ] H)ˣ)
    (hS : ∀ a : A, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
      star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H)))
    (M : ClosedSubmodule ℂ H) (hM : ∀ a x, x ∈ M → π.1 a x ∈ M) :
    ∃ P : H →L[ℂ] H, (∀ x, P x ∈ M) ∧
      (∀ x, x ∈ M → P x = x) ∧ (∀ a, Commute P (π.1 a)) ∧
      ‖P‖ ≤ ‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖ := by
  let e := ContinuousLinearEquiv.ofUnit S
  let U (a : A) : H →L[ℂ] H :=
    e.toContinuousLinearMap * π.1 a * e.symm.toContinuousLinearMap
  let N : ClosedSubmodule ℂ H := M.mapEquiv e
  have hU : ∀ a, U (star a) = star (U a) := hS
  have hN : ∀ a x, x ∈ N → U a x ∈ N := by
    intro a x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨π.1 a y, hM a y hy, by simp [U, mul_apply_eq_comp]⟩
  let Q := N.toSubmodule.starProjection
  let P : H →L[ℂ] H := e.symm.toContinuousLinearMap.comp (Q.comp e.toContinuousLinearMap)
  have hmem (x : H) : P x ∈ M := by
    have h := Submodule.starProjection_apply_mem N.toSubmodule (e x)
    rcases h with ⟨y, hy, he⟩
    change e.symm (Q (e x)) ∈ M
    rw [← he]
    simpa using hy
  have hfix (x : H) (hx : x ∈ M) : P x = x := by
    have hn : e x ∈ N := ⟨x, hx, rfl⟩
    change e.symm (Q (e x)) = x
    rw [Submodule.starProjection_eq_self_iff.mpr hn]
    simp
  have hcomm (a : A) : Commute P (π.1 a) := by
    have hq := orthogonal_projection_commutes U hU N hN a
    change P * π.1 a = π.1 a * P
    ext x
    have h := congrArg (fun T : H →L[ℂ] H => e.symm (T (e x))) hq.eq
    simpa [P, Q, U, mul_apply_eq_comp] using h
  refine ⟨P, hmem, hfix, hcomm, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  calc
    ‖P x‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖Q (e x)‖ :=
      e.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e x‖ :=
      mul_le_mul_of_nonneg_left (N.toSubmodule.norm_starProjection_apply_le _) (norm_nonneg _)
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * (‖e.toContinuousLinearMap‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (e.toContinuousLinearMap.le_opNorm x) (norm_nonneg _)
    _ = (‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖) * ‖x‖ := by
      change ‖(↑S⁻¹ : H →L[ℂ] H)‖ * (‖(S : H →L[ℂ] H)‖ * ‖x‖) = _
      ring

variable {F K : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The implementing upper-right corner inherits the condition-number bound. -/
theorem rectangular_inner_of_similarity_norm
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    (S : (RectangularSum F K →L[ℂ] RectangularSum F K)ˣ)
    (hS : ∀ a : A,
      (S : RectangularSum F K →L[ℂ] RectangularSum F K) *
        (rectangularRepresentation ρ σ δ hδ).1 (star a) * ↑S⁻¹ =
      star ((S : RectangularSum F K →L[ℂ] RectangularSum F K) *
        (rectangularRepresentation ρ σ δ hδ).1 a * ↑S⁻¹)) :
    ∃ V : K →L[ℂ] F, (∀ a, δ a = V.comp (σ a) - (ρ a).comp V) ∧
      ‖V‖ ≤ ‖(S : RectangularSum F K →L[ℂ] RectangularSum F K)‖ *
        ‖(↑S⁻¹ : RectangularSum F K →L[ℂ] RectangularSum F K)‖ := by
  let π := rectangularRepresentation ρ σ δ hδ
  let M : ClosedSubmodule ℂ (RectangularSum F K) :=
    ⟨(WithLp.sndL 2 ℂ F K).ker, (WithLp.sndL 2 ℂ F K).isClosed_ker⟩
  have hM : ∀ a x, x ∈ M → π.1 a x ∈ M := by
    intro a x hx
    change x.snd = 0 at hx
    change (rectangularTriangular (ρ a) (δ a) (σ a) x).snd = 0
    simp [hx]
  obtain ⟨P, hm, hf, hp, hnorm⟩ := exists_commuting_projection_norm π S hS M hM
  let q : K →L[ℂ] F := (WithLp.fstL 2 ℂ F K).comp (P.comp rectangularInr)
  have hzero (x : RectangularSum F K) : (P x).snd = 0 := hm x
  have hfix (x : F) : P (rectangularInl x) = rectangularInl x :=
    hf _ (by change (rectangularInl x).snd = 0; simp [rectangularInl])
  have hdecomp (x : RectangularSum F K) :
      x = rectangularInl x.fst + rectangularInr x.snd := by
    apply (WithLp.equiv 2 (F × K)).injective
    apply Prod.ext <;> simp [rectangularInl, rectangularInr]
  have hfst (x : RectangularSum F K) : (P x).fst = x.fst + q x.snd := by
    nth_rw 1 [hdecomp x]
    rw [map_add, hfix]
    simp [q, rectangularInl]
  have hqnorm : ‖q‖ ≤ ‖P‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg P)
    intro x
    calc
      ‖q x‖ ≤ ‖P (rectangularInr x)‖ := WithLp.norm_fst_le F _
      _ ≤ ‖P‖ * ‖rectangularInr (F := F) x‖ := P.le_opNorm _
      _ = ‖P‖ * ‖x‖ := by
        change ‖P‖ * ‖WithLp.toLp 2 (0, x)‖ = _
        rw [WithLp.norm_toLp_snd]
  refine ⟨-q, ?_, (by simpa using hqnorm.trans hnorm)⟩
  intro a
  ext x
  have h := congrArg
    (fun T : RectangularSum F K →L[ℂ] RectangularSum F K =>
      (T (rectangularInr x)).fst) (hp a).eq
  change (P (rectangularTriangular (ρ a) (δ a) (σ a) (rectangularInr x))).fst =
    (rectangularTriangular (ρ a) (δ a) (σ a) (P (rectangularInr x))).fst at h
  rw [hfst, rectangularTriangular_fst, rectangularTriangular_snd,
    rectangularTriangular_fst, hzero] at h
  have hq (x : K) : (P (rectangularInr x)).fst = q x := rfl
  rw [hq] at h
  have hfst0 : (rectangularInr (F := F) x).fst = 0 := (rectangularInr_apply x).1
  have hsnd : (rectangularInr (F := F) x).snd = x := (rectangularInr_apply x).2
  simp only [hfst0, hsnd, map_zero, zero_add, add_zero] at h
  change δ a x = (-q) (σ a x) - ρ a ((-q) x)
  simp only [neg_apply, map_neg, sub_neg_eq_add]
  apply eq_neg_add_iff_add_eq.mpr
  simpa only [add_comm] using h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_CompletelyBoundedImplementation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedHomOrbit_apply _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.hilbertArrayFlatten_apply _root_.OAI.KadisonSimilarity.hilbertFourfoldFlatten_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.hilbertTripleFlatten_apply _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.listOrbitSum_append _root_.OAI.KadisonSimilarity.listOrbitSum_nil _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_matrixOperator _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.matrixLeftArray_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.pairRepresentation_fst _root_.OAI.KadisonSimilarity.pairRepresentation_snd _root_.OAI.KadisonSimilarity.representedDoubleMatrix_apply _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.sharpHom_apply _root_.OAI.KadisonSimilarity.sharpVectorMap_apply _root_.OAI.KadisonSimilarity.similarityRepresentation_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Implementation of completely bounded rectangular derivations -/

noncomputable section
namespace KadisonSimilarity

variable {A F K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [PartialOrder A] [StarOrderedRing A]

omit [CompleteSpace F] [CompleteSpace K] in
private theorem norm_rectangularInl_le_one : ‖rectangularInl (F := F) (K := K)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖WithLp.toLp 2 (x, 0)‖ ≤ 1 * ‖x‖
  simp [WithLp.norm_toLp_fst]

omit [CompleteSpace F] [CompleteSpace K] in
private theorem norm_rectangularSnd_le_one : ‖WithLp.sndL 2 ℂ F K‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using WithLp.norm_snd_le F x

omit [CompleteSpace F] [CompleteSpace K] in
/-- The off-diagonal square matrix is an isometric-coordinate compression. -/
theorem matrixOperator_offDiagonal {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (K →L[ℂ] F)) :
    matrixOperator (fun i j => (rectangularInl (F := F) (K := K)).comp ((X i j).comp (WithLp.sndL 2 ℂ F K))) =
      (mapCopies (rectangularInl (F := F) (K := K)) n).comp
        ((rectangularMatrixOperator X).comp (mapCopies (WithLp.sndL 2 ℂ F K) n)) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply PiLp.ext
  intro i
  calc
    _ = ∑ j : Fin n, (rectangularInl (F := F) (K := K))
        (X i j ((WithLp.sndL 2 ℂ F K) (ξ j))) :=
      matrixOperator_apply (H := RectangularSum F K) _ ξ i
    _ = (rectangularInl (F := F) (K := K))
        (∑ j : Fin n, X i j ((WithLp.sndL 2 ℂ F K) (ξ j))) := by
      rw [map_sum]
    _ = _ := by
      change _ = (mapCopies (rectangularInl (F := F) (K := K)) n
        (rectangularMatrixOperator X (mapCopies (WithLp.sndL 2 ℂ F K) n ξ))) i
      rw [mapCopies_apply, rectangularMatrixOperator_apply]
      congr 1

private theorem norm_comp_contracts
    {E₁ E₂ E₃ E₄ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]
    [NormedAddCommGroup E₄] [NormedSpace ℂ E₄]
    (L : E₃ →L[ℂ] E₄) (T : E₂ →L[ℂ] E₃) (R : E₁ →L[ℂ] E₂)
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) : ‖L.comp (T.comp R)‖ ≤ ‖T‖ := by
  calc
    ‖L.comp (T.comp R)‖ ≤ ‖L‖ * (‖T‖ * ‖R‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖T‖ * 1) := by gcongr
    _ = ‖T‖ := by ring

omit [CompleteSpace F] [CompleteSpace K] in
/-- The norm of the amplified off-diagonal block does not exceed that of the
original rectangular matrix. -/
theorem norm_matrixOperator_offDiagonal_le {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (K →L[ℂ] F)) :
    ‖matrixOperator (fun i j => (rectangularInl (F := F) (K := K)).comp ((X i j).comp (WithLp.sndL 2 ℂ F K)))‖ ≤
      ‖rectangularMatrixOperator X‖ := by
  have hL : ‖mapCopies (rectangularInl (F := F) (K := K)) n‖ ≤ 1 :=
    (norm_mapCopies_le _ _).trans norm_rectangularInl_le_one
  have hR : ‖mapCopies (WithLp.sndL 2 ℂ F K) n‖ ≤ 1 :=
    (norm_mapCopies_le _ _).trans norm_rectangularSnd_le_one
  calc
    _ = ‖(mapCopies (rectangularInl (F := F) (K := K)) n).comp
        ((rectangularMatrixOperator X).comp (mapCopies (WithLp.sndL 2 ℂ F K) n))‖ :=
      congrArg norm (matrixOperator_offDiagonal X)
    _ ≤ _ := norm_comp_contracts _ _ _ hL hR

/-- A rectangular complete bound controls the complete norm of its triangular
representation by one plus that bound. -/
theorem completeBound_rectangularRepresentation
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    {D : ℝ} (hD : RectangularCompleteBound δ D) :
    CompleteBound (rectangularRepresentation ρ σ δ hδ).1 (1 + D) := by
  intro n X
  let d := rectangularDiagonalStarHom ρ σ
  have hp (a : A) : (rectangularRepresentation ρ σ δ hδ).1 a =
      d a + (rectangularInl (F := F) (K := K)).comp ((δ a).comp (WithLp.sndL 2 ℂ F K)) := by
    ext x
    apply (WithLp.equiv 2 (F × K)).injective
    apply Prod.ext <;>
      simp [d, rectangularRepresentation, rectangularTriangular,
        rectangularInl, rectangularInr, rectangularDiagonalStarHom]
  let Y : Matrix (Fin n) (Fin n) (RectangularSum F K →L[ℂ] RectangularSum F K) :=
    fun i j => (rectangularInl (F := F) (K := K)).comp
      ((δ (X i j)).comp (WithLp.sndL 2 ℂ F K))
  have hm : X.map (rectangularRepresentation ρ σ δ hδ).1 = X.map d + Y := by
    apply Matrix.ext
    intro i j
    exact hp (X i j)
  rw [hm]
  change ‖(operatorMatrixRepresentation (H := RectangularSum F K) n) (X.map d + Y)‖ ≤ _
  rw [map_add]
  calc
    _ ≤ ‖matrixOperator (X.map d)‖ +
        ‖matrixOperator (fun i j => (rectangularInl (F := F) (K := K)).comp
          ((δ (X i j)).comp (WithLp.sndL 2 ℂ F K)))‖ := norm_add_le _ _
    _ ≤ 1 * ‖CStarMatrix.ofMatrix X‖ + D * ‖CStarMatrix.ofMatrix X‖ :=
      add_le_add (completeBound_starHom d n X)
        ((norm_matrixOperator_offDiagonal_le (X.map δ)).trans (hD n X))
    _ = (1 + D) * ‖CStarMatrix.ofMatrix X‖ := by ring

omit [CompleteSpace F] [CompleteSpace K] in
/-- Rescaling a rectangular derivation rescales all of its matrix bounds. -/
theorem rectangularCompleteBound_normalized
    (δ : A →L[ℂ] (K →L[ℂ] F)) {D : ℝ} (hD : RectangularCompleteBound δ D) :
    RectangularCompleteBound (normalizedRectangularDerivation δ) (D * ‖δ‖⁻¹) := by
  intro n X
  let : SeminormedAddCommGroup (HilbertCopies K n →L[ℂ] HilbertCopies F n) := inferInstance
  let : NormedSpace ℂ (HilbertCopies K n →L[ℂ] HilbertCopies F n) := inferInstance
  have hm : X.map (normalizedRectangularDerivation δ) =
      ((‖δ‖⁻¹ : ℝ) : ℂ) • X.map δ := by
    apply Matrix.ext
    intro i j
    rfl
  rw [hm, rectangularMatrixOperator_smul, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg δ))]
  calc
    ‖δ‖⁻¹ * ‖rectangularMatrixOperator (X.map δ)‖ ≤
        ‖δ‖⁻¹ * (D * ‖CStarMatrix.ofMatrix X‖) :=
      mul_le_mul_of_nonneg_left (hD n X) (inv_nonneg.mpr (norm_nonneg δ))
    _ = (D * ‖δ‖⁻¹) * ‖CStarMatrix.ofMatrix X‖ := by ring

/-- The manuscript's completely bounded implementation lemma, using only the
explicit Paulsen input. The projection argument actually bounds the implementer
by the first power of the condition number, hence implies the stated square. -/
theorem rectangular_inner_of_completeBound
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    {D : ℝ} (hD0 : 0 ≤ D) (hD : RectangularCompleteBound δ D)
    (paulsen : PaulsenSimilarityInput (normalizedRectangularRepresentation ρ σ δ hδ)) :
    ∃ V : K →L[ℂ] F, (∀ a, δ a = V.comp (σ a) - (ρ a).comp V) ∧
      ‖V‖ ≤ ‖δ‖ * (1 + D * ‖δ‖⁻¹) ^ 2 := by
  let : SeminormedAddCommGroup (K →L[ℂ] F) := inferInstance
  let : NormedSpace ℂ (K →L[ℂ] F) := inferInstance
  by_cases hz : δ = 0
  · refine ⟨0, ?_, ?_⟩
    · intro a
      simp [hz]
    · simp [hz]
  let δ₀ := normalizedRectangularDerivation δ
  let G : ℝ := 1 + D * ‖δ‖⁻¹
  have hG : 1 ≤ G := by
    dsimp [G]
    exact le_add_of_nonneg_right (mul_nonneg hD0 (inv_nonneg.mpr (norm_nonneg δ)))
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hcb : CompleteBound (normalizedRectangularRepresentation ρ σ δ hδ).1 G :=
    completeBound_rectangularRepresentation ρ σ δ₀
      (normalizedRectangularDerivation_leibniz ρ σ δ hδ)
      (rectangularCompleteBound_normalized δ hD)
  obtain ⟨S, hSnorm, hSstar⟩ := paulsen G hG0 hcb
  obtain ⟨V₀, hV₀, hVnorm⟩ := rectangular_inner_of_similarity_norm ρ σ δ₀
    (normalizedRectangularDerivation_leibniz ρ σ δ hδ) S hSstar
  have hn : ‖δ‖ ≠ 0 := (norm_ne_zero_iff (E := A →L[ℂ] (K →L[ℂ] F))).mpr hz
  have hc : (‖δ‖ : ℂ) * ((‖δ‖⁻¹ : ℝ) : ℂ) = 1 := by
    norm_cast
    exact mul_inv_cancel₀ hn
  have hrec (a : A) : δ a = (‖δ‖ : ℂ) • δ₀ a := by
    simp only [δ₀, normalizedRectangularDerivation, smul_apply, smul_smul, hc, one_smul]
  refine ⟨(‖δ‖ : ℂ) • V₀, ?_, ?_⟩
  · intro a
    rw [hrec a, hV₀ a]
    ext x
    simp only [smul_apply, sub_apply, ContinuousLinearMap.comp_apply, map_smul, smul_sub]
  · calc
      ‖(‖δ‖ : ℂ) • V₀‖ = ‖δ‖ * ‖V₀‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg δ)]
      _ ≤ ‖δ‖ * G := mul_le_mul_of_nonneg_left (hVnorm.trans hSnorm) (norm_nonneg δ)
      _ ≤ ‖δ‖ * G ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg δ)
        nlinarith

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FullColumns
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Extending a corner intertwiner through finitely many matrix units

These are the matrix-coordinate steps of `lem:full-column`: coordinatewise
amplification preserves the error norm and intertwines a full operator matrix
as soon as it intertwines each entry. The geometric construction of the
corner and its matrix-unit coordinates is still required.
-/

noncomputable section

namespace KadisonSimilarity

variable {E F K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Positive finite amplification of a rectangular operator preserves its norm. -/
theorem norm_mapCopies (T : K →L[ℂ] F) {n : ℕ} (hn : 0 < n) :
    ‖mapCopies T n‖ = ‖T‖ := by
  apply le_antisymm (norm_mapCopies_le T n)
  apply ContinuousLinearMap.opNorm_le_bound T (norm_nonneg (mapCopies T n))
  intro x
  let i : Fin n := ⟨0, hn⟩
  have hmap : mapCopies T n (PiLp.single 2 i x) = PiLp.single 2 i (T x) := by
    ext j
    by_cases h : j = i
    · subst j
      simp only [mapCopies_apply, PiLp.single_eq_same]
    · simp only [mapCopies_apply, PiLp.single_apply, ite_eq_right h, map_zero]
  have h := (mapCopies T n).le_opNorm (PiLp.single 2 i x)
  simpa only [hmap, PiLp.norm_single] using h

/-- Entrywise intertwining suffices for intertwining the full matrix algebra. -/
theorem mapCopies_intertwines_matrix (T : K →L[ℂ] F) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (K →L[ℂ] K))
    (Y : Matrix (Fin n) (Fin n) (F →L[ℂ] F))
    (hXY : ∀ i j, T.comp (X i j) = (Y i j).comp T) :
    (mapCopies T n).comp (matrixOperator X) =
      (matrixOperator Y).comp (mapCopies T n) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply, mapCopies_apply, matrixOperator_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun L : K →L[ℂ] F => L (x j)) (hXY i j)

/-- Changing isometric domain coordinates preserves the operator norm. -/
theorem norm_comp_isometricCoordinates (T : K →L[ℂ] F) (U : E ≃ₗᵢ[ℂ] K) :
    ‖T.comp U.toContinuousLinearEquiv.toContinuousLinearMap‖ = ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro x
    change ‖T (U x)‖ ≤ ‖T‖ * ‖x‖
    simpa only [LinearIsometryEquiv.norm_map] using T.le_opNorm (U x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (T.comp U.toContinuousLinearEquiv.toContinuousLinearMap).le_opNorm (U.symm x)
    simpa using h

/-- Isometric codomain coordinates also preserve the operator norm. -/
theorem norm_isometricCoordinates_comp (T : K →L[ℂ] F) (V : F ≃ₗᵢ[ℂ] E) :
    ‖V.toContinuousLinearEquiv.toContinuousLinearMap.comp T‖ = ‖T‖ := by
  exact V.toLinearIsometry.norm_toContinuousLinearMap_comp

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FullColumnTheorem
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The full-column implementation argument

The corner commutator is constructed here, corrected by the proved cyclic
implementation theorem, and extended through finite matrix coordinates with
exactly the same norm. Extension by zero and the tracial commutation theorem
then identify the resulting intertwiner as a right multiplier.

The finite-factor realization of the corner and its matrix coordinates remains
explicit geometric data; the full-column conclusion is not an input.
-/

noncomputable section
namespace KadisonSimilarity

open scoped CStarAlgebra

section MatrixCoordinates

variable {P C H D F K : Type*} [CStarAlgebra P] [CStarAlgebra C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

namespace FullColumnCoordinates

variable {L : P →⋆ₐ[ℂ] (H →L[ℂ] H)} {Lr : P →⋆ₐ[ℂ] (D →L[ℂ] D)}
  {ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F)} {σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)} {n : ℕ}

/-- No factor depending on the number of matrix units enters the norm. -/
theorem norm_extend (c : FullColumnCoordinates L Lr ρ σ n) (hn : 0 < n)
    (T : K →L[ℂ] F) : ‖c.extend T‖ = ‖T‖ := by
  rw [extend, norm_isometricCoordinates_comp, norm_comp_isometricCoordinates,
    norm_mapCopies _ hn]

theorem norm_extend_sub (c : FullColumnCoordinates L Lr ρ σ n) (hn : 0 < n)
    (S T : K →L[ℂ] F) : ‖c.extend S - c.extend T‖ = ‖S - T‖ := by
  rw [← extend_sub, norm_extend c hn]

/-- An intertwiner for the corner extends to one for the whole left action. -/
theorem extend_intertwines (c : FullColumnCoordinates L Lr ρ σ n)
    (T : K →L[ℂ] F) (hT : ∀ a, T.comp (σ a) = (ρ a).comp T) (a : P) :
    (c.extend T).comp (Lr a) = (L a).comp (c.extend T) := by
  ext x
  apply c.codomain.injective
  simp only [ContinuousLinearMap.comp_apply, extend_apply, c.domain_action,
    c.codomain_action]
  exact congrArg (fun T => T (c.domain x))
    (mapCopies_intertwines_matrix T _ _ (fun i j => hT (c.entry a i j)))

end FullColumnCoordinates
end MatrixCoordinates

section RightMultipliers

variable {P H D : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]

/-- A full-column intertwiner extends by zero to a left-module endomorphism;
tracial commutation therefore makes it a right multiplier supported on `r`. -/
theorem exists_supported_right_multiplier
    (L : P →⋆ₐ[ℂ] (H →L[ℂ] H)) (Lr : P →⋆ₐ[ℂ] (D →L[ℂ] D))
    (R : TracialRightAction (P := P) (H := H)) (r : P)
    (inc : D →L[ℂ] H) (pr : H →L[ℂ] D)
    (hpr : pr.comp inc = ContinuousLinearMap.id ℂ D)
    (hr : inc.comp pr = R.right r)
    (hmodule : ∀ a, pr.comp (L a) = (Lr a).comp pr)
    (commutation : TracialCommutationInput L R)
    (T : D →L[ℂ] H) (hT : ∀ a, T.comp (Lr a) = (L a).comp T) :
    ∃ b : P, r * b = b ∧ (R.right b).comp inc = T := by
  let Z := T.comp pr
  have hZ (a : P) : Z.comp (L a) = (L a).comp Z := by
    dsimp [Z]
    rw [ContinuousLinearMap.comp_assoc, hmodule, ← ContinuousLinearMap.comp_assoc,
      hT, ContinuousLinearMap.comp_assoc]
  obtain ⟨b, hb⟩ := commutation Z hZ
  refine ⟨b, R.injective ?_, ?_⟩
  · rw [R.mul, hb, ← hr]
    dsimp [Z]
    rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc pr,
      hpr, ContinuousLinearMap.id_comp]
  · rw [hb]
    dsimp [Z]
    rw [ContinuousLinearMap.comp_assoc, hpr, ContinuousLinearMap.comp_id]

end RightMultipliers

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicColumnTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.hilbertArrayFlatten_apply _root_.OAI.KadisonSimilarity.hilbertFourfoldFlatten_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.hilbertTripleFlatten_apply _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.matrixLeftArray_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.pairRepresentation_fst _root_.OAI.KadisonSimilarity.pairRepresentation_snd _root_.OAI.KadisonSimilarity.representedDoubleMatrix_apply _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dense cyclic orbits give the bounded column tests needed for the
matrix derivation estimate. The unit vector may vary with the test. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped ComplexOrder Topology

variable {A K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Bounded cyclic column tests suffice for the full matrix estimate. -/
theorem rectangularDerivation_bound_of_cyclicColumnTests
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    {c : ℝ} (hc : 0 ≤ c) (hcol : ColumnBound δ c)
    (htests : CyclicColumnTests σ) (n : ℕ) (X : Matrix (Fin n) (Fin n) A) :
    ‖rectangularMatrixOperator (X.map δ)‖ ≤ (4 * c) * ‖CStarMatrix.ofMatrix X‖ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro ξ hξ
  let D := rectangularMatrixOperator (X.map δ)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨ζ, W, hζ, hW, herr⟩ := htests n ξ hξ (ε / (‖D‖ + 1)) (by positivity)
  let v := columnAction σ W ζ
  have hv := norm_derivation_on_column_le ρ σ δ hδ hc hcol X W hW ζ hζ
  have he : ‖D ξ - D v‖ ≤ ε := by
    rw [← map_sub]
    calc
      _ ≤ ‖D‖ * ‖ξ - v‖ := D.le_opNorm _
      _ ≤ ‖D‖ * (ε / (‖D‖ + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg D)
        simpa only [norm_sub_rev] using herr.le
      _ ≤ ε := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg D]
  exact (norm_le_norm_sub_add (D ξ) (D v)).trans (by linarith)

/-- A cyclic representation supplies the completely bounded derivation estimate directly. -/
theorem cyclic_derivation_implementation_of_column_tests
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    (htests : CyclicColumnTests σ)
    (paulsen : PaulsenSimilarityInput (normalizedRectangularRepresentation ρ σ δ hδ)) :
    ∃ V : K →L[ℂ] F, (∀ a, δ a = V.comp (σ a) - (ρ a).comp V) ∧
      ‖V‖ ≤ (1 + 4 * (4 * Real.sqrt 2)) ^ 2 * ‖δ‖ := by
  have hcol := (rectangularDerivation_row_column ρ σ δ hδ dicksonTwoBound_proved).2
  let D : ℝ := 4 * (4 * Real.sqrt 2) * ‖δ‖
  have hD : RectangularCompleteBound δ D := by
    intro n X
    convert rectangularDerivation_bound_of_cyclicColumnTests ρ σ δ hδ
      (by positivity : 0 ≤ (4 * Real.sqrt 2) * ‖δ‖) hcol htests n X using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [D]
    ring
  obtain ⟨V, hV, hb⟩ := rectangular_inner_of_completeBound ρ σ δ hδ
    (by dsimp [D]; positivity : 0 ≤ D) hD paulsen
  refine ⟨V, hV, ?_⟩
  by_cases hz : ‖δ‖ = 0
  · simpa [hz, D] using hb
  have hcancel : D * ‖δ‖⁻¹ = 4 * (4 * Real.sqrt 2) := by
    dsimp [D]
    rw [mul_assoc, mul_inv_cancel₀ hz, mul_one]
  calc
    ‖V‖ ≤ ‖δ‖ * (1 + D * ‖δ‖⁻¹) ^ 2 := hb
    _ = (1 + 4 * (4 * Real.sqrt 2)) ^ 2 * ‖δ‖ := by rw [hcancel]; ring

/-- The corner correction needs only the direct cyclic column tests. -/
theorem exists_corner_intertwiner_of_column_tests
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (G : K →L[ℂ] F) {ε : ℝ} (hG : ‖cornerCommutator ρ σ G‖ ≤ ε)
    (htests : CyclicColumnTests σ)
    (paulsen : PaulsenSimilarityInput (normalizedRectangularRepresentation ρ σ
      (cornerCommutator ρ σ G) (cornerCommutator_leibniz ρ σ G))) :
    ∃ T : K →L[ℂ] F, (∀ a, T.comp (σ a) = (ρ a).comp T) ∧
      ‖G - T‖ ≤ (1 + 4 * (4 * Real.sqrt 2)) ^ 2 * ε := by
  obtain ⟨V, hV, hnV⟩ := cyclic_derivation_implementation_of_column_tests
    ρ σ (cornerCommutator ρ σ G) (cornerCommutator_leibniz ρ σ G) htests paulsen
  refine ⟨G - V, ?_, ?_⟩
  · intro a
    have h := hV a
    ext x
    have hx := congrArg (fun T : K →L[ℂ] F => T x) h
    simp only [cornerCommutator_apply, sub_apply, ContinuousLinearMap.comp_apply] at hx ⊢
    simp only [map_sub]
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using sub_eq_sub_iff_add_eq_add.mp hx
  · simpa only [sub_sub_cancel] using hnV.trans
      (mul_le_mul_of_nonneg_left hG (sq_nonneg _))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_SimilarityMetric
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quantitative positive metric from an invertible star intertwiner

This is the final geometric step of Paulsen's theorem. The intertwiner may
map to a different Hilbert space. Its positive metric on the original space
and its positive square root yield the actual similarity unit, with exactly
the product of the forward and inverse operator norms.
-/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap
open scoped ComplexOrder

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The square of any bounded star intertwiner is a metric for the original
homomorphism, without an invertibility assumption. -/
theorem intertwiner_metric_identity (π : BoundedUnitalHom A H)
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K)
    (hW : ∀ a, W.comp (π.1 a) = (σ a).comp W) (a : A) :
    (W.adjoint.comp W).comp (π.1 (star a)) =
      (π.1 a).adjoint.comp (W.adjoint.comp W) := by
  have hadj : (π.1 a).adjoint.comp W.adjoint = W.adjoint.comp (σ (star a)) := by
    simpa only [adjoint_comp, map_star, star_eq_adjoint] using
      congrArg ContinuousLinearMap.adjoint (hW a)
  calc
    (W.adjoint.comp W).comp (π.1 (star a)) =
        W.adjoint.comp (W.comp (π.1 (star a))) := comp_assoc _ _ _
    _ = W.adjoint.comp ((σ (star a)).comp W) := by rw [hW]
    _ = (W.adjoint.comp (σ (star a))).comp W := (comp_assoc _ _ _).symm
    _ = ((π.1 a).adjoint.comp W.adjoint).comp W := by rw [← hadj]
    _ = (π.1 a).adjoint.comp (W.adjoint.comp W) := comp_assoc _ _ _

/-- The metric is positive because it is an adjoint square. -/
theorem intertwinerMetric_nonneg (W : H →L[ℂ] K) : 0 ≤ W.adjoint.comp W := by
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (ContinuousLinearMap.isPositive_adjoint_comp_self W)

/-- A square root of the positive metric preserves both operator norms
needed for the sharp similarity estimate. -/
theorem exists_positive_sqrt_metric_unit (W : H →L[ℂ] K) (L : K →L[ℂ] H)
    (hLW : L.comp W = 1) (hWL : W.comp L = 1) :
    ∃ S : (H →L[ℂ] H)ˣ,
      0 ≤ (S : H →L[ℂ] H) ∧
      star (S : H →L[ℂ] H) * (S : H →L[ℂ] H) = W.adjoint.comp W ∧
      ‖(S : H →L[ℂ] H)‖ = ‖W‖ ∧ ‖(↑S⁻¹ : H →L[ℂ] H)‖ = ‖L‖ := by
  let Q := intertwinerMetricUnit W L hLW hWL
  have hQ : 0 ≤ (Q : H →L[ℂ] H) := intertwinerMetric_nonneg W
  have hu : IsUnit (CFC.sqrt (Q : H →L[ℂ] H)) :=
    (CFC.isUnit_sqrt_iff _ hQ).mpr Q.isUnit
  obtain ⟨S, hS⟩ := hu
  have hSstar : star (S : H →L[ℂ] H) = (S : H →L[ℂ] H) := by
    rw [hS]
    exact (CFC.sqrt_nonneg _).star_eq
  have hSq : (S : H →L[ℂ] H) * (S : H →L[ℂ] H) = (Q : H →L[ℂ] H) := by
    rw [hS]
    exact CFC.sqrt_mul_sqrt_self _ hQ
  have hmetric : star (S : H →L[ℂ] H) * (S : H →L[ℂ] H) =
      W.adjoint.comp W := by rw [hSstar, hSq]; rfl
  have hnorm : ‖(S : H →L[ℂ] H)‖ = ‖W‖ := by
    have h := CStarRing.norm_star_mul_self (x := (S : H →L[ℂ] H))
    rw [hmetric, norm_adjoint_comp_self] at h
    nlinarith [norm_nonneg (S : H →L[ℂ] H), norm_nonneg W]
  have hunit : S * S = Q := Units.ext hSq
  have hinvSq : (↑S⁻¹ : H →L[ℂ] H) * (↑S⁻¹ : H →L[ℂ] H) =
      L.comp L.adjoint := by
    have h := congrArg (fun U : (H →L[ℂ] H)ˣ => (↑U⁻¹ : H →L[ℂ] H)) hunit
    calc
      (↑S⁻¹ : H →L[ℂ] H) * (↑S⁻¹ : H →L[ℂ] H) = ↑((S * S)⁻¹) := by
        simp only [mul_inv_rev, Units.val_mul]
      _ = (↑Q⁻¹ : H →L[ℂ] H) := h
      _ = L.comp L.adjoint := rfl
  have hSstarU : star S = S := Units.ext hSstar
  have hinvstar : star (↑S⁻¹ : H →L[ℂ] H) = (↑S⁻¹ : H →L[ℂ] H) := by
    rw [← Units.coe_star, star_inv, hSstarU]
  have hinvnorm : ‖(↑S⁻¹ : H →L[ℂ] H)‖ = ‖L‖ := by
    have h := CStarRing.norm_star_mul_self (x := (↑S⁻¹ : H →L[ℂ] H))
    rw [hinvstar, hinvSq] at h
    have hLL := norm_adjoint_comp_self L.adjoint
    rw [adjoint_adjoint, adjoint.norm_map] at hLL
    rw [hLL] at h
    nlinarith [norm_nonneg (↑S⁻¹ : H →L[ℂ] H), norm_nonneg L]
  exact ⟨S, by rw [hS]; exact CFC.sqrt_nonneg _, hmetric, hnorm, hinvnorm⟩

/-- The positive metric construction gives an invertible star intertwiner. -/
theorem exists_sqrt_metric_unit (W : H →L[ℂ] K) (L : K →L[ℂ] H)
    (hLW : L.comp W = 1) (hWL : W.comp L = 1) :
    ∃ S : (H →L[ℂ] H)ˣ,
      star (S : H →L[ℂ] H) * (S : H →L[ℂ] H) = W.adjoint.comp W ∧
      ‖(S : H →L[ℂ] H)‖ = ‖W‖ ∧ ‖(↑S⁻¹ : H →L[ℂ] H)‖ = ‖L‖ := by
  obtain ⟨S, _, hS⟩ := exists_positive_sqrt_metric_unit W L hLW hWL
  exact ⟨S, hS⟩

/-- An invertible bounded intertwiner into a star representation supplies
similarity on the original space with its exact condition-number bound. -/
theorem quantitative_similarity_of_intertwiner (π : BoundedUnitalHom A H)
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) (L : K →L[ℂ] H)
    (hLW : L.comp W = 1) (hWL : W.comp L = 1)
    (hW : ∀ a, W.comp (π.1 a) = (σ a).comp W) :
    ∃ S : (H →L[ℂ] H)ˣ,
      ‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖ ≤ ‖W‖ * ‖L‖ ∧
      ∀ a, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
        star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H)) := by
  obtain ⟨S, hmetric, hnorm, hinvnorm⟩ := exists_sqrt_metric_unit W L hLW hWL
  refine ⟨S, by rw [hnorm, hinvnorm], ?_⟩
  intro a
  have h := intertwiner_metric_identity π σ W hW a
  change (W.adjoint.comp W) * π.1 (star a) = star (π.1 a) * (W.adjoint.comp W) at h
  rw [← hmetric] at h
  have he := congrArg (fun X : H →L[ℂ] H =>
    star (↑S⁻¹ : H →L[ℂ] H) * X * (↑S⁻¹ : H →L[ℂ] H)) h
  simpa only [star_mul, star_inv, mul_assoc, ← Units.coe_star_inv, ← Units.coe_star,
    Units.inv_mul, Units.mul_inv, Units.inv_mul_cancel_left,
    Units.mul_inv_cancel_left, mul_one, one_mul] using he

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_FactorizationSpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reducing space generated by a homomorphism factorization

Only the vectors generated by the right factor are needed. Multiplicativity
makes the left factor an intertwiner on this closed span. Its kernel is then
a reducing subspace, which is the geometric input to invertible similarity.
-/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem right_mem_factorizationSpace (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (W : H →L[ℂ] K) (x : H) : W x ∈ factorizationSpace σ W := by
  apply (Submodule.span ℂ _).le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨(1, x), by simp⟩

/-- The generating space is invariant under the whole star representation. -/
theorem factorizationSpace_invariant (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (W : H →L[ℂ] K) (a : A) (x : K) (hx : x ∈ factorizationSpace σ W) :
    σ a x ∈ factorizationSpace σ W := by
  let N := Submodule.span ℂ (Set.range fun p : A × H => σ p.1 (W p.2))
  have hi : N ≤ N.comap (σ a).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨b, y⟩, rfl⟩
    apply Submodule.subset_span
    exact ⟨(a * b, y), by simp only [map_mul, mul_apply_eq_comp]; rfl⟩
  have hm : Set.MapsTo (σ a) (N : Set K) (N : Set K) := fun _ hy => hi hy
  exact hm.closure (σ a).continuous hx

/-- The left factor intertwines on the closed cyclic span, by continuity
from the algebraic generators and multiplicativity of the homomorphism. -/
theorem left_intertwines_factorizationSpace (π : BoundedUnitalHom A H)
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) (L : K →L[ℂ] H)
    (hf : ∀ a, L.comp ((σ a).comp W) = π.1 a)
    (a : A) (x : K) (hx : x ∈ factorizationSpace σ W) :
    L (σ a x) = π.1 a (L x) := by
  let D := L.comp (σ a) - (π.1 a).comp L
  have hs : Submodule.span ℂ (Set.range fun p : A × H => σ p.1 (W p.2)) ≤
      D.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨b, y⟩, rfl⟩
    change L (σ a (σ b (W y))) - π.1 a (L (σ b (W y))) = 0
    have hab := congrArg (fun T : H →L[ℂ] H => T y) (hf (a * b))
    have hb := congrArg (fun T : H →L[ℂ] H => T y) (hf b)
    simp only [map_mul, comp_apply, mul_apply_eq_comp] at hab hb
    rw [hab, hb]
    exact sub_self _
  have hc : closure (Submodule.span ℂ
      (Set.range fun p : A × H => σ p.1 (W p.2)) : Set K) ⊆ (D.ker : Set K) :=
    closure_minimal hs D.isClosed_ker
  exact sub_eq_zero.mp (hc hx)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_FactorizationGeometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the kernel of a star intertwiner

A surjective intertwiner with a bounded right inverse restricts to an
isomorphism on the orthogonal complement of its kernel. Orthogonal
projection does not increase the right-inverse norm, which retains the
sharp bound needed for quantitative similarity.
-/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A bounded right inverse of a surjective star intertwiner gives
similarity with no increase in the product of its two norms. -/
theorem quantitative_similarity_of_surjective_intertwiner
    (π : BoundedUnitalHom A H) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (W : H →L[ℂ] K) (L : K →L[ℂ] H) (hLW : L.comp W = 1)
    (hL : ∀ a, L.comp (σ a) = (π.1 a).comp L) :
    ∃ S : (H →L[ℂ] H)ˣ,
      ‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖ ≤ ‖W‖ * ‖L‖ ∧
      ∀ a, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
        star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H)) := by
  let N : ClosedSubmodule ℂ K := ⟨L.ker, L.isClosed_ker⟩
  let : CompleteSpace N.toSubmodule := N.isClosed.completeSpace_coe
  let E : ClosedSubmodule ℂ K := ⟨N.toSubmoduleᗮ, N.toSubmodule.isClosed_orthogonal⟩
  let : CompleteSpace E.toSubmodule := E.isClosed.completeSpace_coe
  have hN (a : A) (x : K) (hx : x ∈ N) : σ a x ∈ N := by
    change L (σ a x) = 0
    have h := congrArg (fun T : K →L[ℂ] H => T x) (hL a)
    change L x = 0 at hx
    simpa only [comp_apply, hx, map_zero] using h
  have hE (a : A) (x : K) (hx : x ∈ E) : σ a x ∈ E := by
    apply (N.toSubmodule.mem_orthogonal _).mpr
    intro y hy
    rw [← adjoint_inner_left, ← star_eq_adjoint, ← map_star]
    exact (N.toSubmodule.mem_orthogonal x).mp hx _ (hN (star a) y hy)
  let σ₀ := restrictStarRepresentation σ E hE
  let L₀ : E →L[ℂ] H := L.domRestrict E.toSubmodule
  let W₀ : H →L[ℂ] E := E.toSubmodule.orthogonalProjectionOnto.comp W
  have hL₀W₀ : L₀.comp W₀ = 1 := by
    ext x
    change L ((N.toSubmoduleᗮ).orthogonalProjectionOnto (W x) : K) = x
    rw [N.toSubmodule.orthogonalProjectionOnto_orthogonal]
    change L (W x - N.toSubmodule.starProjection (W x)) = x
    have hz : L (N.toSubmodule.starProjection (W x)) = 0 :=
      Submodule.starProjection_apply_mem N.toSubmodule (W x)
    have hw := congrArg (fun T : H →L[ℂ] H => T x) hLW
    simpa only [map_sub, hz, sub_zero, comp_apply, one_def, id_apply] using hw
  have hL₀inj : Function.Injective L₀ := by
    intro x y hxy
    apply Subtype.ext
    have hk : (x : K) - (y : K) ∈ N := by
      change L ((x : K) - (y : K)) = 0
      change L (x : K) = L (y : K) at hxy
      rw [map_sub, hxy, sub_self]
    have he : (x : K) - (y : K) ∈ N.toSubmoduleᗮ := E.sub_mem x.property y.property
    have hz := (N.toSubmodule.mem_orthogonal _).mp he _ hk
    exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℂ)).mp hz)
  have hW₀L₀ : W₀.comp L₀ = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    apply hL₀inj
    exact congrArg (fun T : H →L[ℂ] H => T (L₀ x)) hL₀W₀
  have hL₀ (a : A) : L₀.comp (σ₀ a) = (π.1 a).comp L₀ := by
    ext x
    exact congrArg (fun T : K →L[ℂ] H => T x) (hL a)
  have hW₀ (a : A) : W₀.comp (π.1 a) = (σ₀ a).comp W₀ := by
    apply ContinuousLinearMap.ext
    intro x
    apply hL₀inj
    have hlx := congrArg (fun T : H →L[ℂ] H => T x) hL₀W₀
    have hla := congrArg (fun T : H →L[ℂ] H => T (π.1 a x)) hL₀W₀
    have hi := congrArg (fun T : E →L[ℂ] H => T (W₀ x)) (hL₀ a)
    change L₀ (W₀ (π.1 a x)) = L₀ (σ₀ a (W₀ x))
    simpa only [comp_apply, one_def, id_apply] using hla.trans (hi.trans
      (congrArg (π.1 a) hlx)).symm
  have hnW : ‖W₀‖ ≤ ‖W‖ := by
    apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    exact (E.toSubmodule.norm_orthogonalProjectionOnto_apply_le (W x)).trans
      (W.le_opNorm x)
  have hnL : ‖L₀‖ ≤ ‖L‖ := by
    apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    exact L.le_opNorm (x : K)
  obtain ⟨S, hS, hstar⟩ := quantitative_similarity_of_intertwiner
    π σ₀ W₀ L₀ hL₀W₀ hW₀L₀ hW₀
  exact ⟨S, hS.trans (mul_le_mul hnW hnL (norm_nonneg _) (norm_nonneg _)), hstar⟩

/-- Multiplicativity upgrades a bounded star-representation factorization
to a similarity, with the original product bound. -/
theorem quantitative_similarity_of_factorization
    (π : BoundedUnitalHom A H) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (W : H →L[ℂ] K) (L : K →L[ℂ] H)
    (hf : ∀ a, L.comp ((σ a).comp W) = π.1 a) :
    ∃ S : (H →L[ℂ] H)ˣ,
      ‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖ ≤ ‖W‖ * ‖L‖ ∧
      ∀ a, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
        star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H)) := by
  let M := factorizationSpace σ W
  let : CompleteSpace M.toSubmodule := M.isClosed.completeSpace_coe
  let σ₀ := restrictStarRepresentation σ M (factorizationSpace_invariant σ W)
  let W₀ : H →L[ℂ] M := W.codRestrict M.toSubmodule (right_mem_factorizationSpace σ W)
  let L₀ : M →L[ℂ] H := L.domRestrict M.toSubmodule
  have hLW : L₀.comp W₀ = 1 := by
    ext x
    change L (W x) = x
    have h := congrArg (fun T : H →L[ℂ] H => T x) (hf 1)
    simpa only [comp_apply, map_one, one_def, id_apply] using h
  have hL (a : A) : L₀.comp (σ₀ a) = (π.1 a).comp L₀ := by
    ext x
    exact left_intertwines_factorizationSpace π σ W L hf a x x.property
  have hnW : ‖W₀‖ ≤ ‖W‖ := by
    apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    exact W.le_opNorm x
  have hnL : ‖L₀‖ ≤ ‖L‖ := by
    apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    exact L.le_opNorm (x : K)
  obtain ⟨S, hS, hs⟩ := quantitative_similarity_of_surjective_intertwiner
    π σ₀ W₀ L₀ hLW hL
  exact ⟨S, hS.trans (mul_le_mul hnW hnL (norm_nonneg _) (norm_nonneg _)), hs⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorSlices
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vanishing tensor slices in the propagation argument

A bounded weakly null family of vectors gives strongly vanishing slices of
any fixed vector in the completed Hilbert tensor product. This is the density
step in `lem:propagation`, with the uniform bound proved on the completion.
-/

noncomputable section
namespace KadisonSimilarity

open Filter
open scoped Topology TensorProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Bessel's inequality makes every orthonormal sequence weakly null. -/
theorem orthonormal_inner_tendsto_zero (x : ℕ → E) (hx : Orthonormal ℂ x) (a : E) :
    Tendsto (fun n => inner ℂ (x n) a) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := (hx.inner_products_summable (x := a)).tendsto_atTop_zero
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs

theorem norm_algebraTensorSlice_apply_le (x : E) (z : E ⊗[ℂ] F) :
    ‖algebraTensorSlice x z‖ ≤ ‖x‖ * ‖z‖ := by
  change ‖(TensorProduct.lidIsometry ℂ F)
    (TensorProduct.mapL (innerSL ℂ x) (ContinuousLinearMap.id ℂ F) z)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖TensorProduct.mapL (innerSL ℂ x) (ContinuousLinearMap.id ℂ F)‖ * ‖z‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖innerSL ℂ x‖ * ‖ContinuousLinearMap.id ℂ F‖) * ‖z‖ :=
      mul_le_mul_of_nonneg_right (TensorProduct.norm_mapL_le _ _) (norm_nonneg _)
    _ ≤ ‖x‖ * ‖z‖ := by
      rw [innerSL_apply_norm]
      calc
        _ ≤ (‖x‖ * 1) * ‖z‖ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := F))
            (norm_nonneg x)) (norm_nonneg z)
        _ = _ := by ring

variable [CompleteSpace F]

theorem norm_tensorSlice_apply_le (x : E) (z : HilbertTensor E F) :
    ‖tensorSlice x z‖ ≤ ‖x‖ * ‖z‖ := by
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih z =>
    change ‖tensorSlice x (z : HilbertTensor E F)‖ ≤
      ‖x‖ * ‖(z : UniformSpace.Completion (E ⊗[ℂ] F))‖
    rw [tensorSlice_coe, UniformSpace.Completion.norm_coe]
    exact norm_algebraTensorSlice_apply_le x z

omit [CompleteSpace F] in
/-- First prove convergence on finite tensor sums, before taking completion. -/
theorem algebraTensorSlice_tendsto_zero (x : ℕ → E)
    (hweak : ∀ a : E, Tendsto (fun n => inner ℂ (x n) a) atTop (𝓝 0))
    (z : E ⊗[ℂ] F) :
    Tendsto (fun n => algebraTensorSlice (x n) z) atTop (𝓝 0) := by
  induction z using OAI.tensorInductionOn with
  | tmul a b => simpa using (hweak a).smul_const b
  | add a b ha hb => simpa only [map_add, zero_add] using ha.add hb

/-- Weak convergence in the first factor yields norm convergence of each
fixed tensor slice. No uniform rate over tensor vectors is asserted. -/
theorem tensorSlice_tendsto_zero (x : ℕ → E)
    (hbound : ∀ n, ‖x n‖ ≤ 1)
    (hweak : ∀ a : E, Tendsto (fun n => inner ℂ (x n) a) atTop (𝓝 0))
    (z : HilbertTensor E F) :
    Tendsto (fun n => tensorSlice (x n) z) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨w, hw⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt z (half_pos hε)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (algebraTensorSlice_tendsto_zero x hweak w)
    (ε / 2) (half_pos hε)
  let w' : HilbertTensor E F := w
  have hw' : dist z w' < ε / 2 := hw
  refine ⟨N, fun n hn => ?_⟩
  have happrox : ‖tensorSlice (x n) (z - w')‖ < ε / 2 := by
    calc
      _ ≤ ‖x n‖ * ‖z - w'‖ := norm_tensorSlice_apply_le _ _
      _ ≤ ‖z - w'‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (hbound n)
      _ < ε / 2 := by simpa only [dist_eq_norm] using hw'
  have hwN : ‖tensorSlice (x n) w'‖ < ε / 2 := by
    rw [show w' = (w : HilbertTensor E F) from rfl, tensorSlice_coe]
    simpa only [dist_zero_right] using hN n hn
  rw [dist_zero_right]
  calc
    _ ≤ ‖tensorSlice (x n) (z - w')‖ +
        ‖tensorSlice (x n) w'‖ := by
      simpa only [map_sub, sub_add_cancel] using
        norm_add_le (tensorSlice (x n) (z - w')) (tensorSlice (x n) w')
    _ < ε := by linarith

/-- In particular the normalized Haar powers used in propagation give
vanishing slices once their orthonormality has been established. -/
theorem tensorSlice_tendsto_zero_of_orthonormal (x : ℕ → E) (hx : Orthonormal ℂ x)
    (z : HilbertTensor E F) :
    Tendsto (fun n => tensorSlice (x n) z) atTop (𝓝 0) :=
  tensorSlice_tendsto_zero x (fun n => (hx.norm_eq_one n).le)
    (orthonormal_inner_tendsto_zero x hx) z

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_TracialCornerCyclicity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cyclicity of finite tracial corners from dense algebra vectors and
partial-isometry transport. No corner cyclicity or density is assumed. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {C : Type*} [CStarAlgebra C]

/-- A partial isometry transports the corner to one where the range
projection is a cyclic vector. The only corner-algebra data are its concrete
left action and the fact that every compression `eae` is represented. -/
theorem tracial_corner_cyclic_of_partial_isometry
    (G : TracialCornerGeometry P H) (e r : P) (he : IsStarProjection e) (hr : IsStarProjection r)
    (σ : C →⋆ₐ[ℂ] (G.corner e r →L[ℂ] G.corner e r)) (ι : C → P)
    (hfull : ∀ a : P, ∃ c : C, ι c = e * a * e)
    (haction : ∀ (c : C) (x : G.corner e r), (σ c x : H) = G.left (ι c) x)
    (v : P) (hv : star v * v = r) (hev : e * (v * star v) = v * star v) :
    CyclicStarRepresentation σ := by
  let p := v * star v
  have hp : IsStarProjection p := range_projection_of_initial_projection r v hr hv
  let U := G.rightTransfer e r v hv
  let η : G.corner e p := ⟨G.vector p, by
    rw [G.mem_corner]
    constructor
    · rw [G.left_vector, hev]
    · rw [G.right_vector, hp.isIdempotentElem.eq]⟩
  let ζ := U.symm η
  let f : C → G.corner e p := fun c => U (σ c ζ)
  have hf (c : C) : (f c : H) = G.left (ι c) (G.vector p) := by
    change G.right (star v) (σ c ζ) = G.left (ι c) (G.vector p)
    rw [haction]
    have hc := congrArg (fun T : H →L[ℂ] H => T (ζ : H)) (G.right_left (ι c) (star v))
    simp only [ContinuousLinearMap.comp_apply] at hc
    rw [hc]
    have hζ : G.right (star v) ζ = G.vector p :=
      congrArg (fun x : G.corner e p => (x : H)) (U.apply_symm_apply η)
    rw [hζ]
  have hdense : DenseRange f := by
    apply (G.corner_vectors_dense e p he.isIdempotentElem hp.isIdempotentElem).mono
    rintro x ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := hfull a
    refine ⟨c, ?_⟩
    apply Subtype.ext
    rw [hf, TracialCornerGeometry.cornerInto_coe,
      TracialCornerGeometry.cornerProjection_vector, G.left_vector, hc]
    congr 1
    calc
      e * a * e * p = e * a * (e * p) := by noncomm_ring
      _ = e * a * p := by rw [hev]
  refine ⟨ζ, ?_⟩
  have h := U.symm.surjective.denseRange.comp hdense U.symm.continuous
  simpa only [Function.comp_def, f, U.symm_apply_apply] using h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_Propagation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The fixed-prefix limit in propagation from a small corner

On the centered-word subspace the prefix acts isometrically. On the remaining
subspace its norm may be large, but is fixed while the tensor slice tends to
zero. The estimates below carry out that limit without a rate assumption.
-/

noncomputable section
namespace KadisonSimilarity

open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Split a prefix into its isometric centered-word action and the exceptional
projection. The latter incurs only the fixed operator norm. -/
theorem norm_prefix_le (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (A : H →L[ℂ] H)
    (hisometry : ∀ z ∈ Pᗮ, ‖A z‖ = ‖z‖) (z : H) :
    ‖A z‖ ≤ ‖z‖ + ‖A‖ * ‖P.starProjection z‖ := by
  have hsplit : A z = A (z - P.starProjection z) + A (P.starProjection z) := by
    rw [← map_add, sub_add_cancel]
  have hcenter : ‖A (z - P.starProjection z)‖ ≤ ‖z‖ := by
    rw [hisometry _ (P.sub_starProjection_mem_orthogonal z),
      ← P.starProjection_orthogonal_val]
    exact Pᗮ.norm_starProjection_apply_le z
  calc
    _ ≤ ‖A (z - P.starProjection z)‖ + ‖A (P.starProjection z)‖ := by
      rw [hsplit]; exact norm_add_le _ _
    _ ≤ ‖z‖ + ‖A‖ * ‖P.starProjection z‖ :=
      add_le_add hcenter (A.le_opNorm _)

/-- A uniform prefix bound need not be small. It vanishes from the resulting
estimate because it multiplies a sequence converging to zero. -/
theorem propagation_bound_of_vanishing_projection
    (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (A : ℕ → H →L[ℂ] H) (z : ℕ → H)
    (hisometry : ∀ n, ∀ v ∈ Pᗮ, ‖A n v‖ = ‖v‖)
    (L : ℝ) (hL : ∀ n, ‖A n‖ ≤ L)
    (error target : ℝ) (hz : ∀ n, ‖z n‖ ≤ error)
    (hvanish : Tendsto (fun n => P.starProjection (z n)) atTop (𝓝 0))
    (htest : ∀ n, target ≤ error + ‖A n (z n)‖) :
    target ≤ 2 * error := by
  have hupper (n : ℕ) : target ≤ 2 * error + L * ‖P.starProjection (z n)‖ := by
    have hprefix := norm_prefix_le P (A n) (hisometry n) (z n)
    have hnorm := mul_le_mul_of_nonneg_right (hL n) (norm_nonneg (P.starProjection (z n)))
    linarith [htest n, hz n]
  have ht : Tendsto (fun n => 2 * error + L * ‖P.starProjection (z n)‖)
      atTop (𝓝 (2 * error)) := by
    simpa using (hvanish.norm.const_mul L).const_add (2 * error)
  exact ge_of_tendsto ht (Eventually.of_forall hupper)

/-- The scaling identity in the small corner removes its trace from the
propagation error. -/
theorem corner_scaled_error_le {a c ε v y : ℝ} (ha : 0 < a)
    (hy : y ≤ c * ε * Real.sqrt a * v) :
    (Real.sqrt a)⁻¹ * y ≤ c * ε * v := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  calc
    _ ≤ (Real.sqrt a)⁻¹ * (c * ε * Real.sqrt a * v) :=
      mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hs.le)
    _ = c * ε * v := by field_simp

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_PropagationTheorem
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Propagation from a full column through repeated reduced words

Only raw word identities and the elementary tracial operator relations are
supplied below. The error vector, its scaling, the vanishing exceptional
coefficient, and the propagation bound are all derived.
-/

noncomputable section
namespace KadisonSimilarity

open Filter ContinuousLinearMap
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Evaluate the full-column operator norm bound on a vector in that column. -/
theorem column_error_apply_le (G S : H →L[ℂ] H) (M : Submodule ℂ H)
    {η : ℝ} (hcolumn : ‖(G - S).comp M.subtypeL‖ ≤ η) (x : H) (hx : x ∈ M) :
    ‖G x - S x‖ ≤ η * ‖x‖ := by
  have h := ((G - S).comp M.subtypeL).le_opNorm (⟨x, hx⟩ : M)
  exact h.trans (mul_le_mul_of_nonneg_right hcolumn (norm_nonneg x))

/-- The relation `X*X = a⁻¹Q` gives the exact tracial scaling on the range
fixed by `Q`; no smallness assumption on `‖X‖` is used. -/
theorem norm_apply_of_scaled_support (X Q : H →L[ℂ] H) {a : ℝ} (ha : 0 < a)
    (hX : X.adjoint.comp X = ((a⁻¹ : ℝ) : ℂ) • Q) (y : H) (hy : Q y = y) :
    ‖X y‖ = (Real.sqrt a)⁻¹ * ‖y‖ := by
  have hi : inner ℂ (X y) (X y) = ((a⁻¹ : ℝ) : ℂ) * inner ℂ y y := by
    rw [← adjoint_inner_right X y (X y)]
    change inner ℂ y ((X.adjoint.comp X) y) = _
    rw [hX, smul_apply, hy, inner_smul_right]
  have hs : ‖X y‖ ^ 2 = a⁻¹ * ‖y‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), hi]
    change Complex.re (((a⁻¹ : ℝ) : ℂ) * inner ℂ y y) =
      a⁻¹ * Complex.re (inner ℂ y y)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg a))
    (norm_nonneg y))).mp
  rw [hs, mul_pow, inv_pow, Real.sq_sqrt ha.le]

section WordData

variable {B V E F : Type*}
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

namespace RepeatedLetterWords

variable {G : H →L[ℂ] H} {B₀ : B →L[ℂ] B} {Bₖ : V →L[ℂ] V}
  {P : Submodule ℂ H} [P.HasOrthogonalProjection] {a : ℝ}

/-- The exceptional first-coordinate coefficient vanishes on each fixed error
vector. This is a consequence of orthonormality and tensor completion. -/
theorem vacuum_projection_tendsto_zero
    (D : RepeatedLetterWords (E := E) (F := F) G B₀ Bₖ P a) (y : H) :
    Tendsto (fun n => P.starProjection (D.letter n y)) atTop (𝓝 0) := by
  have ht := tensorSlice_tendsto_zero_of_orthonormal D.adjoint_letters
    D.adjoint_letters_orthonormal (D.tensor_coordinates y)
  simpa only [D.vacuum_slice, Function.comp_def, map_zero] using
    (D.vacuum_insert.continuous.tendsto 0).comp ht

/-- The repeated-letter estimate for a vector supported in the full column.
The multiplier commutation hypotheses are the raw left/right action laws. -/
theorem propagation_of_column
    (D : RepeatedLetterWords (E := E) (F := F) G B₀ Bₖ P a) (ha : 0 < a)
    (M : Submodule ℂ H) (S : H →L[ℂ] H) {η : ℝ}
    (hcolumn : ‖(G - S).comp M.subtypeL‖ ≤ η)
    (hSsupport : D.support.comp S = S.comp D.support)
    (hSletter : ∀ n, S.comp (D.letter n) = (D.letter n).comp S)
    (hSprefix : ∀ n, S.comp (D.wordPrefix n) = (D.wordPrefix n).comp S)
    (hMletter : ∀ n z, z ∈ M → D.letter n z ∈ M)
    (hMprefix : ∀ n z, z ∈ M → D.wordPrefix n z ∈ M)
    (v : B) (hv : D.small v ∈ M) :
    ‖Bₖ (D.repeatVector v) - D.repeatVector (B₀ v)‖ ≤ 2 * η * ‖v‖ := by
  let y := S (D.small v) - D.small (B₀ v)
  have hy : ‖y‖ ≤ η * Real.sqrt a * ‖v‖ := by
    calc
      ‖y‖ = ‖G (D.small v) - S (D.small v)‖ := by
        dsimp [y]
        rw [D.level_zero, norm_sub_rev]
      _ ≤ η * ‖D.small v‖ := column_error_apply_le G S M hcolumn _ hv
      _ = η * Real.sqrt a * ‖v‖ := by rw [D.small_norm]; ring
  have hQy : D.support y = y := by
    have hc := congrArg (fun T : H →L[ℂ] H => T (D.small v)) hSsupport
    simp only [comp_apply, D.support_small] at hc
    simpa only [y, map_sub, D.support_small] using congrArg (fun z => z - D.small (B₀ v)) hc
  have hz (n : ℕ) : ‖D.letter n y‖ ≤ η * ‖v‖ := by
    rw [norm_apply_of_scaled_support (D.letter n) D.support ha (D.letter_scale n) y hQy]
    have h := corner_scaled_error_le (c := η) (ε := 1) (v := ‖v‖) ha
      (show ‖y‖ ≤ η * 1 * Real.sqrt a * ‖v‖ by simpa using hy)
    simpa using h
  have hword_mem (n : ℕ) : D.word n (D.repeatVector v) ∈ M := by
    rw [D.word_factor]
    exact hMprefix n _ (hMletter n _ hv)
  have hword_error (n : ℕ) :
      ‖G (D.word n (D.repeatVector v)) - S (D.word n (D.repeatVector v))‖ ≤ η * ‖v‖ := by
    simpa only [LinearIsometry.norm_map] using
      column_error_apply_le G S M hcolumn _ (hword_mem n)
  have hSletter_apply (n : ℕ) (z : H) : S (D.letter n z) = D.letter n (S z) :=
    congrArg (fun T : H →L[ℂ] H => T z) (hSletter n)
  have hSprefix_apply (n : ℕ) (z : H) : S (D.wordPrefix n z) = D.wordPrefix n (S z) :=
    congrArg (fun T : H →L[ℂ] H => T z) (hSprefix n)
  have hid (n : ℕ) :
      S (D.word n (D.repeatVector v)) - D.word n (D.repeatVector (B₀ v)) =
        D.wordPrefix n (D.letter n y) := by
    simp only [D.word_factor, hSprefix_apply, hSletter_apply, y, map_sub]
  have htest (n : ℕ) : ‖Bₖ (D.repeatVector v) - D.repeatVector (B₀ v)‖ ≤
      η * ‖v‖ + ‖D.wordPrefix n (D.letter n y)‖ := by
    calc
      _ = ‖G (D.word n (D.repeatVector v)) - D.word n (D.repeatVector (B₀ v))‖ := by
        rw [D.level_repeated, ← map_sub, LinearIsometry.norm_map]
      _ ≤ ‖G (D.word n (D.repeatVector v)) - S (D.word n (D.repeatVector v))‖ +
          ‖S (D.word n (D.repeatVector v)) - D.word n (D.repeatVector (B₀ v))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ η * ‖v‖ + ‖D.wordPrefix n (D.letter n y)‖ := by
        rw [hid]
        exact add_le_add (hword_error n) le_rfl
  have hfinal := propagation_bound_of_vanishing_projection P D.wordPrefix
    (fun n => D.letter n y) D.prefix_isometry D.prefix_bound D.prefix_bound_le
    (η * ‖v‖) ‖Bₖ (D.repeatVector v) - D.repeatVector (B₀ v)‖ hz
    (D.vacuum_projection_tendsto_zero y) htest
  simpa only [mul_assoc] using hfinal

end RepeatedLetterWords

end WordData
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_PaulsenDischarge
attribute [-instance] _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.boundedHomOrbit_apply _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.listOrbitSum_append _root_.OAI.KadisonSimilarity.listOrbitSum_nil _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.sharpHom_apply _root_.OAI.KadisonSimilarity.sharpVectorMap_apply _root_.OAI.KadisonSimilarity.similarityRepresentation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative similarity from the proved completely bounded factorization

The entrywise C-star matrix norm agrees with the concrete matrix operator
norm. Applying the proved factorization and then removing its kernel gives
Paulsen's quantitative similarity conclusion on the original Hilbert space.
-/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem completeBound_entrywise (π : BoundedUnitalHom A H) {C : ℝ}
    (hπ : CompleteBound π.1 C) (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖X.map π.1.toLinearMap‖ ≤ C * ‖X‖ := by
  have h := hπ n (CStarMatrix.ofMatrix.symm X)
  change ‖matrixOperator (CStarMatrix.ofMatrix.symm (X.map π.1.toLinearMap))‖ ≤ C * ‖X‖ at h
  rwa [norm_matrixOperator_eq] at h

/-- Paulsen's quantitative similarity bound, including the zero Hilbert space. -/
theorem paulsenSimilarityInput (π : BoundedUnitalHom A H) : PaulsenSimilarityInput π := by
  intro C hC hπ
  rcases subsingleton_or_nontrivial H with hH | hH
  · let := hH
    refine ⟨1, ?_, fun _ => Subsingleton.elim _ _⟩
    have hnorm : ‖(1 : H →L[ℂ] H)‖ = 0 := by
      rw [Subsingleton.elim (1 : H →L[ℂ] H) 0, norm_zero]
    simpa only [inv_one, Units.val_one, hnorm, zero_mul] using hC
  · let := hH
    have h01 : (0 : A) ≠ 1 := by
      intro h
      have he := congrArg π.1 h
      have hz : (0 : H →L[ℂ] H) = 1 := by
        simpa only [map_zero, map_one] using he
      exact zero_ne_one hz
    let : Nontrivial A := ⟨⟨0, 1, h01⟩⟩
    have hm : (1 : CStarMatrix (Fin 1) (Fin 1) A).map π.1.toLinearMap = 1 := by
      ext i j
      fin_cases i
      fin_cases j
      simp
    have hc := completeBound_entrywise π hπ 1 1
    rw [hm, CStarRing.norm_one, CStarRing.norm_one, mul_one] at hc
    have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hc
    obtain ⟨F⟩ := BoundedHochschild.KadisonRingrose.factorization_of_complete_bound
      π.1.toLinearMap hCpos (completeBound_entrywise π hπ)
    obtain ⟨S, hS, hs⟩ := quantitative_similarity_of_factorization
      π F.representation F.rightMap F.leftMap.adjoint (fun a => (F.factorization a).symm)
    refine ⟨S, hS.trans ?_, hs⟩
    simpa only [ContinuousLinearMap.adjoint.norm_map, mul_comm] using F.bound

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CStarCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual unital C-star algebra cut out by a projection. Its identity
is the projection, and its norm is the ambient norm. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

namespace CStarCorner

variable (e : P) (he : IsStarProjection e)

theorem full : ∀ a : P, ∃ c : CStarCorner e he, (c : P) = e * a * e :=
  fun a => ⟨compress e he a, rfl⟩

end CStarCorner
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCornerRepresentations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerAlgebra _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerAlgebra _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual corner representations on the completed tracial Hilbert corners. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (e : P) (he : IsStarProjection e) (r : P)

theorem corner_adjoint_intertwines (a : CStarCorner e he) :
    (G.corner e r).toSubmodule.subtypeL.adjoint.comp (G.left (a : P)) =
      (G.cornerRepresentation e he r a).comp (G.corner e r).toSubmodule.subtypeL.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint (G.corner_inclusion_intertwines e he r (star a))
  have hL : G.left ((star a : CStarCorner e he) : P) = (G.left (a : P)).adjoint := by
    change G.left (star (a : P)) = _
    rw [map_star, ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.adjoint_comp, hL, ContinuousLinearMap.adjoint_adjoint] at h
  simpa only [ContinuousLinearMap.adjoint_comp, map_star,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] using h

/-- The geometric cyclicity result now applies to the actual algebra `ePe`
and its actual left representation, with no abstract-coordinate hypotheses. -/
theorem cornerRepresentation_cyclic (hr : IsStarProjection r) (v : P)
    (hv : star v * v = r) (hev : e * (v * star v) = v * star v) :
    CyclicStarRepresentation (G.cornerRepresentation e he r) :=
  tracial_corner_cyclic_of_partial_isometry G e r he hr
    (G.cornerRepresentation e he r) Subtype.val (CStarCorner.full e he)
    (fun _ _ => rfl) v hv hev

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialSupportedColumns
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseAlgebraVectors_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseCompression_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_left_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_vector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator_adjoint _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.homIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_other _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionUnitaryRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.mem_l2ClosureAlgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.oppositeGeometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.positiveTrace_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.gnsTracialGeometry_left _root_.OAI.KadisonSimilarity.gnsTracialGeometry_trace _root_.OAI.KadisonSimilarity.gnsTracialGeometry_vector _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Support projections and represented right columns in a concrete tracial
Hilbert space. These are the ambient spaces used by the full-column lemma. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H)

theorem rightColumn_inclusion_intertwines (r a : P) :
    (G.left a).comp (G.corner 1 r).toSubmodule.subtypeL =
      (G.corner 1 r).toSubmodule.subtypeL.comp (G.rightColumnRepresentation r a) := rfl

/-- The adjoint of the inclusion is the right support projection and is a
left-module map; this supplies the projection data of the full-column lemma. -/
theorem rightColumn_projection (r : P) (hr : IsStarProjection r) :
    (G.corner 1 r).toSubmodule.subtypeL.comp
      (G.corner 1 r).toSubmodule.subtypeL.adjoint = G.right r := by
  rw [G.corner_inclusion_adjoint 1 r (IsStarProjection.one P) hr]
  simp [cornerProjection, ContinuousLinearMap.one_def]

theorem rightColumn_adjoint_intertwines (r a : P) :
    (G.corner 1 r).toSubmodule.subtypeL.adjoint.comp (G.left a) =
      (G.rightColumnRepresentation r a).comp (G.corner 1 r).toSubmodule.subtypeL.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint (G.rightColumn_inclusion_intertwines r (star a))
  simpa only [ContinuousLinearMap.adjoint_comp, map_star,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] using h

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCornerEstimate
attribute [-instance] _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.CStarCorner.mem_subalgebra _root_.OAI.KadisonSimilarity.CStarCorner.normalizedTrace_apply _root_.OAI.KadisonSimilarity.DihedralSpectralArc.corner_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseAlgebraVectors_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseCompression_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_left_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_vector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator_adjoint _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.homIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_other _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionUnitaryRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.mem_l2ClosureAlgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.oppositeGeometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.positiveTrace_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe _root_.OAI.KadisonSimilarity.cornerStarAlgHom_coe _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.globalRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.globalRestrictionFiberEquiv_symm_coe _root_.OAI.KadisonSimilarity.gnsTracialGeometry_left _root_.OAI.KadisonSimilarity.gnsTracialGeometry_trace _root_.OAI.KadisonSimilarity.gnsTracialGeometry_vector _root_.OAI.KadisonSimilarity.haarCornerLetter_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_mul _root_.OAI.KadisonSimilarity.haarCornerPower_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_zero _root_.OAI.KadisonSimilarity.invariantStarRepresentation_apply _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.mul_haarCornerPower _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.nonunitalRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.nonunitalRestrictionFiberEquiv_symm_coe _root_.OAI.KadisonSimilarity.projectionFiberAction_coe _root_.OAI.KadisonSimilarity.projectionFiberCompression_coe _root_.OAI.KadisonSimilarity.projectionFiberEquivOfEq_coe _root_.OAI.KadisonSimilarity.projectionFiberRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_inclusion _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.star_haarCornerLetter _root_.OAI.KadisonSimilarity.star_haarCornerPower _root_.OAI.KadisonSimilarity.support_mul_haarCornerLetter _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.unitizationRangeRepresentation_coe _root_.OAI.KadisonSimilarity.unitizationRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.unitizationRestrictionFiberEquiv_symm_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small-corner commutator estimate supplies the actual bounded
rectangular derivation used in the full-column argument. -/

noncomputable section
namespace KadisonSimilarity

open scoped CStarAlgebra

universe u v
variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (e : P) (he : IsStarProjection e) (r : P)

theorem cornerRestriction_commutator (Y : H →L[ℂ] H) (a : CStarCorner e he) :
    cornerCommutator (G.cornerRepresentation e he 1) (G.cornerRepresentation e he r)
      (G.cornerRestriction e r Y) a =
      (G.corner e 1).toSubmodule.subtypeL.adjoint.comp
        ((commutator Y (G.left (a : P))).comp (G.corner e r).toSubmodule.subtypeL) := by
  simp only [cornerCommutator_apply, cornerRestriction, commutator,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_assoc]
  rw [← G.corner_inclusion_intertwines e he r a]
  rw [← ContinuousLinearMap.comp_assoc (G.cornerRepresentation e he 1 a),
    ← G.corner_adjoint_intertwines e he 1 a]
  simp only [ContinuousLinearMap.comp_assoc]

/-- The rectangular derivation has norm at most the original small-corner
constant. Orthogonal domain/output compression introduces no dimension factor. -/
theorem norm_cornerRestriction_commutator_le (Y : H →L[ℂ] H) {ε : ℝ} (hε : 0 ≤ ε)
    (hY : ∀ a : CStarCorner e he, ‖commutator Y (G.left (a : P))‖ ≤ ε * ‖a‖) :
    ‖cornerCommutator (G.cornerRepresentation e he 1) (G.cornerRepresentation e he r)
      (G.cornerRestriction e r Y)‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro a
  rw [G.cornerRestriction_commutator e he r Y a]
  calc
    _ ≤ ‖(G.corner e 1).toSubmodule.subtypeL.adjoint‖ *
        (‖commutator Y (G.left (a : P))‖ * ‖(G.corner e r).toSubmodule.subtypeL‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * ((ε * ‖a‖) * 1) := by
      gcongr
      · simpa using (G.corner e 1).toSubmodule.norm_subtypeL_le
      · exact hY a
      · exact (G.corner e r).toSubmodule.norm_subtypeL_le
    _ = ε * ‖a‖ := by ring

/-- The corrected corner intertwiner is obtained with the paper's constant
from projection comparison and the exact published cyclic inputs. -/
theorem exists_corrected_corner
    (τ : P → ℝ) (comparison : FiniteFactorProjectionComparison τ)
    (hr : IsStarProjection r) (hτ : τ r ≤ τ e)
    (Y : H →L[ℂ] H) {ε : ℝ} (hε : 0 ≤ ε)
    (hY : ∀ a : CStarCorner e he, ‖commutator Y (G.left (a : P))‖ ≤ ε * ‖a‖)
    (published : PublishedDerivationInputs.{u,v} (CStarCorner e he)) :
    ∃ T : G.corner e r →L[ℂ] G.corner e 1,
      (∀ a : CStarCorner e he, T.comp (G.cornerRepresentation e he r a) =
        (G.cornerRepresentation e he 1 a).comp T) ∧
      ‖G.cornerRestriction e r Y - T‖ ≤ (1 + 4 * (4 * Real.sqrt 2)) ^ 2 * ε := by
  obtain ⟨v, hv, hev⟩ := comparison e r he hr hτ
  let ρ := G.cornerRepresentation e he 1
  let σ := G.cornerRepresentation e he r
  let Ye := G.cornerRestriction e r Y
  exact exists_corner_intertwiner_of_column_tests ρ σ Ye
    (G.norm_cornerRestriction_commutator_le e he r Y hε hY)
    (published.columns (G.corner e r) σ (G.cornerRepresentation_cyclic e he r hr v hv hev))
    (paulsenSimilarityInput
      (normalizedRectangularRepresentation ρ σ (cornerCommutator ρ σ Ye)
        (cornerCommutator_leibniz ρ σ Ye)))

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConcreteFullColumn
attribute [-instance] _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.hilbertArrayFlatten_apply _root_.OAI.KadisonSimilarity.hilbertFourfoldFlatten_apply _root_.OAI.KadisonSimilarity.hilbertTripleFlatten_apply _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.matrixLeftArray_apply _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full-column estimate in the concrete tracial Hilbert space. -/

noncomputable section
namespace KadisonSimilarity

section Coordinates
variable {P C H D F K : Type*} [CStarAlgebra P] [CStarAlgebra C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace F] [CompleteSpace K] in
private theorem mapCopies_single (T : K →L[ℂ] F) {n : ℕ} (i : Fin n) (x : K) :
    mapCopies T n (PiLp.single 2 i x) = PiLp.single 2 i (T x) := by
  ext j
  simp only [mapCopies_apply, PiLp.single_apply]
  split_ifs <;> simp

/-- Diagonal extension agrees with the given corner map on every column. -/
theorem extend_column
    (L : P →⋆ₐ[ℂ] (H →L[ℂ] H)) (Lr : P →⋆ₐ[ℂ] (D →L[ℂ] D))
    (ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K))
    {n : ℕ} (U : FiniteOrthogonalColumns F H n) (V : FiniteOrthogonalColumns K D n)
    (entry : P → Matrix (Fin n) (Fin n) C)
    (hU : ∀ a i j, ρ (entry a i j) =
      (U.inclusion i).adjoint.comp ((L a).comp (U.inclusion j)))
    (hV : ∀ a i j, σ (entry a i j) =
      (V.inclusion i).adjoint.comp ((Lr a).comp (V.inclusion j)))
    (T : K →L[ℂ] F) (i : Fin n) (x : K) :
    (fullColumnCoordinatesOfColumns L Lr ρ σ U V entry hU hV).extend T
      (V.inclusion i x) = U.inclusion i (T x) := by
  change U.unitary (mapCopies T n (V.unitary.symm (V.inclusion i x))) = _
  rw [← V.unitary_single, V.unitary.symm_apply_apply, mapCopies_single,
    U.unitary_single]

omit [CompleteSpace H] in
/-- Equality on a complete finite family of columns determines an operator. -/
theorem FiniteOrthogonalColumns.ext_on_columns {n : ℕ}
    (V : FiniteOrthogonalColumns K D n) (S T : D →L[ℂ] H)
    (h : ∀ i x, S (V.inclusion i x) = T (V.inclusion i x)) : S = T := by
  ext x
  obtain ⟨z, rfl⟩ := V.unitary.surjective x
  simp only [FiniteOrthogonalColumns.unitary_apply, sumColumns_apply, map_sum, h]

end Coordinates

universe u v
variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry
variable (G : TracialCornerGeometry P H) (e : P) (he : IsStarProjection e) (r : P)

include he in
/-- Commutation with the left corner projection makes output compression exact. -/
theorem inclusion_cornerRestriction (Y : H →L[ℂ] H)
    (hYe : Y.comp (G.left e) = (G.left e).comp Y) (x : G.corner e r) :
    ((G.cornerRestriction e r Y x : G.corner e 1) : H) = Y (x : H) := by
  change ((G.corner e 1).toSubmodule.subtypeL.comp
    (G.corner e 1).toSubmodule.subtypeL.adjoint) (Y (x : H)) = _
  rw [G.corner_inclusion_adjoint e 1 he (IsStarProjection.one P),
    cornerProjection, G.right_one, ContinuousLinearMap.comp_id]
  have h := congrArg (fun T : H →L[ℂ] H => T (x : H)) hYe
  simpa only [ContinuousLinearMap.comp_apply, ((G.mem_corner e r x).mp x.property).1]
    using h.symm

/-- Matrix commutation extends the actual compressed operator to the full column. -/
theorem extend_cornerRestriction (hr : IsStarProjection r) {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (hsum : ∑ i, v i * star (v i) = 1)
    (Y : H →L[ℂ] H) (hYe : Y.comp (G.left e) = (G.left e).comp Y)
    (hYv : ∀ i, Y.comp (G.left (v i)) = (G.left (v i)).comp Y) :
    (G.fullColumnCoordinates e he r hr v hv hsum).extend
      (G.cornerRestriction e r Y) = Y.comp (G.corner 1 r).toSubmodule.subtypeL := by
  apply (G.supportedCornerColumns e he r hr v hv hsum).ext_on_columns
  intro i x
  have hc := extend_column G.left (G.rightColumnRepresentation r)
    (G.cornerRepresentation e he 1) (G.cornerRepresentation e he r)
    (G.ambientCornerColumns e he v hv hsum)
    (G.supportedCornerColumns e he r hr v hv hsum)
    (cornerMatrixEntry e he v hv)
    (G.ambientCornerColumns_entry e he v hv hsum)
    (G.supportedCornerColumns_entry e he r hr v hv hsum)
    (G.cornerRestriction e r Y) i x
  refine hc.trans ?_
  change G.left (v i) ((G.cornerRestriction e r Y x : G.corner e 1) : H) =
    Y (G.left (v i) (x : H))
  rw [G.inclusion_cornerRestriction e he r Y hYe]
  exact (congrArg (fun T : H →L[ℂ] H => T (x : H)) (hYv i)).symm

/-- The paper's full-column conclusion, with all corner representations and
matrix coordinates constructed from the tracial geometry. Its only analytic
inputs are the explicitly cited cyclic results and tracial commutation. -/
theorem full_column
    (hfaithful : Function.Injective G.vector)
    (τ : P → ℝ) (comparison : FiniteFactorProjectionComparison τ)
    (hr : IsStarProjection r) (hτ : τ r ≤ τ e)
    {n : ℕ} (hn : 0 < n) (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (hsum : ∑ i, v i * star (v i) = 1)
    (Y : H →L[ℂ] H) (hYe : Y.comp (G.left e) = (G.left e).comp Y)
    (hYv : ∀ i, Y.comp (G.left (v i)) = (G.left (v i)).comp Y)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hY : ∀ a : CStarCorner e he, ‖commutator Y (G.left (a : P))‖ ≤ ε * ‖a‖)
    (published : PublishedDerivationInputs.{u,v} (CStarCorner e he))
    (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful)) :
    ∃ b : P, r * b = b ∧
      ‖(Y - G.right b).comp (G.corner 1 r).toSubmodule.subtypeL‖ ≤
        (1 + 4 * (4 * Real.sqrt 2)) ^ 2 * ε := by
  obtain ⟨T, hT, hnorm⟩ := G.exists_corrected_corner e he r τ comparison hr hτ
    Y hε hY published
  let c := G.fullColumnCoordinates e he r hr v hv hsum
  have hpr : (G.corner 1 r).toSubmodule.subtypeL.adjoint.comp
      (G.corner 1 r).toSubmodule.subtypeL = ContinuousLinearMap.id ℂ (G.corner 1 r) := by
    have hI : (G.corner 1 r).toSubmodule.subtypeL.adjoint.comp
        (G.corner 1 r).toSubmodule.subtypeL = 1 :=
      (G.corner 1 r).toSubmodule.subtypeₗᵢ.adjoint_comp_self
    change _ = 1
    exact hI
  obtain ⟨b, hb, hTb⟩ := exists_supported_right_multiplier G.left
    (G.rightColumnRepresentation r) (G.faithfulRightAction hfaithful) r
    (G.corner 1 r).toSubmodule.subtypeL (G.corner 1 r).toSubmodule.subtypeL.adjoint
    hpr (G.rightColumn_projection r hr) (G.rightColumn_adjoint_intertwines r)
    commutation (c.extend T) (c.extend_intertwines T hT)
  refine ⟨b, hb, ?_⟩
  change ‖(Y - (G.faithfulRightAction hfaithful).right b).comp _‖ ≤ _
  rw [ContinuousLinearMap.sub_comp, hTb,
    ← G.extend_cornerRestriction e he r hr v hv hsum Y hYe hYv]
  exact (c.norm_extend_sub hn _ _).le.trans hnorm

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialPropagation
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Propagation through actual left multipliers on a tracial Hilbert space.
The full-column approximation is derived from the concrete corner theorem;
the remaining hypotheses describe the repeated words and their tensor geometry. -/

noncomputable section
namespace KadisonSimilarity

universe u v wB wV wE wF

variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {B : Type wB} {V : Type wV} {E : Type wE} {F : Type wF}
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Y : H →L[ℂ] H} {B₀ : B →L[ℂ] B} {Bₖ : V →L[ℂ] V}
  {Q : Submodule ℂ H} [Q.HasOrthogonalProjection] {t : ℝ}

namespace RepeatedLetterWords

variable (D : RepeatedLetterWords (E := E) (F := F) Y B₀ Bₖ Q t)
  (G : TracialCornerGeometry P H)

/-- A word support represented by left multiplication commutes with every
right multiplier, directly from the tracial representation. -/
theorem tracial_support_commutes (q : P) (hsupport : D.support = G.left q) (b : P) :
    D.support.comp (G.right b) = (G.right b).comp D.support := by
  rw [hsupport]
  exact (G.right_left q b).symm

/-- The tracial left/right action law gives the letter commutation needed by
propagation. -/
theorem tracial_letter_commutes (x : ℕ → P)
    (hletter : ∀ n, D.letter n = G.left (x n)) (b : P) (n : ℕ) :
    (G.right b).comp (D.letter n) = (D.letter n).comp (G.right b) := by
  rw [hletter]
  exact G.right_left (x n) b

/-- Prefix multiplication obeys the same left/right action law. -/
theorem tracial_prefix_commutes (a : ℕ → P)
    (hprefix : ∀ n, D.wordPrefix n = G.left (a n)) (b : P) (n : ℕ) :
    (G.right b).comp (D.wordPrefix n) = (D.wordPrefix n).comp (G.right b) := by
  rw [hprefix]
  exact G.right_left (a n) b

/-- An actual left letter preserves the complete right-supported column. -/
theorem tracial_letter_mem (r : P) (x : ℕ → P)
    (hletter : ∀ n, D.letter n = G.left (x n)) (n : ℕ) (z : H)
    (hz : z ∈ (G.corner 1 r).toSubmodule) :
    D.letter n z ∈ (G.corner 1 r).toSubmodule := by
  rw [hletter]
  exact G.rightColumn_mem r (x n) z hz

/-- An actual left prefix preserves the same column. -/
theorem tracial_prefix_mem (r : P) (a : ℕ → P)
    (hprefix : ∀ n, D.wordPrefix n = G.left (a n)) (n : ℕ) (z : H)
    (hz : z ∈ (G.corner 1 r).toSubmodule) :
    D.wordPrefix n z ∈ (G.corner 1 r).toSubmodule := by
  rw [hprefix]
  exact G.rightColumn_mem r (a n) z hz

/-- The concrete tracial action discharges all multiplier commutation and
column-preservation hypotheses in the abstract propagation theorem. -/
theorem propagation_of_tracial_column (ht : 0 < t)
    (q r : P) (x a : ℕ → P)
    (hsupport : D.support = G.left q)
    (hletter : ∀ n, D.letter n = G.left (x n))
    (hprefix : ∀ n, D.wordPrefix n = G.left (a n))
    (b : P) {η : ℝ}
    (hcolumn : ‖(Y - G.right b).comp (G.corner 1 r).toSubmodule.subtypeL‖ ≤ η)
    (v : B) (hv : D.small v ∈ (G.corner 1 r).toSubmodule) :
    ‖Bₖ (D.repeatVector v) - D.repeatVector (B₀ v)‖ ≤ 2 * η * ‖v‖ := by
  exact D.propagation_of_column ht (G.corner 1 r).toSubmodule (G.right b) hcolumn
    (D.tracial_support_commutes G q hsupport b)
    (D.tracial_letter_commutes G x hletter b)
    (D.tracial_prefix_commutes G a hprefix b)
    (D.tracial_letter_mem G r x hletter)
    (D.tracial_prefix_mem G r a hprefix) v hv

end RepeatedLetterWords

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialRepeatedWords
attribute [-instance] _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Realize the abstract propagation data by actual tracial left multipliers.
The remaining word data are elementary reduced-word multiplication and
isometry identities; the scaled support and vanishing coefficient are proved. -/

noncomputable section
namespace KadisonSimilarity

variable {D P E H F B V : Type*} [CStarAlgebra D] [CStarAlgebra P]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

variable {GD : TracialCornerGeometry D E} {G : TracialCornerGeometry P H}
  {ι : D →⋆ₐ[ℂ] P} (W : TracialHeadCoordinates GD G ι F)
  [W.vacuum.HasOrthogonalProjection]
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq)) (a : ℝ)
  (Y : H →L[ℂ] H) (B₀ : B →L[ℂ] B) (Bₖ : V →L[ℂ] V)

namespace TracialRepeatedWordRealization

variable {W z a Y B₀ Bₖ}
  (R : TracialRepeatedWordRealization W z a Y B₀ Bₖ)

/-- A supported column approximation propagates to the repeated word with
factor two. All action-commutation and exceptional-limit requirements have
been discharged in the tracial model. -/
theorem propagation (hτ : GD.trace 1 = 1) (ha : 0 < a)
    (htrace : GD.trace q = (a : ℂ)) (hhaar : HaarCornerMoments GD.trace z a)
    (r b : P) {η : ℝ}
    (hcolumn : ‖(Y - G.right b).comp (G.corner 1 r).toSubmodule.subtypeL‖ ≤ η)
    (v : B) (hv : R.small v ∈ (G.corner 1 r).toSubmodule) :
    ‖Bₖ (R.repeatVector v) - R.repeatVector (B₀ v)‖ ≤ 2 * η * ‖v‖ := by
  let Q := R.propagationData hτ ha htrace hhaar
  exact Q.propagation_of_tracial_column G ha (ι q) r
    (fun n => ι (haarCornerLetter z a n)) R.prefixElement rfl (fun _ => rfl) (fun _ => rfl)
    b hcolumn v hv

end TracialRepeatedWordRealization
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialPropagationEndgame
attribute [-instance] _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Propagation on the entire base Hilbert space. Polar decomposition is used
only for the right support of the bounded vector qv; density handles all other
base vectors. The full-column bound is derived from the cited cyclic inputs. -/

noncomputable section
namespace KadisonSimilarity

universe u v
variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {D E F V : Type*} [CStarAlgebra D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {GD : TracialCornerGeometry D E} {G : TracialCornerGeometry P H}
  {ι : D →⋆ₐ[ℂ] P} {W : TracialHeadCoordinates GD G ι F}
  [W.vacuum.HasOrthogonalProjection]
  {q : D} {hq : IsStarProjection q} {z : unitary (CStarCorner q hq)} {a : ℝ}
  {Y : H →L[ℂ] H} {A : StarSubalgebra ℂ P}
  {B₀ : G.baseSpace A →L[ℂ] G.baseSpace A} {Bₖ : V →L[ℂ] V}

namespace TracialRepeatedWordRealization

/-- A supported full-column estimate on each bounded base vector propagates
to every vector of the actual closed base space. The support may depend on v. -/
theorem propagation_on_base
    (R : TracialRepeatedWordRealization W z a Y B₀ Bₖ)
    (hτ : GD.trace 1 = 1) (ha : 0 < a)
    (htrace : GD.trace q = (a : ℂ)) (hhaar : HaarCornerMoments GD.trace z a)
    (τ : P → ℝ) (support : TracialRightSupportInput τ (ι q) A)
    (hsmall : ∀ v : A, R.small (G.baseVector A v) = G.vector (ι q * (v : P)))
    {η : ℝ}
    (hcolumn : ∀ r : P, IsStarProjection r → τ r ≤ τ (ι q) →
      ∃ b : P, r * b = b ∧
        ‖(Y - G.right b).comp (G.corner 1 r).toSubmodule.subtypeL‖ ≤ η)
    (v : G.baseSpace A) :
    ‖Bₖ (R.repeatVector v) - R.repeatVector (B₀ v)‖ ≤ 2 * η * ‖v‖ := by
  refine (G.baseVector_dense A).induction_on v (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro v
  obtain ⟨r, hr, htr, hvr⟩ := support v
  obtain ⟨b, _, hb⟩ := hcolumn r hr htr
  have hv : R.small (G.baseVector A v) ∈ (G.corner 1 r).toSubmodule := by
    rw [hsmall]
    change G.vector (ι q * (v : P)) ∈ G.corner 1 r
    rw [G.mem_corner]
    exact ⟨by simp, by simp only [G.right_vector, hvr]⟩
  exact R.propagation hτ ha htrace hhaar r b hb _ hv

/-- All full-column assumptions are discharged using the actual matrix frame
and published cyclic implementation and tracial commutation inputs. -/
theorem propagation_on_base_of_published_inputs_oai
    (R : TracialRepeatedWordRealization W z a Y B₀ Bₖ)
    (hτ : GD.trace 1 = 1) (ha : 0 < a)
    (htrace : GD.trace q = (a : ℂ)) (hhaar : HaarCornerMoments GD.trace z a)
    (τ : P → ℝ) (support : TracialRightSupportInput τ (ι q) A)
    (hsmall : ∀ v : A, R.small (G.baseVector A v) = G.vector (ι q * (v : P)))
    (e : P) (he : IsStarProjection e) (hqe : τ (ι q) ≤ τ e)
    (hfaithful : Function.Injective G.vector)
    (comparison : FiniteFactorProjectionComparison τ)
    {n : ℕ} (hn : 0 < n) (frame : Fin n → P)
    (hframe : ∀ i j, star (frame i) * frame j = if i = j then e else 0)
    (hsum : ∑ i, frame i * star (frame i) = 1)
    (hYe : Y.comp (G.left e) = (G.left e).comp Y)
    (hYframe : ∀ i, Y.comp (G.left (frame i)) = (G.left (frame i)).comp Y)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hY : ∀ x : CStarCorner e he, ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖)
    (published : PublishedDerivationInputs.{u,v} (CStarCorner e he))
    (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
    (v : G.baseSpace A) :
    ‖Bₖ (R.repeatVector v) - R.repeatVector (B₀ v)‖ ≤
      2 * cyclicConstant * ε * ‖v‖ := by
  have hp := R.propagation_on_base hτ ha htrace hhaar τ support hsmall
    (fun r hr htr => G.full_column e he r hfaithful τ comparison hr (htr.trans hqe)
      hn frame hframe hsum Y hYe hYframe hε hY published commutation) v
  simpa only [cyclicConstant, rowConstant, mul_assoc] using hp

end TracialRepeatedWordRealization
end KadisonSimilarity

end

end OAI
end

theorem solution.{u, v, u_1, u_2, u_3, u_4} : type_of% @OAI.KadisonSimilarity.TracialRepeatedWordRealization.propagation_on_base_of_published_inputs_oai.{u, v, u_1, u_2, u_3, u_4} := @OAI.KadisonSimilarity.TracialRepeatedWordRealization.propagation_on_base_of_published_inputs_oai.{u, v, u_1, u_2, u_3, u_4}
