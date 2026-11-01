-- Prove2me | solution 1 for OAI.KadisonSimilarity.similarityTheorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T14:47:28.083589+00:00
-- url     : https://prove2.me/submissions/7c9fe1a3-cc8b-4201-a4e7-0c74a2e86d1e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A018
import Definitions.Def_OAIQ075A025
import Definitions.Def_OAIQ075A028
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_factorization_of_complete_bound
import Theorems.Thm_OAI_KadisonSimilarity_list_equal_square_orbit_comparison
import Theorems.Thm_OAI_KadisonSimilarity_uniformCommutatorEstimate

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Constants
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical constants fixed by the manuscript. -/

noncomputable section

namespace KadisonSimilarity

theorem two_le_factorConstant : 2 ≤ factorConstant := le_max_right _ _

theorem factorConstant_pos : 0 < factorConstant := lt_of_lt_of_le (by norm_num) two_le_factorConstant

theorem universalConstant_pos : 0 < universalConstant := by
  unfold universalConstant
  linarith [factorConstant_pos]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_Amplification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.hilbertArrayFlatten_apply _root_.OAI.KadisonSimilarity.hilbertFourfoldFlatten_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.hilbertTripleFlatten_apply _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_matrixOperator _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.matrixLeftArray_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_apply _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_zero _root_.OAI.KadisonSimilarity.representedDoubleMatrix_apply _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.KadisonSimilarity.vonNeumannInnerDerivation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix amplification and the main statements

Matrices act on finite Hilbert sums with their `ℓ²` norm. Consequently the
norm in `CommutatorEstimate` is the concrete operator matrix norm, rather than
the coordinatewise supremum norm of a matrix. No main estimate is assumed here.
-/

noncomputable section

universe u v

namespace KadisonSimilarity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Hilbert amplification does not increase the operator norm. -/
theorem norm_amplify_le (Y : H →L[ℂ] H) (n : ℕ) : ‖amplify Y n‖ ≤ ‖Y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Y)
  intro ξ
  have hs : ‖amplify Y n ξ‖ ^ 2 ≤ (‖Y‖ * ‖ξ‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      ∑ i : Fin n, ‖amplify Y n ξ i‖ ^ 2 ≤
          ∑ i : Fin n, (‖Y‖ * ‖ξ i‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [amplify_apply]
        exact pow_le_pow_left₀ (norm_nonneg _) (Y.le_opNorm _) 2
      _ = ‖Y‖ ^ 2 * (∑ i : Fin n, ‖ξ i‖ ^ 2) := by
        simp_rw [mul_pow]
        rw [Finset.mul_sum]
      _ = (‖Y‖ * ‖ξ‖) ^ 2 := by rw [← PiLp.norm_sq_eq_of_L2]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg Y) (norm_nonneg ξ))).mp hs

/-- Matrix amplification of an inner derivation agrees with the commutator
of the amplified operator and the matrix operator. -/
theorem commutator_amplify_matrixOperator (Y : H →L[ℂ] H) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    commutator (amplify Y n) (matrixOperator X) =
      matrixOperator (fun i j => commutator Y (X i j)) := by
  ext ξ i
  simp [commutator, matrixOperator, amplify, map_sum, Finset.sum_sub_distrib]

variable [CompleteSpace H]

theorem scalarCommutatorNorm_nonneg (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) :
    0 ≤ scalarCommutatorNorm P Y := by
  let : SeminormedAddCommGroup P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  let : NormedSpace ℂ P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  exact norm_nonneg ((innerDerivation Y).comp
    P.toStarSubalgebra.toSubalgebra.toSubmodule.subtypeL)

/-- The defining operator norm controls every scalar commutator. -/
theorem norm_commutator_le_scalarCommutatorNorm (P : VonNeumannAlgebra H)
    (Y T : H →L[ℂ] H) (hT : T ∈ P) :
    ‖commutator Y T‖ ≤ scalarCommutatorNorm P Y * ‖T‖ := by
  let : SeminormedAddCommGroup P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  let : NormedSpace ℂ P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  exact ((innerDerivation Y).comp
    P.toStarSubalgebra.toSubalgebra.toSubmodule.subtypeL).le_opNorm ⟨T, hT⟩

/-- Characterization of the scalar commutator norm by homogeneous bounds. -/
theorem scalarCommutatorNorm_le_iff (P : VonNeumannAlgebra H)
    (Y : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c) :
    scalarCommutatorNorm P Y ≤ c ↔
      ∀ T : H →L[ℂ] H, T ∈ P → ‖commutator Y T‖ ≤ c * ‖T‖ := by
  let : SeminormedAddCommGroup P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  let : NormedSpace ℂ P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  constructor
  · intro h T hT
    exact (norm_commutator_le_scalarCommutatorNorm P Y T hT).trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg T))
  · intro h
    apply ContinuousLinearMap.opNorm_le_bound _ hc
    intro a
    exact h a a.property

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

/-- The manuscript's concrete uniform estimate bounds the complete norm of
an inner derivation after any star representation into the tested algebra. -/
theorem completeBound_commutator_of_estimate (P : VonNeumannAlgebra H)
    {C : ℝ} (hC : 0 ≤ C) (estimate : CommutatorEstimate P C)
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hσ : ∀ a, σ a ∈ P) (Y : H →L[ℂ] H) :
    CompleteBound (fun a => commutator Y (σ a)) (C * scalarCommutatorNorm P Y) := by
  intro n X
  change ‖matrixOperator (fun i j => commutator Y (σ (X i j)))‖ ≤
    (C * scalarCommutatorNorm P Y) * ‖CStarMatrix.ofMatrix X‖
  calc
    ‖matrixOperator (fun i j => commutator Y (σ (X i j)))‖ =
        ‖commutator (amplify Y n) (matrixOperator (X.map σ))‖ :=
      congrArg norm (commutator_amplify_matrixOperator Y (X.map σ)).symm
    ‖commutator (amplify Y n) (matrixOperator (fun i j => σ (X i j)))‖ ≤
        C * scalarCommutatorNorm P Y * ‖matrixOperator (fun i j => σ (X i j))‖ :=
      estimate Y n _ (fun i j => hσ (X i j))
    _ ≤ C * scalarCommutatorNorm P Y * (1 * ‖CStarMatrix.ofMatrix X‖) :=
      mul_le_mul_of_nonneg_left (completeBound_starHom σ n X)
        (mul_nonneg hC (scalarCommutatorNorm_nonneg P Y))
    _ = (C * scalarCommutatorNorm P Y) * ‖CStarMatrix.ofMatrix X‖ := by ring

end CompletelyBounded

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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_SimilarityCompleteBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual matrix bounds for a similarity, used to identify the minimum
condition number with the complete norm. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [PartialOrder A] [StarOrderedRing A]

theorem completeBound_conjugate_star (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (V W : H →L[ℂ] H) :
    CompleteBound (fun a => V * σ a * W) (‖V‖ * ‖W‖) := by
  intro n X
  have he : matrixOperator (X.map (fun a => V * σ a * W)) =
      amplify V n * matrixOperator (X.map σ) * amplify W n := by
    ext ξ i
    simp only [matrixOperator_apply, Matrix.map_apply, mul_apply_eq_comp, amplify_apply,
      map_sum]
  rw [he]
  calc
    _ ≤ (‖amplify V n‖ * ‖matrixOperator (X.map σ)‖) * ‖amplify W n‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (‖V‖ * (1 * ‖CStarMatrix.ofMatrix X‖)) * ‖W‖ := by
      gcongr
      · exact norm_amplify_le V n
      · exact completeBound_starHom σ n X
      · exact norm_amplify_le W n
    _ = _ := by ring

theorem completeBound_of_similarity (π : BoundedUnitalHom A H) (S : (H →L[ℂ] H)ˣ)
    (hS : ∀ a, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
      star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H))) :
    CompleteBound π.1 (‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖) := by
  have h := completeBound_conjugate_star (similarityStarRepresentation π S hS)
    (↑S⁻¹ : H →L[ℂ] H) (S : H →L[ℂ] H)
  simpa only [similarityStarRepresentation, similarityRepresentation, AlgHom.coe_mk,
    StarAlgHom.coe_mk, mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul,
    mul_one, mul_comm ‖(↑S⁻¹ : H →L[ℂ] H)‖] using h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_SimilarityRetract
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Similarity descends to a bounded algebraic retract. This is used for
the first-coordinate corner after finite matrix amplification. -/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem similarity_of_retract (π : BoundedUnitalHom A H) (ρ : BoundedUnitalHom A K)
    (U : H →L[ℂ] K) (V : K →L[ℂ] H)
    (h : ∀ a, V.comp ((ρ.1 a).comp U) = π.1 a)
    (hρ : SimilarToStar A K ρ) : SimilarToStar A H π := by
  obtain ⟨S, hS⟩ := hρ
  let σ := similarityStarRepresentation ρ S hS
  let W : H →L[ℂ] K := (S : K →L[ℂ] K).comp U
  let L : K →L[ℂ] H := V.comp (↑S⁻¹ : K →L[ℂ] K)
  have hf (a : A) : L.comp ((σ a).comp W) = π.1 a := by
    ext x
    have hc (z : K) : (↑S⁻¹ : K →L[ℂ] K) ((S : K →L[ℂ] K) z) = z := by
      have hz := congrArg (fun T : K →L[ℂ] K => T z) (Units.inv_mul S)
      simpa only [mul_apply_eq_comp, one_def, id_apply] using hz
    change V ((↑S⁻¹ : K →L[ℂ] K) ((S : K →L[ℂ] K)
      (ρ.1 a ((↑S⁻¹ : K →L[ℂ] K) ((S : K →L[ℂ] K) (U x)))))) = π.1 a x
    rw [hc, hc]
    exact congrArg (fun T : H →L[ℂ] H => T x) (h a)
  obtain ⟨R, _, hR⟩ := quantitative_similarity_of_factorization π σ W L hf
  exact ⟨R, hR⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_BoundedHomRestriction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction of a bounded homomorphism to a closed invariant subspace.
Similarity passes to this restriction through its orthogonal compression. -/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem restrictBoundedHom_bound (π : BoundedUnitalHom A H)
    (M : ClosedSubmodule ℂ H) (hM : ∀ a x, x ∈ M → π.1 a x ∈ M)
    {C : ℝ} (hC : 0 ≤ C) (hπ : ∀ a, ‖π.1 a‖ ≤ C * ‖a‖) (a : A) :
    ‖(restrictBoundedHom π M hM).1 a‖ ≤ C * ‖a‖ := by
  apply opNorm_le_bound _ (mul_nonneg hC (norm_nonneg _))
  intro x
  change ‖π.1 a (x : H)‖ ≤ _
  exact ((π.1 a).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (hπ a) (norm_nonneg x))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.Naimark_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u v w
namespace NaimarkZFC


section GNS

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem gnsVector_cyclic (f : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A => f.gnsStarAlgHom a (gnsVector f)) := by
  simp only [gns_apply_vector]
  exact Completion.denseRange_coe.comp f.toPreGNS.surjective.denseRange (Completion.continuous_coe _)

end GNS

section FaithfulMoments

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem gnsOrbit_dense (f : A →ₚ[ℂ] ℂ) : DenseRange (gnsOrbit f) :=
  gnsVector_cyclic f

end FaithfulMoments

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_QuadraticSandwich
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.boundedHomOrbit_apply _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.similarityRepresentation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The separation step in Haagerup's cyclic-similarity argument. Equal
finite square sums with comparable orbit norms give a positive functional
between the corresponding quadratic forms. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The only hypothesis is the finite quadratic comparison. -/
theorem exists_positive_orbit_sandwich (π : BoundedUnitalHom A H) (ξ : H) (K : ℝ)
    (hcompare : ∀ a b : List A, listSquareSum a = listSquareSum b →
      listOrbitSum π ξ a ≤ K * listOrbitSum π ξ b) :
    ∃ ω : A →ₚ[ℂ] ℂ, ∀ a : A,
      ‖π.1 a ξ‖ ^ 2 ≤ (ω (star a * a)).re ∧
        (ω (star a * a)).re ≤ K * ‖π.1 a ξ‖ ^ 2 := by
  let E := selfAdjoint A
  let P : Submodule ℝ (E × ℝ) := (LinearMap.inr ℝ E ℝ).range
  let f : (E × ℝ) →ₗ.[ℝ] ℝ := (-LinearMap.snd ℝ E ℝ).toPMap P
  let C := orbitSandwichCone π ξ K
  have hnonneg (x : f.domain) (hx : (x : E × ℝ) ∈ C) : 0 ≤ f x := by
    obtain ⟨r, hr⟩ := x.property
    obtain ⟨a, b, hab, hs⟩ := hx
    have hx0 : ((x : E × ℝ)).1 = 0 := by rw [← hr]; rfl
    have he : listSquareSum a = listSquareSum b := sub_eq_zero.mp (hab.symm.trans hx0)
    have hc := hcompare a b he
    change 0 ≤ -((x : E × ℝ)).2
    linarith
  have hdense (y : E × ℝ) : ∃ x : f.domain, (x : E × ℝ) + y ∈ C := by
    let a := CFC.sqrt (y.1 : A)⁺
    let b := CFC.sqrt (y.1 : A)⁻
    have ha : (star a * a) = (y.1 : A)⁺ := by
      rw [(CFC.sqrt_nonneg _).star_eq, CFC.sqrt_mul_sqrt_self _ (CFC.posPart_nonneg _)]
    have hb : (star b * b) = (y.1 : A)⁻ := by
      rw [(CFC.sqrt_nonneg _).star_eq, CFC.sqrt_mul_sqrt_self _ (CFC.negPart_nonneg _)]
    let r := listOrbitSum π ξ [a] - K * listOrbitSum π ξ [b] - y.2
    refine ⟨⟨(0, r), ⟨r, rfl⟩⟩, [a], [b], ?_, ?_⟩
    · apply Subtype.ext
      simp only [Prod.fst_add, zero_add, AddSubgroupClass.coe_sub,
        listSquareSum_singleton_coe]
      rw [ha, hb, CFC.posPart_sub_negPart _ y.1.property]
    · change r + y.2 ≤ _
      dsimp [r]
      linarith
  obtain ⟨g, hg, hgpos⟩ := riesz_extension C f hnonneg hdense
  have hvertical (r : ℝ) : g (0, r) = -r := hg ⟨(0, r), ⟨r, rfl⟩⟩
  let φ : E →ₗ[ℝ] ℝ := g.comp (LinearMap.inl ℝ E ℝ)
  have hgformula (x : E) (r : ℝ) : g (x, r) = φ x - r := by
    have he : (x, r) = (x, (0 : ℝ)) + (0, r) := by simp
    rw [he, map_add, hvertical]
    rfl
  have hbounds (a : A) : ‖π.1 a ξ‖ ^ 2 ≤ φ (listSquareSum [a]) ∧
      φ (listSquareSum [a]) ≤ K * ‖π.1 a ξ‖ ^ 2 := by
    have hlo := hgpos (listSquareSum [a], ‖π.1 a ξ‖ ^ 2)
      ⟨[a], [], by simp [listOrbitSum]⟩
    have hhi := hgpos (-listSquareSum [a], -K * ‖π.1 a ξ‖ ^ 2)
      ⟨[], [a], by simp [listOrbitSum]⟩
    rw [hgformula] at hlo hhi
    simp only [map_neg] at hhi
    constructor <;> linarith
  have hφpos (x : A) (hx : 0 ≤ x) : 0 ≤ φ ⟨x, hx.isSelfAdjoint⟩ := by
    have he : listSquareSum [CFC.sqrt x] = ⟨x, hx.isSelfAdjoint⟩ := by
      apply Subtype.ext
      simp only [listSquareSum_singleton_coe]
      rw [(CFC.sqrt_nonneg _).star_eq, CFC.sqrt_mul_sqrt_self _ hx]
    exact (sq_nonneg _).trans (he ▸ (hbounds (CFC.sqrt x)).1)
  let ω : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ (NaimarkZFC.selfAdjointComplexify φ)
    (fun x hx => by
      rw [show x = (⟨x, hx.isSelfAdjoint⟩ : selfAdjoint A) from rfl,
        NaimarkZFC.selfAdjointComplexify_coe]
      exact ⟨hφpos x hx, by simp⟩)
  refine ⟨ω, fun a => ?_⟩
  change _ ≤ (NaimarkZFC.selfAdjointComplexify φ (star a * a)).re ∧ _
  have he : (star a * a) = (listSquareSum [a] : A) := (listSquareSum_singleton_coe a).symm
  change _ ≤ (NaimarkZFC.selfAdjointComplexify φ (star a * a)).re ∧
    (NaimarkZFC.selfAdjointComplexify φ (star a * a)).re ≤ _
  rw [he, NaimarkZFC.selfAdjointComplexify_coe]
  exact hbounds a

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_CyclicSimilarity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.similarityRepresentation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive functional comparable to a cyclic orbit gives an actual
invertible intertwiner with its GNS representation. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem similarity_of_cyclic_orbit_sandwich (π : BoundedUnitalHom A H) (ξ : H)
    (hcyc : DenseRange (fun a : A => π.1 a ξ)) (ω : A →ₚ[ℂ] ℂ)
    {K : ℝ} (hK : 0 ≤ K)
    (hω : ∀ a, ‖π.1 a ξ‖ ^ 2 ≤ (ω (star a * a)).re ∧
      (ω (star a * a)).re ≤ K * ‖π.1 a ξ‖ ^ 2) : SimilarToStar A H π := by
  let e := boundedHomOrbit π ξ
  let g := NaimarkZFC.gnsOrbit ω
  have he : DenseRange e.toLinearMap := hcyc
  have hg : DenseRange g.toLinearMap := NaimarkZFC.gnsOrbit_dense ω
  have hgnorm (a : A) : ‖g a‖ ^ 2 = (ω (star a * a)).re := by
    simp only [g, NaimarkZFC.gnsOrbit_apply, UniformSpace.Completion.norm_coe,
      PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.ofPreGNS_toPreGNS]
    exact Real.sq_sqrt (ω.map_nonneg (star_mul_self_nonneg a)).1
  have heg (a : A) : ‖e a‖ ≤ 1 * ‖g a‖ := by
    rw [one_mul]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hgnorm]
    exact (hω a).1
  have hge (a : A) : ‖g a‖ ≤ Real.sqrt K * ‖e a‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hK, hgnorm]
    exact (hω a).2
  let W : H →L[ℂ] ω.GNS := g.toLinearMap.extendOfNorm e.toLinearMap
  let L : ω.GNS →L[ℂ] H := e.toLinearMap.extendOfNorm g.toLinearMap
  have hW (a : A) : W (e a) = g a :=
    LinearMap.extendOfNorm_eq he ⟨Real.sqrt K, hge⟩ a
  have hL (a : A) : L (g a) = e a :=
    LinearMap.extendOfNorm_eq hg ⟨1, heg⟩ a
  have hLW : L.comp W = 1 := by
    ext x
    exact he.induction (by
      rintro y ⟨a, rfl⟩
      change L (W (e a)) = e a
      rw [hW, hL]) (isClosed_eq (L.continuous.comp W.continuous) continuous_id) x
  have hWL : W.comp L = 1 := by
    ext x
    exact hg.induction (by
      rintro y ⟨a, rfl⟩
      change W (L (g a)) = g a
      rw [hL, hW]) (isClosed_eq (W.continuous.comp L.continuous) continuous_id) x
  have hinter (a : A) : W.comp (π.1 a) = (ω.gnsStarAlgHom a).comp W := by
    ext x
    change W (π.1 a x) = ω.gnsStarAlgHom a (W x)
    refine he.induction ?_ (isClosed_eq (W.continuous.comp (π.1 a).continuous)
      ((ω.gnsStarAlgHom a).continuous.comp W.continuous)) x
    rintro y ⟨b, rfl⟩
    change W (π.1 a (e b)) = ω.gnsStarAlgHom a (W (e b))
    have heab : π.1 a (e b) = e (a * b) := by simp [e, map_mul, mul_apply_eq_comp]
    rw [heab, hW, hW]
    simp only [g, NaimarkZFC.gnsOrbit_apply, NaimarkZFC.gns_apply_coe]
  obtain ⟨S, _, hS⟩ := quantitative_similarity_of_intertwiner π ω.gnsStarAlgHom W L hLW hWL hinter
  exact ⟨S, hS⟩

/-- Every bounded cyclic representation is similar to a star representation.
The proof uses only the established little Grothendieck estimate and GNS. -/
theorem cyclic_similarity (π : BoundedUnitalHom A H) (ξ : H)
    (hcyc : DenseRange (fun a : A => π.1 a ξ)) : SimilarToStar A H π := by
  let f : A →L[ℂ] (H →L[ℂ] H) := ⟨π.1.toLinearMap, π.2⟩
  obtain ⟨ω, hω⟩ := exists_positive_orbit_sandwich π ξ ((2 * ‖f‖ ^ 4) ^ 2)
    (fun a b hab => list_equal_square_orbit_comparison π (norm_nonneg f)
      (fun a => f.le_opNorm a) a b hab ξ)
  exact similarity_of_cyclic_orbit_sandwich π ξ hcyc ω (sq_nonneg _) hω

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_BoundedMatrixHom
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite matrix amplification of a bounded homomorphism. A finite
generating family becomes one cyclic vector for this amplification. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem boundedMatrixHom_cyclic (π : BoundedUnitalHom A H) {n : ℕ}
    (ξ : Fin n → H) (hξ : DenseRange (finiteOrbitMap π ξ)) :
    DenseRange (fun X : CStarMatrix (Fin n) (Fin n) A =>
      (boundedMatrixHom π n).1 X (WithLp.toLp 2 ξ)) := by
  let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm
  have hd : DenseRange (fun a : Fin n → Fin n → A => fun i => finiteOrbitMap π ξ (a i)) :=
    DenseRange.piMap (fun _ => hξ)
  have he := e.surjective.denseRange.comp hd e.continuous
  apply he.mono
  rintro x ⟨a, rfl⟩
  refine ⟨CStarMatrix.ofMatrix a, ?_⟩
  ext i
  simp only [boundedMatrixHom_apply, finiteOrbitMap, LinearMap.coe_mk,
    AddHom.coe_mk]
  rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_FiniteCyclicSimilarity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.hilbertArrayFlatten_apply _root_.OAI.KadisonSimilarity.hilbertFourfoldFlatten_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.hilbertTripleFlatten_apply _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.matrixLeftArray_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.representedDoubleMatrix_apply _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finitely cyclic representations reduce to the cyclic case by finite
matrix amplification and the first-coordinate corner. -/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finitely_cyclic_similarity (π : BoundedUnitalHom A H) {n : ℕ} (hn : 0 < n)
    (ξ : Fin n → H) (hξ : DenseRange (finiteOrbitMap π ξ)) : SimilarToStar A H π := by
  let ρ := boundedMatrixHom π n
  obtain ⟨S, hS⟩ := cyclic_similarity ρ (WithLp.toLp 2 ξ) (boundedMatrixHom_cyclic π ξ hξ)
  let φ := scalarCStarMatrixHom (A := A) n
  let L := φ.toLinearMap.mkContinuous 1
    (fun a => by simpa using NonUnitalStarAlgHom.norm_apply_le φ a)
  let τ : BoundedUnitalHom A (HilbertCopies H n) :=
    ⟨ρ.1.comp φ.toAlgHom, ρ.2.comp L.continuous⟩
  have hτ : SimilarToStar A (HilbertCopies H n) τ := by
    refine ⟨S, fun a => ?_⟩
    change (S : _ →L[ℂ] _) * ρ.1 (φ (star a)) * (↑S⁻¹ : _ →L[ℂ] _) = _
    rw [map_star]
    exact hS (φ a)
  let U := firstCoordinateInclusion (H := H) n hn
  let V : HilbertCopies H n →L[ℂ] H := PiLp.proj 2 (fun _ : Fin n => H) (⟨0, hn⟩ : Fin n)
  apply similarity_of_retract π τ U V ?_ hτ
  intro a
  ext x
  change (boundedMatrixHom π n).1 (φ a) (U x) (⟨0, hn⟩ : Fin n) = π.1 a x
  rw [boundedMatrixHom_apply]
  rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
  · have hd : (φ a) (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n) = a := by
      change (if (⟨0, hn⟩ : Fin n) = ⟨0, hn⟩ then a else 0) = a
      simp
    rw [hd]
    congr 1
  · intro j _ hj
    have hd : (φ a) (⟨0, hn⟩ : Fin n) j = 0 := by
      change (if (⟨0, hn⟩ : Fin n) = j then a else 0) = 0
      simp [Ne.symm hj]
    rw [hd, map_zero]
    rfl
  · simp

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FiniteOrbitSubspace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseCompression_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_left_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_vector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator_adjoint _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerInto_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightTransferBack_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightTransferMap_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightTransfer_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.invariantStarRepresentation_apply _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberAction_coe _root_.OAI.KadisonSimilarity.projectionFiberCompression_coe _root_.OAI.KadisonSimilarity.projectionFiberRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_inclusion _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.unitizationRangeRepresentation_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The closed invariant subspace generated by finitely many vectors is
finitely cyclic, and therefore its restricted representation is similar. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
theorem finiteOrbitSubspace_cyclic (π : BoundedUnitalHom A H) {n : ℕ} (ξ : Fin n → H) :
    DenseRange (finiteOrbitMap
      (restrictBoundedHom π (finiteOrbitSubspace π ξ) (finiteOrbitSubspace_invariant π ξ))
      (finiteOrbitGenerators π ξ)) := by
  let M := finiteOrbitSubspace π ξ
  let F := finiteOrbitMap π ξ
  let e : (Fin n → A) →ₗ[ℂ] M := F.codRestrict M.toSubmodule
    (fun a => (LinearMap.range F).le_topologicalClosure ⟨a, rfl⟩)
  have he : DenseRange e := by
    change Dense (Set.range e)
    rw [Subtype.dense_iff, ← Set.range_comp]
    change closure (Set.range F) ⊆ closure (Set.range F)
    exact Set.Subset.rfl
  have heq : finiteOrbitMap
      (restrictBoundedHom π (finiteOrbitSubspace π ξ) (finiteOrbitSubspace_invariant π ξ))
      (finiteOrbitGenerators π ξ) = e := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    simp [finiteOrbitMap, e, F, finiteOrbitGenerators, restrictBoundedHom_apply]
    rfl
  rw [heq]
  exact he

theorem finiteOrbitSubspace_similar (π : BoundedUnitalHom A H) {n : ℕ} (hn : 0 < n)
    (ξ : Fin n → H) :
    SimilarToStar A (finiteOrbitSubspace π ξ)
      (restrictBoundedHom π (finiteOrbitSubspace π ξ) (finiteOrbitSubspace_invariant π ξ)) :=
  finitely_cyclic_similarity _ hn (finiteOrbitGenerators π ξ) (finiteOrbitSubspace_cyclic π ξ)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ScalarKaplansky
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.vonNeumannInnerDerivation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-test-vector specialization of matrix Kaplansky density and
C*-quotient norm lifting is enough for the scalar commutator closure used
in the final derivation and separability reductions. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A bound on the original algebra extends to its von Neumann closure using
only the two vectors needed for each commutator test. -/
theorem scalarKaplanskyClosure_of_twoVector
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (P : VonNeumannAlgebra H)
    (kaplansky : TwoVectorKaplanskyInput σ P) : ScalarKaplanskyClosure σ P := by
  intro V d hd hV
  apply (scalarCommutatorNorm_le_iff P V hd).mpr
  intro b hb
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hd (norm_nonneg b))
  intro x
  apply le_of_forall_pos_le_add
  intro η hη
  let K := ‖V‖ + 1 + d * ‖x‖
  have hK : 0 < K := by dsimp [K]; positivity
  let ε := η / K
  have hε : 0 < ε := div_pos hη hK
  obtain ⟨a, ha, hx, hVx⟩ := kaplansky b hb x (V x) ε hε
  have herr : ‖commutator V b x - commutator V (σ a) x‖ ≤ ‖V‖ * ε + ε := by
    have heq : commutator V b x - commutator V (σ a) x =
        V (b x - σ a x) - (b (V x) - σ a (V x)) := by
      simp only [commutator, sub_apply, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply, map_sub]
      abel
    rw [heq]
    calc
      _ ≤ ‖V (b x - σ a x)‖ + ‖b (V x) - σ a (V x)‖ := norm_sub_le _ _
      _ ≤ ‖V‖ * ‖b x - σ a x‖ + ‖b (V x) - σ a (V x)‖ :=
        add_le_add (V.le_opNorm _) le_rfl
      _ ≤ ‖V‖ * ε + ε := by
        rw [norm_sub_rev (b x), norm_sub_rev (b (V x))]
        exact add_le_add (mul_le_mul_of_nonneg_left hx (norm_nonneg V)) hVx
  have hmain : ‖commutator V (σ a) x‖ ≤ d * (‖b‖ + ε) * ‖x‖ := by
    calc
      _ ≤ ‖commutator V (σ a)‖ * ‖x‖ := (commutator V (σ a)).le_opNorm x
      _ ≤ (d * ‖a‖) * ‖x‖ := mul_le_mul_of_nonneg_right (hV a) (norm_nonneg x)
      _ ≤ d * (‖b‖ + ε) * ‖x‖ := by gcongr
  calc
    ‖commutator V b x‖ ≤ ‖commutator V (σ a) x‖ +
        ‖commutator V b x - commutator V (σ a) x‖ := by
      simpa only [add_sub_cancel] using norm_add_le
        (commutator V (σ a) x) (commutator V b x - commutator V (σ a) x)
    _ ≤ d * (‖b‖ + ε) * ‖x‖ + (‖V‖ * ε + ε) := add_le_add hmain herr
    _ = d * ‖b‖ * ‖x‖ + η := by
      have hcancel : ε * K = η := div_mul_cancel₀ η (ne_of_gt hK)
      dsimp [K] at hcancel
      nlinarith

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_AmplifyExponential
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.hilbertArrayFlatten_apply _root_.OAI.KadisonSimilarity.hilbertFourfoldFlatten_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.hilbertTripleFlatten_apply _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.matrixLeftArray_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_apply _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_zero _root_.OAI.KadisonSimilarity.representedDoubleMatrix_apply _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity
open NormedSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem amplify_continuous (n : ℕ) : Continuous (fun Y : H →L[ℂ] H => amplify Y n) := by
  let L : (H →L[ℂ] H) →ₗ[ℂ] (HilbertCopies H n →L[ℂ] HilbertCopies H n) :=
    (amplifyAlgHom n).toLinearMap
  exact (L.mkContinuous 1 (fun Y => by change ‖amplify Y n‖ ≤ 1 * ‖Y‖; simpa using norm_amplify_le Y n)).continuous

@[simp] theorem amplify_exp (Y : H →L[ℂ] H) (n : ℕ) :
    amplify (exp Y) n = exp (amplify Y n) := by
  let : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  let : NormedAlgebra ℚ (HilbertCopies H n →L[ℂ] HilbertCopies H n) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.map_exp (amplifyAlgHom n) (amplify_continuous n) Y

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_CompleteNorm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The least nonnegative complete bound. Kirchberg's proof uses a
similarity attaining this bound, rather than an arbitrary similarity. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem completeNorm_nonneg {f : A → (H →L[ℂ] H)} (hf : IsCompletelyBounded f) :
    0 ≤ completeNorm f :=
  le_csInf hf (fun _ h => h.1)

theorem completeNorm_le {f : A → (H →L[ℂ] H)} {C : ℝ}
    (hC : 0 ≤ C) (hf : CompleteBound f C) : completeNorm f ≤ C :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨hC, hf⟩

/-- Complete bounds form a closed set, so their finite infimum is a bound. -/
theorem completeBound_completeNorm {f : A → (H →L[ℂ] H)}
    (hf : IsCompletelyBounded f) : CompleteBound f (completeNorm f) := by
  intro n X
  by_cases hz : ‖CStarMatrix.ofMatrix X‖ = 0
  · obtain ⟨C, _, hC⟩ := hf
    simpa only [hz, mul_zero] using hC n X
  · have hp : 0 < ‖CStarMatrix.ofMatrix X‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (div_le_iff₀ hp).mp
    exact le_csInf hf (fun C hC => (div_le_iff₀ hp).mpr (hC.2 n X))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_KirchbergExponentialNorm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact exponential condition-number scaling used on page 61 of
Kirchberg's proof. -/

noncomputable section
namespace KadisonSimilarity

open NormedSpace
open scoped CStarAlgebra

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem exp_real_smul_eq_rpow (t : B) (ht : IsSelfAdjoint t) (s : ℝ) :
    exp (s • t) = (exp t) ^ s := by
  have hs : IsSelfAdjoint (s • t) := (IsSelfAdjoint.all s).smul ht
  rw [← CFC.real_exp_eq_normedSpace_exp hs, ← cfc_comp_const_mul s Real.exp t (by fun_prop) ht,
    ← CFC.real_exp_eq_normedSpace_exp ht,
    CFC.cfc_rpow (fun x _ => Real.exp_pos x) (by fun_prop) ht]
  congr 1
  funext x
  rw [mul_comm s x, Real.exp_mul]

theorem norm_exp_real_smul (t : B) (ht : IsSelfAdjoint t) {s : ℝ} (hs : 0 < s) :
    ‖exp (s • t)‖ = ‖exp t‖ ^ s := by
  rw [exp_real_smul_eq_rpow t ht s, CFC.norm_rpow _ hs ht.exp_nonneg]

/-- The product of the forward and inverse norms scales by the same power. -/
theorem exp_condition_real_smul (t : B) (ht : IsSelfAdjoint t) {s : ℝ} (hs : 0 < s) :
    ‖exp (s • (-t))‖ * ‖exp (s • t)‖ = (‖exp (-t)‖ * ‖exp t‖) ^ s := by
  rw [norm_exp_real_smul (-t) ht.neg hs, norm_exp_real_smul t ht hs,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

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
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_PositiveSimilarity
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Paulsen's attained complete bound can be realized by a positive
similarity. Kirchberg takes its self-adjoint logarithm. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
theorem positive_similarity_of_similarity (π : BoundedUnitalHom A H)
    (U : (H →L[ℂ] H)ˣ)
    (hU : ∀ a, (U : H →L[ℂ] H) * π.1 (star a) * (↑U⁻¹ : H →L[ℂ] H) =
      star ((U : H →L[ℂ] H) * π.1 a * (↑U⁻¹ : H →L[ℂ] H))) :
    ∃ S : (H →L[ℂ] H)ˣ, 0 ≤ (S : H →L[ℂ] H) ∧
      ‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖ =
        ‖(U : H →L[ℂ] H)‖ * ‖(↑U⁻¹ : H →L[ℂ] H)‖ ∧
      ∀ a, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
        star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H)) := by
  have hm (a : A) :
      (star (U : H →L[ℂ] H) * (U : H →L[ℂ] H)) * π.1 (star a) =
        star (π.1 a) * (star (U : H →L[ℂ] H) * (U : H →L[ℂ] H)) := by
    have h := congrArg (fun X : H →L[ℂ] H =>
      star (U : H →L[ℂ] H) * X * (U : H →L[ℂ] H)) (hU a)
    simpa only [star_mul, star_inv, mul_assoc, ← Units.coe_star_inv, ← Units.coe_star,
      Units.inv_mul, Units.mul_inv, Units.inv_mul_cancel_left,
      Units.mul_inv_cancel_left, mul_one, one_mul] using h
  obtain ⟨S, hp, hmetric, hn, hi⟩ := exists_positive_sqrt_metric_unit
    (U : H →L[ℂ] H) (↑U⁻¹ : H →L[ℂ] H) U.inv_val U.val_inv
  refine ⟨S, hp, by rw [hn, hi], ?_⟩
  intro a
  have hm' : (star (S : H →L[ℂ] H) * (S : H →L[ℂ] H)) * π.1 (star a) =
      star (π.1 a) * (star (S : H →L[ℂ] H) * (S : H →L[ℂ] H)) := by
    rw [hmetric]
    simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] using hm a
  have h := congrArg (fun X : H →L[ℂ] H =>
    star (↑S⁻¹ : H →L[ℂ] H) * X * (↑S⁻¹ : H →L[ℂ] H)) hm'
  simpa only [star_mul, star_inv, mul_assoc, ← Units.coe_star_inv, ← Units.coe_star,
    Units.inv_mul, Units.mul_inv, Units.inv_mul_cancel_left,
    Units.mul_inv_cancel_left, mul_one, one_mul] using h

/-- The positive similarity has condition number exactly the complete norm. -/
theorem exists_positive_similarity_completeNorm (π : BoundedUnitalHom A H)
    (hπ : IsCompletelyBounded π.1) :
    ∃ S : (H →L[ℂ] H)ˣ, 0 ≤ (S : H →L[ℂ] H) ∧
      ‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖ = completeNorm π.1 ∧
      ∀ a, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
        star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H)) := by
  obtain ⟨U, hUnorm, hU⟩ := paulsenSimilarityInput π (completeNorm π.1)
    (completeNorm_nonneg hπ) (completeBound_completeNorm hπ)
  obtain ⟨S, hp, hn, hS⟩ := positive_similarity_of_similarity π U hU
  refine ⟨S, hp, le_antisymm (hn.le.trans hUnorm) ?_, hS⟩
  exact completeNorm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (completeBound_of_similarity π S hS)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_ExponentialSimilarity
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The optimal positive similarity, written in the exponential form used
in Kirchberg, J. Operator Theory 36 (1996), Proposition 1. -/

noncomputable section
namespace KadisonSimilarity
open NormedSpace
open scoped CStarAlgebra

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonSimilarity.exponentialSimilarityRatAlgebra
theorem exists_exponential_similarity (π : BoundedUnitalHom A H)
    (hπ : IsCompletelyBounded π.1) :
    ∃ (t : H →L[ℂ] H) (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)), IsSelfAdjoint t ∧
      (∀ a, π.1 a = exp (-t) * σ a * exp t) ∧
      ‖exp (-t)‖ * ‖exp t‖ = completeNorm π.1 := by
  obtain ⟨S, hp, hn, hS⟩ := exists_positive_similarity_completeNorm π hπ
  let t := CFC.log (S : H →L[ℂ] H)
  have ht : IsSelfAdjoint t := IsSelfAdjoint.log
  have he : exp t = (S : H →L[ℂ] H) := CFC.exp_log _ (S.isUnit.isStrictlyPositive hp)
  have hi : exp (-t) = (↑S⁻¹ : H →L[ℂ] H) := by
    have h : exp (-t) * (S : H →L[ℂ] H) = 1 := by
      rw [← he, ← exp_add_of_commute (Commute.refl t).neg_left,
        neg_add_cancel, NormedSpace.exp_zero]
    have h' := congrArg (fun X : H →L[ℂ] H => X * (↑S⁻¹ : H →L[ℂ] H)) h
    simpa only [mul_assoc, Units.mul_inv, mul_one, one_mul] using h'
  refine ⟨t, similarityStarRepresentation π S hS, ht, ?_, ?_⟩
  · intro a
    simp only [he, hi, similarityStarRepresentation, similarityRepresentation,
      StarAlgHom.coe_mk, mul_assoc, Units.inv_mul_cancel_left,
      Units.inv_mul, mul_one]
  · rw [he, hi, mul_comm]
    exact hn

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_KirchbergNumerics
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar cancellation in Kirchberg, J. Operator Theory 36 (1996),
page 61. The analytic estimate preceding it is kept separate. -/

namespace KadisonSimilarity

/-- Cancellation of the nonzero `K - 1` in Kirchberg's integral estimate. -/
theorem log_le_of_kirchberg_inequality {K D : ℝ} (hK : 1 < K)
    (h : K ≤ 1 + D * ((K - 1) / Real.log K)) : Real.log K ≤ D := by
  have hl : 0 < Real.log K := Real.log_pos hK
  have hh : K - 1 ≤ D * ((K - 1) / Real.log K) := by linarith
  have hm := (le_div_iff₀ hl).mp (show K - 1 ≤ D * (K - 1) / Real.log K by
    simpa only [mul_div_assoc] using hh)
  nlinarith

/-- The estimate also covers completely contractive representations. -/
theorem le_exp_of_kirchberg_inequality {K D : ℝ} (hD : 0 ≤ D)
    (h : 1 < K → K ≤ 1 + D * ((K - 1) / Real.log K)) :
    K ≤ Real.exp D := by
  by_cases hK : 1 < K
  · exact (Real.log_le_iff_le_exp (by linarith : 0 < K)).mp
      (log_le_of_kirchberg_inequality hK (h hK))
  · exact (le_of_not_gt hK).trans (Real.one_le_exp hD)

end KadisonSimilarity

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_KirchbergIntegral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fundamental-theorem-of-calculus estimate in Kirchberg's
Proposition 1, page 61. -/

noncomputable section
namespace KadisonSimilarity

open NormedSpace MeasureTheory Set
open scoped Topology

theorem integral_const_rpow_unit {K : ℝ} (hK : 1 < K) :
    (∫ s : ℝ in 0..1, K ^ s) = (K - 1) / Real.log K := by
  have hK0 : 0 < K := lt_trans zero_lt_one hK
  have hl : Real.log K ≠ 0 := ne_of_gt (Real.log_pos hK)
  have hder (s : ℝ) : HasDerivAt (fun x : ℝ => K ^ x / Real.log K) (K ^ s) s := by
    simpa only [mul_div_cancel_right₀ _ hl] using
      (Real.hasStrictDerivAt_const_rpow hK0 s).hasDerivAt.div_const (Real.log K)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hder s) ((Real.continuous_const_rpow hK0.ne').intervalIntegrable 0 1)
  simpa only [Real.rpow_one, Real.rpow_zero, ← sub_div] using h

section Algebra

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]

theorem real_conjugation_hasDerivAt (t a : B) (s : ℝ) :
    HasDerivAt (fun x : ℝ => exp (x • (-t)) * a * exp (x • t))
      (exp (s • (-t)) * (a * t - t * a) * exp (s • t)) s := by
  have h := ((hasDerivAt_exp_smul_const (-t) s).mul_const a).mul
    (hasDerivAt_exp_smul_const t s)
  have hc : Commute t (exp (s • t)) := ((Commute.refl t).smul_right s).exp_right
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [mul_sub, sub_mul, mul_neg, neg_mul, mul_assoc, ← hc.eq]
  abel

attribute [local instance] OAI.KadisonSimilarity.kirchbergIntegralRatAlgebra
theorem real_conjugation_integral (t a : B) :
    (∫ s : ℝ in 0..1, exp (s • (-t)) * (a * t - t * a) * exp (s • t)) =
      exp (-t) * a * exp t - a := by
  have hc : Continuous (fun s : ℝ => exp (s • (-t)) * (a * t - t * a) * exp (s • t)) := by
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => real_conjugation_hasDerivAt t a s) (hc.intervalIntegrable 0 1)
  simpa only [one_smul, zero_smul, NormedSpace.exp_zero, one_mul, mul_one] using h

/-- The matrix-independent path estimate. The precise condition-number
scaling is supplied separately by functional calculus. -/
theorem norm_real_conjugation_le (t a : B) {K : ℝ} (hK : 1 < K)
    (hscale : ∀ s ∈ Ioc (0 : ℝ) 1,
      ‖exp (s • (-t))‖ * ‖exp (s • t)‖ ≤ K ^ s) :
    ‖exp (-t) * a * exp t‖ ≤
      ‖a‖ + ‖a * t - t * a‖ * ((K - 1) / Real.log K) := by
  have hK0 : 0 < K := lt_trans zero_lt_one hK
  have hint : IntervalIntegrable (fun s : ℝ => ‖a * t - t * a‖ * K ^ s) volume 0 1 :=
    (continuous_const.mul (Real.continuous_const_rpow hK0.ne')).intervalIntegrable 0 1
  have hbound := intervalIntegral.norm_integral_le_of_norm_le (a := (0 : ℝ)) (b := 1)
    (f := fun s : ℝ => exp (s • (-t)) * (a * t - t * a) * exp (s • t)) zero_le_one
    (Filter.Eventually.of_forall (fun s hs => show
      ‖exp (s • (-t)) * (a * t - t * a) * exp (s • t)‖ ≤
        ‖a * t - t * a‖ * K ^ s from by
      calc
        _ ≤ (‖exp (s • (-t))‖ * ‖a * t - t * a‖) * ‖exp (s • t)‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ = ‖a * t - t * a‖ * (‖exp (s • (-t))‖ * ‖exp (s • t)‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hscale s hs) (norm_nonneg _))) hint
  rw [real_conjugation_integral, intervalIntegral.integral_const_mul,
    integral_const_rpow_unit hK] at hbound
  calc
    _ = ‖a + (exp (-t) * a * exp t - a)‖ := by congr 1; abel
    _ ≤ ‖a‖ + ‖exp (-t) * a * exp t - a‖ := norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl hbound

end Algebra
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_KirchbergCompleteBound
attribute [-instance] _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kirchberg's cancellation argument at all matrix sizes, with the
commutator estimate left as an explicit hypothesis. -/

noncomputable section
namespace KadisonSimilarity
open NormedSpace

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kirchberg_completeNorm_le_exp (π : BoundedUnitalHom A H)
    (t : H →L[ℂ] H) (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ht : IsSelfAdjoint t)
    (hπ : ∀ a, π.1 a = exp (-t) * σ a * exp t)
    (hK : ‖exp (-t)‖ * ‖exp t‖ = completeNorm π.1)
    {D : ℝ} (hD : 0 ≤ D) (hδ : CompleteBound (fun a => commutator t (σ a)) D) :
    completeNorm π.1 ≤ Real.exp D := by
  apply le_exp_of_kirchberg_inequality hD
  intro hlarge
  let K := completeNorm π.1
  let q := (K - 1) / Real.log K
  have hq : 0 ≤ q := div_nonneg (sub_nonneg.mpr hlarge.le) (Real.log_pos hlarge).le
  apply completeNorm_le (show 0 ≤ 1 + D * q by positivity)
  intro n X
  let a := matrixOperator (X.map σ)
  let T := amplify t n
  have hscale (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
      ‖exp (s • (-T))‖ * ‖exp (s • T)‖ ≤ K ^ s := by
    change ‖exp (s • (-amplify t n))‖ * ‖exp (s • amplify t n)‖ ≤ _
    rw [← amplify_neg, ← amplify_smul, ← amplify_smul, ← amplify_exp, ← amplify_exp]
    calc
      _ ≤ ‖exp (s • (-t))‖ * ‖exp (s • t)‖ :=
        mul_le_mul (norm_amplify_le _ n) (norm_amplify_le _ n) (norm_nonneg _) (norm_nonneg _)
      _ = K ^ s := by rw [exp_condition_real_smul t ht hs.1, hK]
  have he : matrixOperator (X.map π.1) = exp (-T) * a * exp T := by
    change _ = exp (-amplify t n) * _ * exp (amplify t n)
    rw [← amplify_neg, ← amplify_exp, ← amplify_exp]
    ext ξ i
    simp only [a, matrixOperator_apply, Matrix.map_apply, hπ, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      amplify_apply, map_sum]
  have hd : ‖a * T - T * a‖ ≤ D * ‖CStarMatrix.ofMatrix X‖ := by
    rw [norm_sub_rev]
    change ‖commutator T a‖ ≤ _
    rw [show commutator T a = matrixOperator (fun i j => commutator t (σ (X i j))) from
      commutator_amplify_matrixOperator t (X.map σ)]
    exact hδ n X
  rw [he]
  calc
    _ ≤ ‖a‖ + ‖a * T - T * a‖ * q := norm_real_conjugation_le T a hlarge hscale
    _ ≤ ‖CStarMatrix.ofMatrix X‖ + (D * ‖CStarMatrix.ofMatrix X‖) * q := by
      exact add_le_add (by simpa only [one_mul] using completeBound_starHom σ n X)
        (mul_le_mul_of_nonneg_right hd hq)
    _ = (1 + D * q) * ‖CStarMatrix.ofMatrix X‖ := by ring

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_KirchbergConjugation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The entire conjugation path used in Kirchberg's Proposition 1,
J. Operator Theory 36 (1996), pp. 60--61. -/

noncomputable section
namespace KadisonSimilarity

open NormedSpace Complex Set

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [StarRing B]
  [CStarRing B] [CompleteSpace B] [StarModule ℂ B]

omit [StarRing B] [CStarRing B] [StarModule ℂ B] in
theorem differentiable_kirchbergPath (t a : B) :
    Differentiable ℂ (kirchbergPath t a) := by
  unfold kirchbergPath
  fun_prop

omit [StarRing B] [CStarRing B] [StarModule ℂ B] in
theorem kirchbergPath_hasDerivAt_zero (t a : B) :
    HasDerivAt (kirchbergPath t a) (a * t - t * a) 0 := by
  change HasDerivAt (fun z : ℂ => exp (z • (-t)) * a * exp (z • t)) _ _
  have h₁ := (hasDerivAt_exp_smul_const (-t) (0 : ℂ)).mul_const a
  have h₂ := h₁.mul (hasDerivAt_exp_smul_const t (0 : ℂ))
  simpa only [Pi.mul_def, zero_smul, NormedSpace.exp_zero, one_mul, mul_one,
    neg_mul, sub_eq_add_neg, add_comm] using h₂

attribute [local instance] OAI.KadisonSimilarity.kirchbergConjugationRatAlgebra
theorem kirchbergPath_norm_re (t a : B) (ht : IsSelfAdjoint t) (z : ℂ) :
    ‖kirchbergPath t a z‖ = ‖kirchbergPath t a (z.re : ℂ)‖ := by
  have hcomm (s w : ℂ) : Commute (s • t) (w • t) :=
    ((Commute.refl t).smul_left s).smul_right w
  let U : unitary B := selfAdjoint.expUnitary (z.im • ⟨t, ht⟩)
  let V : unitary B := selfAdjoint.expUnitary ((-z.im) • ⟨t, ht⟩)
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * I := by
    simpa only [mul_comm] using (re_add_im z).symm
  have hleft : exp (z • (-t)) =
      (V : B) * exp ((z.re : ℂ) • (-t)) := by
    conv_lhs => rw [hz, add_smul, add_comm]
    rw [exp_add_of_commute]
    · congr 1
      simp [V, selfAdjoint.expUnitary_coe, ← Complex.coe_smul, smul_smul, mul_comm]
    · exact ((Commute.refl (-t)).smul_left _).smul_right _
  have hright : exp (z • t) = exp ((z.re : ℂ) • t) * (U : B) := by
    conv_lhs => rw [hz, add_smul, exp_add_of_commute (hcomm _ _)]
    congr 1
    simp [U, selfAdjoint.expUnitary_coe, ← Complex.coe_smul, smul_smul, mul_comm]
  rw [kirchbergPath, hleft, hright]
  calc
    _ = ‖(V : B) * (exp ((z.re : ℂ) • (-t)) * a *
        exp ((z.re : ℂ) • t)) * (U : B)‖ := by simp only [mul_assoc]
    _ = _ := by rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]; rfl

/-- Compactness of the real interval gives boundedness on the infinite strip. -/
theorem kirchbergPath_strip_bddAbove (t a : B) (ht : IsSelfAdjoint t) :
    BddAbove ((norm ∘ kirchbergPath t a) ''
      Complex.HadamardThreeLines.verticalClosedStrip (-1) 1) := by
  have hc : Continuous (fun x : ℝ => ‖kirchbergPath t a (x : ℂ)‖) :=
    (differentiable_kirchbergPath t a).continuous.comp Complex.continuous_ofReal |>.norm
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hc).bddAbove
  refine ⟨C, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  rw [Function.comp_apply, kirchbergPath_norm_re t a ht z]
  exact hC ⟨z.re, hz, rfl⟩

/-- The two boundary bounds control the whole strip, by three lines. -/
theorem kirchbergPath_norm_le (t a : B) (ht : IsSelfAdjoint t) {M : ℝ}
    (hM : 0 < M) (hleft : ‖kirchbergPath t a (-1)‖ ≤ M)
    (hright : ‖kirchbergPath t a 1‖ ≤ M) {z : ℂ}
    (hz : -1 ≤ z.re ∧ z.re ≤ 1) : ‖kirchbergPath t a z‖ ≤ M := by
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := kirchbergPath t a) (a := M) (b := M) (by norm_num : (-1 : ℝ) < 1)
    hz (differentiable_kirchbergPath t a).diffContOnCl
    (kirchbergPath_strip_bddAbove t a ht) ?_ ?_
  · simpa only [← Real.rpow_add hM, sub_add_cancel, Real.rpow_one] using h
  · intro w hw
    rw [kirchbergPath_norm_re t a ht, show w.re = -1 from hw]
    simpa only [Complex.ofReal_neg, Complex.ofReal_one] using hleft
  · intro w hw
    rw [kirchbergPath_norm_re t a ht, show w.re = 1 from hw]
    exact hright

/-- Schwarz's lemma gives the scalar derivation bound on page 60. -/
theorem norm_commutator_le_of_kirchberg_bound (t a : B) (ht : IsSelfAdjoint t)
    {M : ℝ} (hM : 0 < M) (hleft : ‖kirchbergPath t a (-1)‖ ≤ M)
    (hright : ‖kirchbergPath t a 1‖ ≤ M) :
    ‖t * a - a * t‖ ≤ M + ‖a‖ := by
  have hmap : MapsTo (kirchbergPath t a) (Metric.ball 0 1)
      (Metric.closedBall (kirchbergPath t a 0) (M + ‖a‖)) := by
    intro z hz
    have hnz : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hre : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans hnz.le
    rw [Metric.mem_closedBall, dist_eq_norm, kirchbergPath_zero]
    exact (norm_sub_le _ _).trans (add_le_add
      (kirchbergPath_norm_le t a ht hM hleft hright (abs_le.mp hre)) le_rfl)
  have h := Complex.norm_deriv_le_div_of_mapsTo_ball
    (differentiable_kirchbergPath t a).differentiableOn hmap (by norm_num : (0 : ℝ) < 1)
  rw [(kirchbergPath_hasDerivAt_zero t a).deriv, div_one] at h
  simpa only [← neg_sub (a * t) (t * a), norm_neg] using h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_KirchbergScalarDerivation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kirchberg's scalar commutator bound for an exponential similarity of
a star representation. This is the estimate before equation (2), p. 61. -/

noncomputable section
namespace KadisonSimilarity

open NormedSpace

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem star_kirchbergPath_one (t : B) (ht : IsSelfAdjoint t) (a : B) :
    star (kirchbergPath t (star a) 1) = kirchbergPath t a (-1) := by
  simp [kirchbergPath, star_mul, NormedSpace.star_exp, ht.star_eq, mul_assoc]

/-- A bound for the positive endpoint also bounds the negative endpoint,
because the source representation preserves adjoints. -/
theorem kirchberg_commutator_bound (σ : A →⋆ₐ[ℂ] B) (t : B)
    (ht : IsSelfAdjoint t) {M : ℝ} (hM : 0 < M)
    (hπ : ∀ a : A, ‖kirchbergPath t (σ a) 1‖ ≤ M * ‖a‖) (a : A) :
    ‖t * σ a - σ a * t‖ ≤ (M + 1) * ‖a‖ := by
  by_cases ha : a = 0
  · simp [ha]
  have hMa : 0 < M * ‖a‖ := mul_pos hM (norm_pos_iff.mpr ha)
  have hleft : ‖kirchbergPath t (σ a) (-1)‖ ≤ M * ‖a‖ := by
    rw [← star_kirchbergPath_one t ht (σ a), norm_star, ← map_star]
    simpa only [norm_star] using hπ (star a)
  exact (norm_commutator_le_of_kirchberg_bound t (σ a) ht hMa hleft (hπ a)).trans
    (by nlinarith [NonUnitalStarAlgHom.norm_apply_le σ a])

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_KirchbergUniformBound
attribute [-instance] _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quantitative conclusion of Kirchberg's Proposition 1: a uniform
complete bound for those homomorphisms already known to be similar. -/

noncomputable section
namespace KadisonSimilarity
open NormedSpace

universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kirchberg_uniform_completeBound {C : ℝ} (hC : 0 ≤ C)
    (estimate : UniformCommutatorEstimate.{v} C) (π : BoundedUnitalHom A H)
    {M : ℝ} (hM : 0 < M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖)
    (hcb : IsCompletelyBounded π.1) :
    CompleteBound π.1 (Real.exp (C * (M + 1))) := by
  obtain ⟨t, σ, ht, he, hK⟩ := exists_exponential_similarity π hcb
  let P := representationVonNeumannAlgebra σ
  have hscalar : scalarCommutatorNorm P t ≤ M + 1 := by
    apply scalarKaplanskyClosure_of_twoVector σ P (twoVectorKaplanskyInput σ)
      t (M + 1) (by positivity)
    intro a
    apply kirchberg_commutator_bound σ t ht hM
    intro b
    simpa only [kirchbergPath, one_smul] using (he b ▸ hπ b)
  have hd : CompleteBound (fun a => commutator t (σ a)) (C * (M + 1)) := by
    intro n X
    exact (completeBound_commutator_of_estimate P hC (estimate H P) σ
      (mem_representationVonNeumannAlgebra σ) t n X).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscalar hC) (norm_nonneg _))
  have hk := kirchberg_completeNorm_le_exp π t σ ht he hK (by positivity) hd
  intro n X
  exact (completeBound_completeNorm hcb n X).trans
    (mul_le_mul_of_nonneg_right hk (norm_nonneg _))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_KirchbergEndgame
attribute [-instance] _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseCompression_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_left_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_vector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator_adjoint _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerInto_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightTransferBack_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightTransferMap_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightTransfer_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.hilbertArrayFlatten_apply _root_.OAI.KadisonSimilarity.hilbertFourfoldFlatten_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.hilbertTripleFlatten_apply _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.invariantStarRepresentation_apply _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.matrixLeftArray_apply _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberAction_coe _root_.OAI.KadisonSimilarity.projectionFiberCompression_coe _root_.OAI.KadisonSimilarity.projectionFiberRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_inclusion _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.unitizationRangeRepresentation_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haagerup's finite cyclic reduction completes Kirchberg's Proposition 1.
Each finite matrix test vector generates an invariant subspace on which the
representation is similar. The uniform bound on these restrictions therefore
bounds every amplification of the original bounded homomorphism. -/

noncomputable section
namespace KadisonSimilarity

universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem completeBound_of_uniformCommutator {C : ℝ} (hC : 0 ≤ C)
    (estimate : UniformCommutatorEstimate.{v} C) (π : BoundedUnitalHom A H)
    {M : ℝ} (hM : 0 < M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖) :
    CompleteBound π.1 (Real.exp (C * (M + 1))) := by
  intro n X
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro ξ
  by_cases hn : 0 < n
  · let E := finiteOrbitSubspace π (fun i => ξ i)
    let ρ := restrictBoundedHom π E (finiteOrbitSubspace_invariant π (fun i => ξ i))
    obtain ⟨S, hS⟩ := finiteOrbitSubspace_similar π hn (fun i => ξ i)
    have hcb : IsCompletelyBounded ρ.1 :=
      ⟨_, mul_nonneg (norm_nonneg _) (norm_nonneg _), completeBound_of_similarity ρ S hS⟩
    have hb := kirchberg_uniform_completeBound hC estimate ρ hM
      (restrictBoundedHom_bound π E (finiteOrbitSubspace_invariant π (fun i => ξ i))
        (le_of_lt hM) hπ) hcb n X
    let η : HilbertCopies E n := WithLp.toLp 2 (finiteOrbitGenerators π (fun i => ξ i))
    have hη : ‖η‖ = ‖ξ‖ := by
      have he : ‖η‖ ^ 2 = ‖ξ‖ ^ 2 := by
        simp only [PiLp.norm_sq_eq_of_L2, η, finiteOrbitGenerators]
        rfl
      nlinarith [norm_nonneg η, norm_nonneg ξ]
    have he (i : Fin n) :
        ((matrixOperator (X.map ρ.1) η i : E) : H) =
          matrixOperator (X.map π.1) ξ i := by
      simp [matrixOperator_apply, ρ, η, finiteOrbitGenerators, restrictBoundedHom_apply]
    have hnorm : ‖matrixOperator (X.map ρ.1) η‖ = ‖matrixOperator (X.map π.1) ξ‖ := by
      have hs : ‖matrixOperator (X.map ρ.1) η‖ ^ 2 =
          ‖matrixOperator (X.map π.1) ξ‖ ^ 2 := by
        simp only [PiLp.norm_sq_eq_of_L2]
        apply Finset.sum_congr rfl
        intro i _
        rw [← he i]
        rfl
      nlinarith [norm_nonneg (matrixOperator (X.map ρ.1) η),
        norm_nonneg (matrixOperator (X.map π.1) ξ)]
    calc
      ‖matrixOperator (X.map π.1) ξ‖ = ‖matrixOperator (X.map ρ.1) η‖ := hnorm.symm
      _ ≤ ‖matrixOperator (X.map ρ.1)‖ * ‖η‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (Real.exp (C * (M + 1)) * ‖CStarMatrix.ofMatrix X‖) * ‖ξ‖ := by
        rw [hη]
        exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  · have hn0 : n = 0 := by omega
    subst n
    have hξ : ξ = 0 := Subsingleton.elim _ _
    simp [hξ]

/-- Uniform commutator control implies similarity for every bounded unital
homomorphism, including those not initially known to be completely bounded. -/
theorem similarity_of_uniformCommutator {C : ℝ} (hC : 0 ≤ C)
    (estimate : UniformCommutatorEstimate.{v} C) (π : BoundedUnitalHom A H) :
    SimilarToStar A H π := by
  let f : A →L[ℂ] (H →L[ℂ] H) := ⟨π.1.toLinearMap, π.2⟩
  have hb : ∀ a, ‖π.1 a‖ ≤ (‖f‖ + 1) * ‖a‖ := by
    intro a
    exact (f.le_opNorm a).trans (by nlinarith [norm_nonneg a])
  obtain ⟨S, _, hS⟩ := paulsenSimilarityInput π (Real.exp (C * ((‖f‖ + 1) + 1)))
    (le_of_lt (Real.exp_pos _))
    (completeBound_of_uniformCommutator hC estimate π (by positivity) hb)
  exact ⟨S, hS⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_UnconditionalSimilarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The universal commutator estimate and finite cyclic reduction imply
similarity for every bounded unital representation. -/

noncomputable section
namespace KadisonSimilarity

universe u v

/-- Theorem `thm:similarity`: every bounded unital complex-algebra
representation of a unital C-star algebra is similar to a star representation. -/
theorem similarityTheorem_oai : SimilarityTheorem.{u,v} := by
  intro A _ H _ _ _ π
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  have : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  exact similarity_of_uniformCommutator (le_of_lt universalConstant_pos)
    uniformCommutatorEstimate π

end KadisonSimilarity

end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.KadisonSimilarity.similarityTheorem_oai.{u, v} := @OAI.KadisonSimilarity.similarityTheorem_oai.{u, v}
