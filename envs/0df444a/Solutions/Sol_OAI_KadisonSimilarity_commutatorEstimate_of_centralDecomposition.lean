-- Prove2me | solution 1 for OAI.KadisonSimilarity.commutatorEstimate_of_centralDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T15:02:36.633982+00:00
-- url     : https://prove2.me/submissions/9a026f11-c7d7-4219-9f1b-55ddc6d8df0d

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A018
import Definitions.Def_OAIQ075A033
import Theorems.Thm_OAI_KadisonSimilarity_FiniteFactorModel_estimate

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

theorem finiteFactorConstant_le : 3 * cornerConstant + 2 ≤ factorConstant :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem infiniteFactorConstant_le : 1 + 2 * rowConstant ≤ factorConstant :=
  (le_max_right _ _).trans (le_max_left _ _)

theorem two_le_factorConstant : 2 ≤ factorConstant := le_max_right _ _

theorem factorConstant_pos : 0 < factorConstant := lt_of_lt_of_le (by norm_num) two_le_factorConstant

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_OperatorAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete operators for Kadison similarity

These definitions use bounded operators on the actual Hilbert space, and similarity
uses a unit of that bounded-operator algebra.  The compression estimate is the
operator calculation in Lemma `lem:compressed-commutator` of the manuscript.
-/

noncomputable section

namespace KadisonSimilarity

section Commutators

variable {R : Type*} [NormedRing R]

theorem commutator_sub_left (S T U : R) :
    commutator (S - T) U = commutator S U - commutator T U := by
  simp only [commutator, sub_mul, mul_sub]
  abel

/-- Replacing an operator changes a commutator by at most twice its norm change. -/
theorem norm_commutator_le (S T : R) :
    ‖commutator S T‖ ≤ 2 * ‖S‖ * ‖T‖ := by
  calc
    ‖commutator S T‖ ≤ ‖S * T‖ + ‖T * S‖ := norm_sub_le _ _
    _ ≤ ‖S‖ * ‖T‖ + ‖T‖ * ‖S‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖S‖ * ‖T‖ := by ring

theorem norm_commutator_sub_le (S T U : R) :
    ‖commutator S U - commutator T U‖ ≤ 2 * ‖S - T‖ * ‖U‖ := by
  rw [← commutator_sub_left]
  exact norm_commutator_le _ _

/-- The perturbation estimate used when restoring the original operator after averaging. -/
theorem norm_commutator_le_of_approx (S T U : R) {a d : ℝ}
    (hT : ‖commutator T U‖ ≤ a) (hST : ‖S - T‖ ≤ d) :
    ‖commutator S U‖ ≤ a + 2 * d * ‖U‖ := by
  calc
    ‖commutator S U‖ ≤ ‖commutator T U‖ + ‖commutator S U - commutator T U‖ :=
      norm_le_insert' _ _
    _ ≤ a + 2 * ‖S - T‖ * ‖U‖ := add_le_add hT (norm_commutator_sub_le _ _ _)
    _ ≤ a + 2 * d * ‖U‖ := by gcongr

end Commutators

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
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_WeakOperatorCompactness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak-operator compactness of a norm ball, obtained from compact scalar
matrix-coefficient discs and the Hilbert-space representation of bounded forms. -/

noncomputable section
namespace KadisonSimilarity

open scoped Topology
open ContinuousLinearMapWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem norm_operatorOfForm_le (f : H → H → ℂ) (hf : IsOperatorForm f) (R : ℝ)
    (hR : 0 ≤ R) (hb : ∀ x y, ‖f x y‖ ≤ R * ‖x‖ * ‖y‖) :
    ‖operatorOfForm f hf R hb‖ ≤ R := by
  apply norm_le_of_matrix_coefficients _ hR
  intro x y
  rw [← norm_inner_symm, operatorOfForm_inner]
  convert hb x y using 1
  all_goals try with_reducible_and_instances rfl
  ring

omit [CompleteSpace H] in
private theorem isClosed_operatorForms : IsClosed {f : H → H → ℂ | IsOperatorForm f} := by
  have hc (x y : H) : Continuous (fun f : H → H → ℂ => f x y) :=
    (continuous_apply y).comp (continuous_apply x)
  unfold IsOperatorForm
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
  · refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z => ?_
    exact isClosed_eq (hc (x + y) z) ((hc x z).add (hc y z))
  · refine isClosed_iInter fun c => isClosed_iInter fun x => isClosed_iInter fun y => ?_
    exact isClosed_eq (hc (c • x) y) (continuous_const.mul (hc x y))
  · refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z => ?_
    exact isClosed_eq (hc x (y + z)) ((hc x y).add (hc x z))
  · refine isClosed_iInter fun c => isClosed_iInter fun x => isClosed_iInter fun y => ?_
    exact isClosed_eq (hc x (c • y)) (continuous_const.mul (hc x y))

omit [CompleteSpace H] in
private theorem isCompact_boundedOperatorForms (R : ℝ) :
    IsCompact (boundedOperatorForms (H := H) R) := by
  have hd : IsCompact {f : H → H → ℂ | ∀ x y, f x y ∈ Metric.closedBall 0 (R * ‖x‖ * ‖y‖)} :=
    isCompact_pi_infinite fun x => isCompact_pi_infinite fun y => isCompact_closedBall _ _
  have he : boundedOperatorForms (H := H) R =
      {f | IsOperatorForm f} ∩ {f : H → H → ℂ | ∀ x y,
        f x y ∈ Metric.closedBall 0 (R * ‖x‖ * ‖y‖)} := by
    ext f
    simp [boundedOperatorForms, Metric.mem_closedBall, dist_zero_right]
  rw [he]
  exact hd.inter_left isClosed_operatorForms

private theorem continuous_boundedFormOperator (R : ℝ) :
    Continuous (boundedFormOperator (H := H) R) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro x y
  have he : (fun f : boundedOperatorForms (H := H) R =>
      inner ℂ y (boundedFormOperator R f x)) =
      fun f => star (f.val x y) := by
    funext f
    change inner ℂ y (operatorOfForm f.val f.property.1 R f.property.2 x) = _
    rw [← inner_conj_symm, operatorOfForm_inner]
    rfl
  rw [he]
  have hc : Continuous (fun f : H → H → ℂ => f x y) :=
    (continuous_apply y).comp (continuous_apply x)
  exact (hc.comp continuous_subtype_val).star

/-- The closed norm ball in bounded operators on a Hilbert space is compact
in the weak-operator topology. -/
theorem isCompact_weakOperator_ball (R : ℝ) (hR : 0 ≤ R) :
    IsCompact {T : H →WOT[ℂ] H | ‖toCLM T‖ ≤ R} := by
  let : CompactSpace (boundedOperatorForms (H := H) R) :=
    isCompact_iff_compactSpace.mp (isCompact_boundedOperatorForms R)
  have himage : Set.range (boundedFormOperator (H := H) R) =
      {T : H →WOT[ℂ] H | ‖toCLM T‖ ≤ R} := by
    ext T
    constructor
    · rintro ⟨f, rfl⟩
      exact norm_operatorOfForm_le f.val f.property.1 R hR f.property.2
    · intro hT
      let f : H → H → ℂ := fun x y => inner ℂ (T x) y
      have hf : IsOperatorForm f := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro x y z; simp [f, inner_add_left]
        · intro c x y; simp [f, inner_smul_left, mul_comm]
        · intro x y z; simp [f, inner_add_right]
        · intro c x y; simp [f, inner_smul_right]
      have hb : ∀ x y, ‖f x y‖ ≤ R * ‖x‖ * ‖y‖ := by
        intro x y
        calc
          ‖f x y‖ ≤ ‖T x‖ * ‖y‖ := norm_inner_le_norm _ _
          _ ≤ (‖toCLM T‖ * ‖x‖) * ‖y‖ :=
            mul_le_mul_of_nonneg_right ((toCLM T).le_opNorm x) (norm_nonneg y)
          _ ≤ R * ‖x‖ * ‖y‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hT (norm_nonneg x)) (norm_nonneg y)
      refine ⟨⟨f, hf, hb⟩, ?_⟩
      apply ContinuousLinearMapWOT.ext_inner
      intro x y
      change inner ℂ y (operatorOfForm f hf R hb x) = inner ℂ y (T x)
      rw [← inner_conj_symm, operatorOfForm_inner]
      exact inner_conj_symm _ _
  rw [← himage]
  exact isCompact_range (continuous_boundedFormOperator R)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FiniteSymmetrization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite unitary averaging and weak-operator cluster points. These are the
analytic and algebraic symmetrization steps, before identifying the matrix
unitaries of the free-product model. -/

noncomputable section
namespace KadisonSimilarity

open scoped Topology
open Filter ContinuousLinearMapWOT

variable {Γ V H : Type*} [Fintype Γ] [Nonempty Γ]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

omit [Nonempty Γ] in
theorem finiteMean_sub (f g : Γ → V) :
    finiteMean (fun a => f a - g a) = finiteMean f - finiteMean g := by
  simp [finiteMean, Finset.sum_sub_distrib, smul_sub]

theorem norm_finiteMean_le (f : Γ → V) {c : ℝ} (hc : ∀ g, ‖f g‖ ≤ c) :
    ‖finiteMean f‖ ≤ c := by
  have hcard : (0 : ℝ) < Fintype.card Γ := Nat.cast_pos.mpr Fintype.card_pos
  calc
    ‖finiteMean f‖ = (Fintype.card Γ : ℝ)⁻¹ * ‖∑ g, f g‖ := by
      simp [finiteMean, norm_smul]
    _ ≤ (Fintype.card Γ : ℝ)⁻¹ * ∑ g, ‖f g‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (Fintype.card Γ : ℝ)⁻¹ * ((Fintype.card Γ : ℝ) * c) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa using Finset.sum_le_sum (fun g (_ : g ∈ (Finset.univ : Finset Γ)) => hc g)
    _ = c := by field_simp

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [Group Γ]

omit [Fintype Γ] [Nonempty Γ] in
private theorem representation_mul_inv (U : Γ →* (H →L[ℂ] H)) (g : Γ) :
    U g * U g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]

omit [Fintype Γ] [Nonempty Γ] in
private theorem representation_inv_mul (U : Γ →* (H →L[ℂ] H)) (g : Γ) :
    U g⁻¹ * U g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]

/-- Contractivity of finite averaging of unitary conjugates. -/
theorem norm_finiteTwirl_le (U : Γ →* (H →L[ℂ] H))
    (hU : ∀ g, ‖U g‖ ≤ 1) (T : H →L[ℂ] H) : ‖finiteTwirl U T‖ ≤ ‖T‖ := by
  apply norm_finiteMean_le
  intro g
  calc
    ‖U g * T * U g⁻¹‖ ≤ ‖U g‖ * ‖T‖ * ‖U g⁻¹‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖T‖ * 1 := by gcongr; exact hU _; exact hU _
    _ = ‖T‖ := by ring

omit [Nonempty Γ] in
/-- Reindexing the finite group proves exact invariance under its unitaries. -/
theorem finiteTwirl_conjugate (U : Γ →* (H →L[ℂ] H)) (T : H →L[ℂ] H) (g : Γ) :
    U g * finiteTwirl U T * U g⁻¹ = finiteTwirl U T := by
  simp only [finiteTwirl, finiteMean, mul_smul_comm, smul_mul_assoc,
    Finset.mul_sum, Finset.sum_mul]
  congr 1
  calc
    ∑ h, U g * (U h * T * U h⁻¹) * U g⁻¹ =
        ∑ h, U (g * h) * T * U (g * h)⁻¹ := by
      apply Finset.sum_congr rfl
      intro h _
      simp only [mul_inv_rev, map_mul]
      noncomm_ring
    _ = ∑ h, U h * T * U h⁻¹ :=
      Equiv.sum_comp (Equiv.mulLeft g) (fun h => U h * T * U h⁻¹)

omit [Nonempty Γ] in
/-- The averaged operator commutes with every unitary in the finite group. -/
theorem finiteTwirl_commute (U : Γ →* (H →L[ℂ] H)) (T : H →L[ℂ] H) (g : Γ) :
    commutator (finiteTwirl U T) (U g) = 0 := by
  have h := congrArg (fun X : H →L[ℂ] H => X * U g) (finiteTwirl_conjugate U T g)
  simp only [mul_assoc, representation_inv_mul, mul_one] at h
  exact sub_eq_zero.mpr h.symm

/-- A bound on the original commutators bounds the distance to the twirl. -/
theorem norm_sub_finiteTwirl_le (U : Γ →* (H →L[ℂ] H))
    (hU : ∀ g, ‖U g‖ ≤ 1) (T : H →L[ℂ] H) {ε : ℝ}
    (hcomm : ∀ g, ‖commutator T (U g)‖ ≤ ε) : ‖T - finiteTwirl U T‖ ≤ ε := by
  have he : T - finiteTwirl U T =
      finiteMean (fun g => (commutator T (U g)) * U g⁻¹) := by
    change T - finiteMean (fun g => U g * T * U g⁻¹) = _
    calc
      _ = finiteMean (fun _ : Γ => T) - finiteMean (fun g => U g * T * U g⁻¹) := by
        rw [finiteMean_const]
      _ = finiteMean (fun g => T - U g * T * U g⁻¹) := (finiteMean_sub _ _).symm
      _ = _ := ?_
    congr 1
    funext g
    simp only [commutator, sub_mul, mul_assoc, representation_mul_inv, mul_one]
  rw [he]
  apply norm_finiteMean_le
  intro g
  calc
    ‖commutator T (U g) * U g⁻¹‖ ≤ ‖commutator T (U g)‖ * ‖U g⁻¹‖ := norm_mul_le _ _
    _ ≤ ε * 1 := by
      apply mul_le_mul (hcomm g) (hU _) (norm_nonneg _) ?_
      exact (norm_nonneg _).trans (hcomm g)
    _ = ε := mul_one _

variable [CompleteSpace H]

/-- Every bounded sequence of operators has a weak-operator cluster point,
without a separability assumption on the Hilbert space. -/
theorem exists_weakOperator_cluster (T : ℕ → H →L[ℂ] H) {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ n, ‖T n‖ ≤ R) :
    ∃ S : H →L[ℂ] H, ‖S‖ ≤ R ∧ MapClusterPt (ofCLM S) atTop (fun n => ofCLM (T n)) := by
  have hev : ∀ᶠ n : ℕ in atTop, ofCLM (T n) ∈
      {B : H →WOT[ℂ] H | ‖toCLM B‖ ≤ R} := Eventually.of_forall hbound
  obtain ⟨S, hS, hcluster⟩ :=
    (isCompact_weakOperator_ball (H := H) R hR).exists_mapClusterPt_of_frequently hev.frequently
  exact ⟨toCLM S, hS, hcluster⟩

/-- Operator-norm bounds on affine expressions pass to weak cluster points. -/
theorem norm_sub_le_of_weakOperator_cluster (T : ℕ → H →L[ℂ] H)
    (S A : H →L[ℂ] H)
    (hcluster : MapClusterPt (ofCLM S) atTop (fun n => ofCLM (T n)))
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ᶠ n in atTop, ‖T n - A‖ ≤ c) : ‖S - A‖ ≤ c := by
  have hclosed : IsClosed {B : H →WOT[ℂ] H | ‖toCLM B - A‖ ≤ c} :=
    (isCompact_weakOperator_ball (H := H) c hc).isClosed.preimage
      (continuous_id.sub continuous_const)
  exact hclosed.mem_of_mapClusterPt hcluster hbound

/-- Eventual commutator bounds pass to weak cluster points. -/
theorem norm_commutator_le_of_weakOperator_cluster (T : ℕ → H →L[ℂ] H)
    (S A : H →L[ℂ] H)
    (hcluster : MapClusterPt (ofCLM S) atTop (fun n => ofCLM (T n)))
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ᶠ n in atTop, ‖commutator (T n) A‖ ≤ c) :
    ‖commutator S A‖ ≤ c := by
  have hclosed : IsClosed {B : H →WOT[ℂ] H | ‖commutator (toCLM B) A‖ ≤ c} :=
    (isCompact_weakOperator_ball (H := H) c hc).isClosed.preimage
      ((continuous_id.mul_const (ofCLM A)).sub (continuous_id.const_mul (ofCLM A)))
  exact hclosed.mem_of_mapClusterPt hcluster hbound

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_WeakOperatorIntegral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak operator integrals built from scalar integrals. In particular this
permits averaging a strongly continuous unitary action without assuming
continuity in the operator norm. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory ContinuousLinearMap

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure X) [IsProbabilityMeasure μ]

theorem norm_weakOperatorIntegral_le (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ g, ‖A g‖ ≤ R) :
    ‖weakOperatorIntegral μ A hA R hbound‖ ≤ R :=
  norm_operatorOfForm_le _ _ R hR _

/-- Left and right multiplication may be passed through the weak integral. -/
theorem weakOperatorIntegral_sandwich_inner (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) (R : ℝ) (hbound : ∀ g, ‖A g‖ ≤ R)
    (B C : H →L[ℂ] H) (x y : H) :
    inner ℂ ((B * weakOperatorIntegral μ A hA R hbound * C) x) y =
      ∫ g, inner ℂ ((B * A g * C) x) y ∂μ := by
  change inner ℂ (B (weakOperatorIntegral μ A hA R hbound (C x))) y = _
  rw [← adjoint_inner_right, weakOperatorIntegral_inner]
  apply integral_congr_ae
  filter_upwards with g
  exact adjoint_inner_right B (A g (C x)) y

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_HaarSymmetrization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar symmetrization, defined through weak scalar integrals. This applies
to the compact matrix-unitary actions used in the free-product argument. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory ContinuousLinearMap

variable {Γ H K : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (μ : Measure Γ) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]

omit [MeasurableMul Γ] [μ.IsMulLeftInvariant] in
/-- Haar averaging is contractive in operator norm. -/
theorem norm_haarTwirl_le (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (T : H →L[ℂ] H) (hI : WeaklyIntegrable μ (unitaryConjugate U T)) :
    ‖haarTwirl μ U hU T hI‖ ≤ ‖T‖ :=
  norm_weakOperatorIntegral_le μ _ _ _ (norm_nonneg _) _

/-- Left invariance of Haar measure gives invariance of the operator average. -/
theorem haarTwirl_conjugate (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (T : H →L[ℂ] H) (hI : WeaklyIntegrable μ (unitaryConjugate U T)) (g : Γ) :
    U g * haarTwirl μ U hU T hI * U g⁻¹ = haarTwirl μ U hU T hI := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [haarTwirl, weakOperatorIntegral_sandwich_inner, weakOperatorIntegral_inner]
  calc
    _ = ∫ h, inner ℂ (unitaryConjugate U T (g * h) x) y ∂μ := by
      apply integral_congr_ae
      filter_upwards with h
      congr 2
      simp only [unitaryConjugate, mul_inv_rev, map_mul, mul_assoc]
    _ = _ := integral_mul_left_eq_self (μ := μ) (fun h => inner ℂ (unitaryConjugate U T h x) y) g

/-- Thus the Haar average commutes with the whole compact group. -/
theorem haarTwirl_commute (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (T : H →L[ℂ] H) (hI : WeaklyIntegrable μ (unitaryConjugate U T)) (g : Γ) :
    commutator (haarTwirl μ U hU T hI) (U g) = 0 := by
  have hc := congrArg (fun B : H →L[ℂ] H => B * U g) (haarTwirl_conjugate μ U hU T hI g)
  have hi : U g⁻¹ * U g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  simp only [mul_assoc, hi, mul_one] at hc
  exact sub_eq_zero.mpr hc.symm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialHaarPerturbation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative proximity in Haar symmetrization. The finite-factor argument
uses a cluster point within the original scalar commutator bound. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory ContinuousLinearMap Filter ContinuousLinearMapWOT
open scoped Topology

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- A weak integral stays in every operator norm ball containing its field. -/
theorem norm_weakOperatorIntegral_sub_le (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) (R : ℝ) (hbound : ∀ g, ‖A g‖ ≤ R)
    (T : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ) (hclose : ∀ g, ‖A g - T‖ ≤ δ) :
    ‖weakOperatorIntegral μ A hA R hbound - T‖ ≤ δ := by
  apply norm_le_of_matrix_coefficients _ hδ
  intro x y
  rw [← norm_inner_symm]
  have he : inner ℂ ((weakOperatorIntegral μ A hA R hbound - T) x) y =
      ∫ g, inner ℂ ((A g - T) x) y ∂μ := by
    simp only [_root_.sub_apply, inner_sub_left, weakOperatorIntegral_inner]
    rw [integral_sub (hA x y) (integrable_const _), integral_const]
    simp
  rw [he]
  have hb : ∀ᵐ g ∂μ, ‖inner ℂ ((A g - T) x) y‖ ≤ δ * ‖x‖ * ‖y‖ :=
    Eventually.of_forall fun g => calc
      _ ≤ ‖(A g - T) x‖ * ‖y‖ := norm_inner_le_norm _ _
      _ ≤ (‖A g - T‖ * ‖x‖) * ‖y‖ :=
        mul_le_mul_of_nonneg_right ((A g - T).le_opNorm x) (norm_nonneg y)
      _ ≤ δ * ‖x‖ * ‖y‖ := by gcongr; exact hclose g
  have hi := norm_integral_le_of_norm_le_const hb
  simp only [probReal_univ, mul_one] at hi
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ring

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]

omit [MeasurableSpace X] [IsProbabilityMeasure μ] [CompleteSpace H]
  [MeasurableSpace Γ] [MeasurableMul Γ] in
/-- Conjugating by a contractive group representation moves an operator by
at most its commutator with the group element. -/
theorem norm_unitaryConjugate_sub_le (U : Γ →* (H →L[ℂ] H))
    (hU : ∀ g, ‖U g‖ ≤ 1) (T : H →L[ℂ] H) {δ : ℝ}
    (hcomm : ∀ g, ‖commutator T (U g)‖ ≤ δ) (g : Γ) :
    ‖unitaryConjugate U T g - T‖ ≤ δ := by
  have hi : U g * U g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have he : T - unitaryConjugate U T g = commutator T (U g) * U g⁻¹ := by
    simp only [unitaryConjugate, commutator, sub_mul, mul_assoc, hi, mul_one]
  rw [norm_sub_rev, he]
  calc
    _ ≤ ‖commutator T (U g)‖ * ‖U g⁻¹‖ := norm_mul_le _ _
    _ ≤ δ * 1 := mul_le_mul (hcomm g) (hU _) (norm_nonneg _)
      ((norm_nonneg _).trans (hcomm g))
    _ = δ := mul_one _

omit [MeasurableMul Γ] in
/-- The Haar average is close to the original operator by the scalar bound. -/
theorem norm_haarTwirl_sub_le (ν : Measure Γ) [IsProbabilityMeasure ν]
    (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (T : H →L[ℂ] H) (hI : WeaklyIntegrable ν (unitaryConjugate U T))
    {δ : ℝ} (hδ : 0 ≤ δ) (hcomm : ∀ g, ‖commutator T (U g)‖ ≤ δ) :
    ‖haarTwirl ν U hU T hI - T‖ ≤ δ :=
  norm_weakOperatorIntegral_sub_le ν _ hI _ _ T hδ
    (norm_unitaryConjugate_sub_le U hU T hcomm)

/-- The norm perturbation controls the full scalar commutator seminorm. -/
theorem scalarCommutatorNorm_le_of_close (P : VonNeumannAlgebra H)
    (S T : H →L[ℂ] H) {δ : ℝ} (hclose : ‖S - T‖ ≤ δ) :
    scalarCommutatorNorm P S ≤ scalarCommutatorNorm P T + 2 * δ := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hclose
  have hT := scalarCommutatorNorm_nonneg P T
  apply (scalarCommutatorNorm_le_iff P S (by positivity)).mpr
  intro a ha
  have h := norm_commutator_le_of_approx S T a
    (norm_commutator_le_scalarCommutatorNorm P T a ha) hclose
  nlinarith

section IncreasingGroups

variable {G : ℕ → Type*} [∀ n, Group (G n)] [∀ n, MeasurableSpace (G n)]
  [∀ n, MeasurableMul (G n)] (ν : ∀ n, Measure (G n))
  [∀ n, IsProbabilityMeasure (ν n)] [∀ n, (ν n).IsMulLeftInvariant]

/-- Increasing Haar averages give a single invariant operator within the
original commutator bound. There is no invariant operator among the inputs. -/
theorem exists_simultaneously_symmetrized_close
    (U : ∀ n, G n →* (H →L[ℂ] H)) (hU : ∀ n g, ‖U n g‖ ≤ 1)
    (embedding : ∀ n m, n ≤ m → G n → G m)
    (hcompat : ∀ n m h g, U m (embedding n m h g) = U n g)
    (T : H →L[ℂ] H)
    (hI : ∀ n, WeaklyIntegrable (ν n) (unitaryConjugate (U n) T))
    {δ : ℝ} (hδ : 0 ≤ δ) (hcomm : ∀ n g, ‖commutator T (U n g)‖ ≤ δ) :
    ∃ S : H →L[ℂ] H, ‖S‖ ≤ ‖T‖ ∧ ‖S - T‖ ≤ δ ∧
      ∀ n g, commutator S (U n g) = 0 := by
  let averages : ℕ → H →L[ℂ] H := fun n => haarTwirl (ν n) (U n) (hU n) T (hI n)
  obtain ⟨S, hS, hc⟩ := exists_weakOperator_cluster averages (norm_nonneg T)
    (fun n => norm_haarTwirl_le (ν n) (U n) (hU n) T (hI n))
  refine ⟨S, hS, ?_, ?_⟩
  · apply norm_sub_le_of_weakOperator_cluster averages S T hc hδ
    exact Eventually.of_forall fun n =>
      norm_haarTwirl_sub_le (ν n) (U n) (hU n) T (hI n) hδ (hcomm n)
  · intro n g
    apply norm_eq_zero.mp
    apply le_antisymm ?_ (norm_nonneg _)
    apply norm_commutator_le_of_weakOperator_cluster averages S (U n g) hc (le_refl 0)
    filter_upwards [eventually_ge_atTop n] with m hm
    have he := haarTwirl_commute (ν m) (U m) (hU m) T (hI m) (embedding n m hm g)
    rw [hcompat] at he
    simp only [averages, he, norm_zero, le_refl]

/-- The finite-factor averaging step, including the factor-three scalar
commutator bound used before passage to the ultrapower. -/
theorem exists_scalar_symmetrization (P : VonNeumannAlgebra H)
    (U : ∀ n, G n →* (H →L[ℂ] H)) (hU : ∀ n g, ‖U n g‖ ≤ 1)
    (hmem : ∀ n g, U n g ∈ P)
    (embedding : ∀ n m, n ≤ m → G n → G m)
    (hcompat : ∀ n m h g, U m (embedding n m h g) = U n g)
    (T : H →L[ℂ] H)
    (hI : ∀ n, WeaklyIntegrable (ν n) (unitaryConjugate (U n) T)) :
    ∃ S : H →L[ℂ] H, ‖S‖ ≤ ‖T‖ ∧
      ‖S - T‖ ≤ scalarCommutatorNorm P T ∧
      scalarCommutatorNorm P S ≤ 3 * scalarCommutatorNorm P T ∧
      ∀ n g, commutator S (U n g) = 0 := by
  obtain ⟨S, hS, hclose, hc⟩ := exists_simultaneously_symmetrized_close ν U hU
    embedding hcompat T hI (scalarCommutatorNorm_nonneg P T) (fun n g =>
      (norm_commutator_le_scalarCommutatorNorm P T _ (hmem n g)).trans
        (mul_le_of_le_one_right (scalarCommutatorNorm_nonneg P T) (hU n g)))
  refine ⟨S, hS, hclose, ?_, hc⟩
  have hb := scalarCommutatorNorm_le_of_close P S T hclose
  linarith

end IncreasingGroups
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_CompactHaarIntegrability
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong continuity of a unitary action gives every weak Haar integral
used in symmetrization. No continuity in operator norm is required. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory ContinuousLinearMap

variable {Γ H : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] in
/-- Moving the left unitary to the second inner-product slot makes matrix
coefficients of its conjugation action continuous in the strong topology. -/
theorem continuous_unitaryConjugate_coefficient
    (U : Γ →* (H →L[ℂ] H)) (hstar : ∀ g, (U g).adjoint = U g⁻¹)
    (hcont : ∀ x, Continuous (fun g => U g x)) (T : H →L[ℂ] H) (x y : H) :
    Continuous (fun g => inner ℂ (unitaryConjugate U T g x) y) := by
  have he : (fun g => inner ℂ (unitaryConjugate U T g x) y) =
      fun g => inner ℂ (T (U g⁻¹ x)) (U g⁻¹ y) := by
    funext g
    change inner ℂ (U g (T (U g⁻¹ x))) y = _
    rw [← adjoint_inner_right, hstar]
  rw [he]
  exact (T.continuous.comp ((hcont x).comp continuous_inv)).inner
    ((hcont y).comp continuous_inv)

/-- On a compact group these continuous scalar coefficients are integrable
against Haar probability measure. -/
theorem weaklyIntegrable_unitaryConjugate (μ : Measure Γ) [IsFiniteMeasure μ]
    (U : Γ →* (H →L[ℂ] H)) (hstar : ∀ g, (U g).adjoint = U g⁻¹)
    (hcont : ∀ x, Continuous (fun g => U g x)) (T : H →L[ℂ] H) :
    WeaklyIntegrable μ (unitaryConjugate U T) := by
  intro x y
  exact (continuous_unitaryConjugate_coefficient U hstar hcont T x y).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralSteps
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.vonNeumannInnerDerivation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The spectral-step part of the hyperreflexivity deduction

`SpectralStepApproximation` isolates exactly the norm approximation by spectral
projections that the manuscript uses. It is the step-function specialization of
Blackadar, *Operator Algebras* (2006; revised manuscript February 8, 2017),
I.6.1.3--4, with membership of spectral projections from I.9.2.1(iv).
The scalar offset is essential: summation by parts gives a total variation of
the remaining coefficients at most twice the operator norm.

The spectral approximation and the uniform commutator estimate together imply
the hyperreflexivity bound.
-/

noncomputable section

namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The scalar term has zero commutator; the other terms retain their coefficients. -/
theorem commutator_spectralStep (T : H →L[ℂ] H) {n : ℕ}
    (r : ℝ) (c : Fin n → ℝ) (e : Fin n → H →L[ℂ] H) :
    commutator T (spectralStep r c e) = ∑ i, (c i : ℂ) • commutator T (e i) := by
  change innerDerivation T (spectralStep r c e) = _
  simp [spectralStep, map_add, map_sum, innerDerivation_apply, commutator]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CentralSymmetrization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.vonNeumannInnerDerivation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging over finite families of central projections

The finite sign groups and their averages are constructed explicitly. A weak
operator cluster point of the net indexed by finite projection families
commutes with every central projection. The final passage to the whole center
uses only the already stated spectral-step specialization of Blackadar.
-/

noncomputable section
namespace KadisonSimilarity

open Filter ContinuousLinearMapWOT
open scoped Topology Classical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem centralSignRepresentation_mem (P : VonNeumannAlgebra H)
    (s : Finset (CentralProjection P)) (g : s → ℤˣ) :
    centralSignRepresentation P s g ∈ P := by
  exact (MonoidHom.noncommPiCoprod (fun p : s => centralSignHom p.val)
    (fun _ _ _ _ _ => centralUnitary_commute P _ _) g).property.1

private theorem norm_centralSignRepresentation_le (P : VonNeumannAlgebra H)
    (s : Finset (CentralProjection P)) (g : s → ℤˣ) :
    ‖centralSignRepresentation P s g‖ ≤ 1 := by
  let u : unitary (H →L[ℂ] H) :=
    (MonoidHom.noncommPiCoprod (fun p : s => centralSignHom p.val)
      (fun _ _ _ _ _ => centralUnitary_commute P _ _) g).val
  change ‖(u : H →L[ℂ] H)‖ ≤ 1
  have h := CStarRing.norm_coe_unitary_mul u (1 : H →L[ℂ] H)
  simpa only [mul_one] using h.le.trans (IsStarProjection.norm_le 1 (.one _))

private theorem centralSignRepresentation_single (P : VonNeumannAlgebra H)
    (s : Finset (CentralProjection P)) (p : s) :
    centralSignRepresentation P s (Pi.mulSingle p (-1)) = 2 * p.val.val - 1 := by
  classical
  simp only [centralSignRepresentation, MonoidHom.comp_apply]
  simp [centralSignHom, centralReflection]

theorem centralProjectionTwirl_commute (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
    (s : Finset (CentralProjection P)) (p : CentralProjection P) (hp : p ∈ s) :
    commutator (centralProjectionTwirl P Y s) p.val = 0 := by
  classical
  have h := finiteTwirl_commute (centralSignRepresentation P s) Y
    (Pi.mulSingle (⟨p, hp⟩ : s) (-1))
  rw [centralSignRepresentation_single] at h
  change commutator (centralProjectionTwirl P Y s) (2 * p.val - 1) = 0 at h
  have he : commutator (centralProjectionTwirl P Y s) (2 * p.val - 1) =
      (2 : ℂ) • commutator (centralProjectionTwirl P Y s) p.val := by
    simp only [two_mul, commutator, mul_sub, sub_mul, mul_add, add_mul, mul_one, one_mul]
    module
  rw [he] at h
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

/-- Weak-operator compactness applies to arbitrary directed nets. -/
theorem exists_weakOperator_net_cluster {J : Type*} (l : Filter J) [l.NeBot]
    (T : J → H →L[ℂ] H) {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ j, ‖T j‖ ≤ R) :
    ∃ S : H →L[ℂ] H, ‖S‖ ≤ R ∧ MapClusterPt (ofCLM S) l (fun j => ofCLM (T j)) := by
  have hev : ∀ᶠ j in l, ofCLM (T j) ∈
      {B : H →WOT[ℂ] H | ‖toCLM B‖ ≤ R} := Eventually.of_forall hbound
  obtain ⟨S, hS, hcluster⟩ :=
    (isCompact_weakOperator_ball (H := H) R hR).exists_mapClusterPt_of_frequently hev.frequently
  exact ⟨toCLM S, hS, hcluster⟩

theorem norm_sub_le_of_weakOperator_net_cluster {J : Type*} {l : Filter J}
    (T : J → H →L[ℂ] H) (S A : H →L[ℂ] H)
    (hcluster : MapClusterPt (ofCLM S) l (fun j => ofCLM (T j)))
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ᶠ j in l, ‖T j - A‖ ≤ c) : ‖S - A‖ ≤ c := by
  have hclosed : IsClosed {B : H →WOT[ℂ] H | ‖toCLM B - A‖ ≤ c} :=
    (isCompact_weakOperator_ball (H := H) c hc).isClosed.preimage
      (continuous_id.sub continuous_const)
  exact hclosed.mem_of_mapClusterPt hcluster hbound

theorem norm_commutator_le_of_weakOperator_net_cluster {J : Type*} {l : Filter J}
    (T : J → H →L[ℂ] H) (S A : H →L[ℂ] H)
    (hcluster : MapClusterPt (ofCLM S) l (fun j => ofCLM (T j)))
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ᶠ j in l, ‖commutator (T j) A‖ ≤ c) :
    ‖commutator S A‖ ≤ c := by
  have hclosed : IsClosed {B : H →WOT[ℂ] H | ‖commutator (toCLM B) A‖ ≤ c} :=
    (isCompact_weakOperator_ball (H := H) c hc).isClosed.preimage
      ((continuous_id.mul_const (ofCLM A)).sub (continuous_id.const_mul (ofCLM A)))
  exact hclosed.mem_of_mapClusterPt hcluster hbound

/-- No countability assumption is needed: finite sign averages have a
common weak cluster point commuting with every central projection. -/
theorem exists_central_projection_symmetrization (P : VonNeumannAlgebra H)
    (Y : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : scalarCommutatorNorm P Y ≤ δ) :
    ∃ Y₁ : H →L[ℂ] H, ‖Y₁‖ ≤ ‖Y‖ ∧ ‖Y₁ - Y‖ ≤ δ ∧
      (∀ p : CentralProjection P, commutator Y₁ p.val = 0) := by
  let T := centralProjectionTwirl P Y
  have hnorm s : ‖T s‖ ≤ ‖Y‖ :=
    norm_finiteTwirl_le _ (norm_centralSignRepresentation_le P s) Y
  obtain ⟨Y₁, hY₁, hcluster⟩ := exists_weakOperator_net_cluster
    (atTop : Filter (Finset (CentralProjection P))) T (norm_nonneg Y) hnorm
  refine ⟨Y₁, hY₁, ?_, ?_⟩
  · apply norm_sub_le_of_weakOperator_net_cluster T Y₁ Y hcluster hδ
    apply Eventually.of_forall
    intro s
    rw [norm_sub_rev]
    apply norm_sub_finiteTwirl_le _ (norm_centralSignRepresentation_le P s)
    intro g
    calc
      ‖commutator Y (centralSignRepresentation P s g)‖ ≤
          scalarCommutatorNorm P Y * ‖centralSignRepresentation P s g‖ :=
        norm_commutator_le_scalarCommutatorNorm P Y _ (centralSignRepresentation_mem P s g)
      _ ≤ δ * 1 := mul_le_mul hscalar (norm_centralSignRepresentation_le P s g)
        (norm_nonneg _) hδ
      _ = δ := mul_one _
  · intro p
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    apply norm_commutator_le_of_weakOperator_net_cluster T Y₁ p.val hcluster le_rfl
    filter_upwards [eventually_ge_atTop ({p} : Finset (CentralProjection P))] with s hs
    have hp : p ∈ s := hs (Finset.mem_singleton_self p)
    simp only [T, centralProjectionTwirl_commute P Y s p hp, norm_zero, le_refl]

/-- Norm approximation by spectral steps extends projection commutation to
commutation with the whole von Neumann algebra. -/
theorem commutator_zero_of_spectralSteps (C : VonNeumannAlgebra H)
    (approximation : SpectralStepApproximation C) (T : H →L[ℂ] H)
    (hprojection : ∀ p : H →L[ℂ] H, p ∈ C → IsStarProjection p → commutator T p = 0) :
    ∀ a : H →L[ℂ] H, a ∈ C → commutator T a = 0 := by
  have hself (a : H →L[ℂ] H) (ha : a ∈ C) (has : star a = a) :
      commutator T a = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    apply le_of_forall_pos_le_add
    intro ε hε
    let η := ε / (2 * ‖T‖ + 1)
    have hη : 0 < η := by dsimp [η]; positivity
    obtain ⟨n, r, c, e, he, _, herr⟩ := approximation a ha has η hη
    have hstep : commutator T (spectralStep r c e) = 0 := by
      rw [commutator_spectralStep]
      apply Finset.sum_eq_zero
      intro i _
      rw [hprojection (e i) (he i).1 ⟨(he i).2.2, (he i).2.1⟩, smul_zero]
    have heq : commutator T a = commutator T (a - spectralStep r c e) := by
      change innerDerivation T a = innerDerivation T (a - spectralStep r c e)
      rw [map_sub]
      change commutator T a = commutator T a - commutator T (spectralStep r c e)
      rw [hstep, sub_zero]
    have hηε : 2 * ‖T‖ * η ≤ ε := by
      have hden : 0 < 2 * ‖T‖ + 1 := by positivity
      dsimp [η]
      rw [← mul_div_assoc, div_le_iff₀ hden]
      nlinarith
    calc
      ‖commutator T a‖ = ‖commutator T (a - spectralStep r c e)‖ := congrArg norm heq
      _ ≤ 2 * ‖T‖ * ‖a - spectralStep r c e‖ := norm_commutator_le _ _
      _ ≤ 2 * ‖T‖ * η := mul_le_mul_of_nonneg_left herr (by positivity)
      _ ≤ 0 + ε := by simpa only [zero_add] using hηε
  intro a ha
  have hstar : star a ∈ C := star_mem ha
  let b : H →L[ℂ] H := realPart a
  let c : H →L[ℂ] H := imaginaryPart a
  have hb : b ∈ C := by
    dsimp [b]
    rw [realPart_apply_coe, ← Complex.coe_smul]
    exact C.toStarSubalgebra.smul_mem (C.add_mem ha hstar) _
  have hc : c ∈ C := by
    dsimp [c]
    rw [imaginaryPart_apply_coe, ← Complex.coe_smul]
    exact C.toStarSubalgebra.smul_mem
      (C.toStarSubalgebra.smul_mem (C.sub_mem ha hstar) _) _
  change innerDerivation T a = 0
  rw [← realPart_add_I_smul_imaginaryPart a, map_add, map_smul]
  change commutator T b + Complex.I • commutator T c = 0
  rw [hself b hb (realPart a).property, hself c hc (imaginaryPart a).property,
    smul_zero, add_zero]

/-- Central averaging for the global reduction. The only published input
is spectral approximation inside the actual center; the average, its norm
control, and its exact central commutation are all constructed above. -/
theorem exists_central_symmetrization (P : VonNeumannAlgebra H)
    (approximation : SpectralStepApproximation (vonNeumannCenter P))
    (Y : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : scalarCommutatorNorm P Y ≤ δ) :
    ∃ Y₁ : H →L[ℂ] H, ‖Y₁‖ ≤ ‖Y‖ ∧ ‖Y₁ - Y‖ ≤ δ ∧
      scalarCommutatorNorm P Y₁ ≤ 3 * δ ∧
      ∀ a : H →L[ℂ] H, a ∈ vonNeumannCenter P → commutator Y₁ a = 0 := by
  obtain ⟨Y₁, hnorm, hclose, hprojection⟩ :=
    exists_central_projection_symmetrization P Y hδ hscalar
  refine ⟨Y₁, hnorm, hclose, ?_, ?_⟩
  · apply (scalarCommutatorNorm_le_iff P Y₁ (by positivity)).mpr
    intro a ha
    calc
      ‖commutator Y₁ a‖ ≤ scalarCommutatorNorm P Y * ‖a‖ + 2 * δ * ‖a‖ :=
        norm_commutator_le_of_approx Y₁ Y a
          (norm_commutator_le_scalarCommutatorNorm P Y a ha) hclose
      _ ≤ δ * ‖a‖ + 2 * δ * ‖a‖ := by gcongr
      _ = (3 * δ) * ‖a‖ := by ring
  · apply commutator_zero_of_spectralSteps (vonNeumannCenter P) approximation Y₁
    intro p hp hps
    exact hprojection ⟨p, hp, hps⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CountableFiberTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One conull set for the scalar fiber estimates

A countable family of contraction tests gives a common conull set. Weak
operator density then extends the bound to every contraction in each fiber.
This is the countability step in the central-decomposition argument; the
existence and density of the measurable sections remain explicit data.
-/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMapWOT MeasureTheory Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A commutator bound extends from a set of operators to its weak closure. -/
theorem commutator_bound_of_weak_closure (Y T : H →L[ℂ] H)
    (S : Set (H →L[ℂ] H)) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ X ∈ S, ‖commutator Y X‖ ≤ c)
    (hT : ofCLM T ∈ closure (ofCLM '' S)) : ‖commutator Y T‖ ≤ c := by
  have hclosed : IsClosed {X : H →WOT[ℂ] H | ‖commutator Y (toCLM X)‖ ≤ c} := by
    exact (isCompact_weakOperator_ball (H := H) c hc).isClosed.preimage
      ((continuous_const_mul (ofCLM Y)).sub (continuous_mul_const (ofCLM Y)))
  apply closure_minimal _ hclosed hT
  rintro X ⟨X, hX, rfl⟩
  exact hbound X hX

/-- Weakly dense contraction tests control the full scalar commutator norm. -/
theorem scalarCommutatorNorm_le_of_weak_dense_tests
    (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
    (test : ℕ → H →L[ℂ] H)
    (hdense : ∀ X : H →L[ℂ] H, X ∈ P → ‖X‖ ≤ 1 →
      ofCLM X ∈ closure (Set.range fun n => ofCLM (test n)))
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ n, ‖commutator Y (test n)‖ ≤ c) :
    scalarCommutatorNorm P Y ≤ c := by
  let : SeminormedAddCommGroup P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  let : NormedSpace ℂ P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hc
  intro x hx
  change ‖commutator Y (x : H →L[ℂ] H)‖ ≤ c
  apply commutator_bound_of_weak_closure Y x (Set.range test) hc
  · rintro _ ⟨n, rfl⟩
    exact hbound n
  · simpa only [Set.range_comp'] using hdense x x.property (le_of_eq hx)

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type*) [∀ a, NormedAddCommGroup (K a)]
  [∀ a, InnerProductSpace ℂ (K a)] [∀ a, CompleteSpace (K a)]

/-- Countably many almost-everywhere test inequalities hold simultaneously.
Density on each remaining fiber gives its full scalar commutator bound. -/
theorem ae_scalarCommutatorNorm_le_of_countable_tests
    (P : ∀ a, VonNeumannAlgebra (K a))
    (Y : ∀ a, K a →L[ℂ] K a) (test : ∀ a, ℕ → K a →L[ℂ] K a)
    (hdense : ∀ᵐ a ∂μ, ∀ X : K a →L[ℂ] K a, X ∈ P a → ‖X‖ ≤ 1 →
      ofCLM X ∈ closure (Set.range fun n => ofCLM (test a n)))
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ n, ∀ᵐ a ∂μ, ‖commutator (Y a) (test a n)‖ ≤ c) :
    ∀ᵐ a ∂μ, scalarCommutatorNorm (P a) (Y a) ≤ c := by
  have hall : ∀ᵐ a ∂μ, ∀ n, ‖commutator (Y a) (test a n)‖ ≤ c :=
    eventually_countable_forall.mpr hbound
  filter_upwards [hdense, hall] with a ha hb
  exact scalarCommutatorNorm_le_of_weak_dense_tests (P a) (Y a) (test a) ha hc hb

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FiniteAmplificationReduction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite amplification is reduced to centered symmetry tests on square Hilbert
arrays. The operator replacement and its symmetry bound remain explicit local
hypotheses; the padding, dilation, coordinate change, and perturbation losses
are all proved here.
-/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [PartialOrder A] [StarOrderedRing A]

omit [CompleteSpace H] in
/-- Amplifying the replacement does not enlarge its norm distance. -/
theorem norm_amplify_sub_le (S T : H →L[ℂ] H) (n : ℕ) :
    ‖amplify S n - amplify T n‖ ≤ ‖S - T‖ := by
  have h : amplify S n - amplify T n = amplify (S - T) n := by
    ext x i
    simp only [sub_apply, PiLp.sub_apply, amplify_apply]
  rw [h]
  exact norm_amplify_le (S - T) n

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FiniteFactorSymmetrization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-factor averaging stage uses actual normalized Haar measures
on the finite matrix-unitary groups. Their continuity and weak integrability
are proved here; the resulting operator is within the original scalar
commutator bound and has scalar commutator bound at most three times it. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory TopologicalSpace
open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]

section SingleStage

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem matrixUnitaryAction_norm_le (R : Matrix α α ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
    (u : Matrix.unitaryGroup α ℂ) : ‖matrixUnitaryAction R u‖ ≤ 1 := by
  let w := Unitary.map (StarMonoidHom.ofClass R) u
  change ‖(w : H →L[ℂ] H)‖ ≤ 1
  exact (Unitary.linearIsometryEquiv w).toLinearIsometry.norm_toContinuousLinearMap_le

theorem matrixUnitaryAction_adjoint (R : Matrix α α ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
    (u : Matrix.unitaryGroup α ℂ) :
    (matrixUnitaryAction R u).adjoint = matrixUnitaryAction R u⁻¹ := by
  change (R (u : Matrix α α ℂ)).adjoint = R (↑u⁻¹ : Matrix α α ℂ)
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  congr 1

/-- Finite-dimensional continuity proves strong continuity of the action. -/
theorem matrixUnitaryAction_continuous (R : Matrix α α ℂ →⋆ₐ[ℂ] (H →L[ℂ] H)) (x : H) :
    Continuous (fun u : Matrix.unitaryGroup α ℂ => matrixUnitaryAction R u x) := by
  have hR : Continuous R := R.toAlgHom.toLinearMap.continuous_of_finiteDimensional
  exact (hR.comp continuous_subtype_val).clm_apply continuous_const

/-- Commutation with matrix unitaries implies commutation with every matrix,
by the four-unitary spanning theorem in the actual C-star matrix algebra. -/
theorem commutes_matrix_of_unitaries [Nonempty α]
    (R : Matrix α α ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S : H →L[ℂ] H) (hS : ∀ u, commutator S (matrixUnitaryAction R u) = 0)
    (a : Matrix α α ℂ) : commutator S (R a) = 0 := by
  let φ : CStarMatrix α α ℂ →⋆ₐ[ℂ] (H →L[ℂ] H) :=
    R.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom
  obtain ⟨u, c, ha, _⟩ := CStarAlgebra.exists_sum_four_unitary (CStarMatrix.ofMatrix a)
  have hu (i : Fin 4) : commutator S (φ (u i : CStarMatrix α α ℂ)) = 0 := by
    let v : Matrix.unitaryGroup α ℂ :=
      Unitary.map (StarMonoidHom.ofClass CStarMatrix.ofMatrixStarAlgEquiv.symm) (u i)
    exact hS v
  have he : R a = ∑ i, c i • φ (u i : CStarMatrix α α ℂ) := by
    change φ (CStarMatrix.ofMatrix a) = _
    rw [ha, map_sum]
    simp only [map_smul]
  rw [he]
  unfold commutator
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro i _
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
  change c i • commutator S (φ (u i : CStarMatrix α α ℂ)) = 0
  rw [hu, smul_zero]

end SingleStage

attribute [local instance] OAI.KadisonSimilarity.finiteMatrixUnitaryCompactSpace
attribute [local instance] OAI.KadisonSimilarity.finiteMatrixUnitaryMeasurableSpace
attribute [local instance] OAI.KadisonSimilarity.finiteMatrixUnitaryBorelSpace
/-- Actual Haar averaging over increasing matrix stages produces the
finite-factor perturbation with the manuscript's factor-three estimate. -/
theorem exists_finite_matrix_symmetrization
    [∀ n, Nonempty (I n)]
    (M : VonNeumannAlgebra H)
    (R : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hmem : ∀ n a, R n a ∈ M)
    (ι : ∀ n m, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (hcompat : ∀ n m h a, R m (ι n m h a) = R n a)
    (Y : H →L[ℂ] H) :
    ∃ Y₀ : H →L[ℂ] H, ‖Y₀‖ ≤ ‖Y‖ ∧
      ‖Y₀ - Y‖ ≤ scalarCommutatorNorm M Y ∧
      scalarCommutatorNorm M Y₀ ≤ 3 * scalarCommutatorNorm M Y ∧
      ∀ n a, commutator Y₀ (R n a) = 0 := by
  let U := fun n => matrixUnitaryAction (R n)
  let emb := fun n m h =>
    Unitary.map (StarMonoidHom.ofClass (ι n m h))
  have hc n m h u : U m (emb n m h u) = U n u := hcompat n m h u
  have hI n : WeaklyIntegrable (finiteMatrixHaarProbability (I := I) n)
      (unitaryConjugate (U n) Y) :=
    weaklyIntegrable_unitaryConjugate _ _ (matrixUnitaryAction_adjoint (R n))
      (matrixUnitaryAction_continuous (R n)) Y
  obtain ⟨Y₀, hnorm, hclose, hscalar, hinv⟩ := exists_scalar_symmetrization
    (finiteMatrixHaarProbability (I := I)) M U
    (fun n => matrixUnitaryAction_norm_le (R n)) (fun n u => hmem n u)
    (fun n m h u => emb n m h u) hc Y hI
  exact ⟨Y₀, hnorm, hclose, hscalar, fun n => commutes_matrix_of_unitaries (R n) Y₀ (hinv n)⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FiniteTypeIEstimate
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.vonNeumannInnerDerivation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite type-I branch of the factor argument. Actual normalized
matrix-unitary averaging puts the operator within its scalar commutator
norm of the commutant, giving complete commutator constant two. -/

noncomputable section
namespace KadisonSimilarity

variable {H α : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype α] [DecidableEq α] [Nonempty α]

/-- A represented full finite matrix algebra has the uniform matrix
commutator estimate with constant two, in every multiplicity. -/
theorem finiteTypeI_commutator_estimate (P : VonNeumannAlgebra H)
    (ι : Matrix α α ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hmem : ∀ a, ι a ∈ P)
    (hsurj : ∀ T : H →L[ℂ] H, T ∈ P → ∃ a, ι a = T) :
    CommutatorEstimate P 2 := by
  intro Y n X hX
  obtain ⟨Y₀, _hnorm, hclose, _hscalar, hinv⟩ :=
    exists_finite_matrix_symmetrization (I := fun _ : ℕ => α) P (fun _ => ι)
      (fun _ => hmem) (fun _ _ _ => StarAlgHom.id ℂ (Matrix α α ℂ))
      (fun _ _ _ _ => rfl) Y
  have hcomm (i j : Fin n) : commutator Y₀ (X i j) = 0 := by
    obtain ⟨a, ha⟩ := hsurj (X i j) (hX i j)
    rw [← ha]
    exact hinv 0 a
  have hz : commutator (amplify Y₀ n) (matrixOperator X) = 0 := by
    rw [commutator_amplify_matrixOperator]
    ext ξ i
    simp [matrixOperator, hcomm]
  have hc : ‖amplify Y n - amplify Y₀ n‖ ≤ scalarCommutatorNorm P Y := by
    apply (norm_amplify_sub_le Y Y₀ n).trans
    rwa [norm_sub_rev]
  have h := norm_commutator_le_of_approx (amplify Y n) (amplify Y₀ n) (matrixOperator X)
    (show ‖commutator (amplify Y₀ n) (matrixOperator X)‖ ≤ 0 by rw [hz, norm_zero]) hc
  simpa only [zero_add] using h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_IsometricTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.innerDerivation_apply _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.vonNeumannInnerDerivation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transfer through an isometric row

This is the operator calculation in the properly infinite case of
`prop:factor-representations`. The row/column derivation estimates must still be
provided before applying this lemma to a properly infinite von Neumann algebra.
-/

noncomputable section

namespace KadisonSimilarity

open ContinuousLinearMap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Solving the three-term commutator expansion by compressing with an isometry. -/
theorem isometric_commutator_identity (Y : H →L[ℂ] H) (A X : K →L[ℂ] K)
    (V : K →L[ℂ] H) (hV : V.adjoint.comp V = ContinuousLinearMap.id ℂ K) :
    commutator A X =
      V.adjoint.comp ((commutator Y (V.comp (X.comp V.adjoint))).comp V) -
      V.adjoint.comp ((Y.comp V - V.comp A).comp X) -
      X.comp ((A.comp V.adjoint - V.adjoint.comp Y).comp V) := by
  simp only [commutator, mul_def, comp_sub, sub_comp, comp_assoc, hV, comp_id]
  simp only [← comp_assoc, hV, id_comp]
  abel

/-- The coefficient `1+2c` in the properly infinite factor estimate. -/
theorem norm_commutator_le_isometric_transfer (Y : H →L[ℂ] H)
    (A X : K →L[ℂ] K) (V : K →L[ℂ] H)
    (hV : V.adjoint.comp V = ContinuousLinearMap.id ℂ K)
    {δ c : ℝ} (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hscalar : ‖commutator Y (V.comp (X.comp V.adjoint))‖ ≤
      δ * ‖V.comp (X.comp V.adjoint)‖)
    (hrow : ‖Y.comp V - V.comp A‖ ≤ c * δ)
    (hcol : ‖A.comp V.adjoint - V.adjoint.comp Y‖ ≤ c * δ) :
    ‖commutator A X‖ ≤ (1 + 2 * c) * δ * ‖X‖ := by
  have hVnorm : ‖V‖ ≤ 1 := by
    have h := norm_adjoint_comp_self V
    rw [hV] at h
    have hi := ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := K)
    nlinarith [norm_nonneg V]
  have hVadj : ‖V.adjoint‖ ≤ 1 := by simpa using hVnorm
  have hmiddle : ‖V.comp (X.comp V.adjoint)‖ ≤ ‖X‖ := by
    calc
      _ ≤ ‖V‖ * (‖X‖ * ‖V.adjoint‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖X‖ * 1) := by gcongr
      _ = ‖X‖ := by ring
  have hfirst :
      ‖V.adjoint.comp ((commutator Y (V.comp (X.comp V.adjoint))).comp V)‖ ≤
        δ * ‖X‖ := by
    calc
      _ ≤ ‖V.adjoint‖ * (‖commutator Y (V.comp (X.comp V.adjoint))‖ * ‖V‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * ((δ * ‖X‖) * 1) := by
        gcongr
        exact hscalar.trans (mul_le_mul_of_nonneg_left hmiddle hδ)
      _ = δ * ‖X‖ := by ring
  have hsecond : ‖V.adjoint.comp ((Y.comp V - V.comp A).comp X)‖ ≤ c * δ * ‖X‖ := by
    calc
      _ ≤ ‖V.adjoint‖ * (‖Y.comp V - V.comp A‖ * ‖X‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * ((c * δ) * ‖X‖) := by gcongr
      _ = c * δ * ‖X‖ := by ring
  have hthird : ‖X.comp ((A.comp V.adjoint - V.adjoint.comp Y).comp V)‖ ≤ c * δ * ‖X‖ := by
    calc
      _ ≤ ‖X‖ * (‖A.comp V.adjoint - V.adjoint.comp Y‖ * ‖V‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ ‖X‖ * ((c * δ) * 1) := by gcongr
      _ = c * δ * ‖X‖ := by ring
  rw [isometric_commutator_identity Y A X V hV]
  calc
    _ ≤ (‖V.adjoint.comp ((commutator Y (V.comp (X.comp V.adjoint))).comp V)‖ +
        ‖V.adjoint.comp ((Y.comp V - V.comp A).comp X)‖) +
        ‖X.comp ((A.comp V.adjoint - V.adjoint.comp Y).comp V)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (δ * ‖X‖ + c * δ * ‖X‖) + c * δ * ‖X‖ :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ = (1 + 2 * c) * δ * ‖X‖ := by ring

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ProperlyInfiniteEstimate
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.hilbertArrayFlatten_apply _root_.OAI.KadisonSimilarity.hilbertFourfoldFlatten_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.hilbertTripleFlatten_apply _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_matrixOperator _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.matrixLeftArray_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.representedDoubleMatrix_apply _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The properly infinite commutator estimate. Internal orthogonal isometries
supply the row, and Dickson supplies its actual commutator error bounds. -/

noncomputable section
namespace KadisonSimilarity

open scoped CStarAlgebra

section NativeMatrixNorm

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem norm_cstarMatrix_conjTranspose_le {m n : Type*} [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) : ‖M.conjTranspose‖ ≤ ‖M‖ := by
  apply CStarMatrix.norm_le_of_forall_inner_le (C := ‖M‖₊)
  intro v w
  have hi := CStarMatrix.inner_toCLM_conjTranspose_right (M := M) (v := w) (w := v)
  have hn := congrArg norm hi
  calc
    _ = ‖inner A (CStarMatrix.toCLM M w) v‖ := hn
    _ ≤ ‖CStarMatrix.toCLM M w‖ * ‖v‖ := CStarModule.norm_inner_le _
    _ ≤ (‖M‖ * ‖w‖) * ‖v‖ := mul_le_mul_of_nonneg_right
      ((CStarMatrix.toCLM M).le_opNorm w) (norm_nonneg v)
    _ = (‖M‖₊ : ℝ) * ‖v‖ * ‖w‖ := by simp only [coe_nnnorm]; ring

/-- Rectangular conjugate transpose preserves the native C-star matrix norm. -/
theorem norm_cstarMatrix_conjTranspose {m n : Type*} [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) : ‖M.conjTranspose‖ = ‖M‖ := by
  apply le_antisymm (norm_cstarMatrix_conjTranspose_le M)
  have hMM : M.conjTranspose.conjTranspose = M := by
    ext i j
    simp [CStarMatrix.conjTranspose_apply]
  simpa only [hMM] using norm_cstarMatrix_conjTranspose_le M.conjTranspose

/-- The adjoint column of orthogonal internal isometries is contractive in
the native C-star matrix norm. -/
theorem norm_cstar_isometry_adjoint_column_le_one {n : ℕ} (v : Fin n → A)
    (hv : ∀ i j, star (v i) * v j = if i = j then 1 else 0) :
    ‖CStarMatrix.ofMatrix (fun i (_ : Fin 1) => star (v i))‖ ≤ 1 := by
  let W : CStarMatrix (Fin n) (Fin 1) A := CStarMatrix.ofMatrix (fun i _ => star (v i))
  change ‖CStarMatrix.toCLM W‖ ≤ 1
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have hterm (i j : Fin n) :
      x i * star (v i) * (v j * star (x j)) =
        if i = j then x i * star (x j) else 0 := by
    calc
      _ = x i * (star (v i) * v j) * star (x j) := by noncomm_ring
      _ = _ := by rw [hv]; split_ifs <;> simp
  have hi : inner A (CStarMatrix.toCLM W x) (CStarMatrix.toCLM W x) = inner A x x := by
    have hout : CStarMatrix.toCLM W x =
        (WithCStarModule.equiv A (Fin 1 → A)).symm
          (fun _ => ∑ i : Fin n, x i * star (v i)) :=
      CStarMatrix.toCLM_apply_eq_sum
    rw [hout]
    change (∑ _ : Fin 1, (∑ i : Fin n, x i * star (v i)) *
      star (∑ j : Fin n, x j * star (v j))) = ∑ i : Fin n, x i * star (x i)
    simp only [Finset.univ_unique, Finset.sum_singleton, star_sum, star_mul, star_star,
      Finset.mul_sum, Finset.sum_mul]
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hn : ‖CStarMatrix.toCLM W x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [CStarModule.norm_sq_eq A, CStarModule.norm_sq_eq A, hi]
  have heq : ‖CStarMatrix.toCLM W x‖ = ‖x‖ := by
    nlinarith [norm_nonneg (CStarMatrix.toCLM W x), norm_nonneg x]
  simpa only [one_mul] using heq.le

/-- The row of internal orthogonal isometries has native matrix norm at most one. -/
theorem norm_cstar_isometry_row_le_one {n : ℕ} (v : Fin n → A)
    (hv : ∀ i j, star (v i) * v j = if i = j then 1 else 0) :
    ‖CStarMatrix.ofMatrix (fun (_ : Fin 1) i => v i)‖ ≤ 1 := by
  rw [← norm_cstarMatrix_conjTranspose]
  exact norm_cstar_isometry_adjoint_column_le_one v hv

end NativeMatrixNorm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem internal_isometry_relation (P : VonNeumannAlgebra H) {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then 1 else 0) (i j : Fin n) :
    (v i : H →L[ℂ] H).adjoint.comp (v j : H →L[ℂ] H) =
      if i = j then ContinuousLinearMap.id ℂ H else 0 := by
  have h := congrArg (fun a : P => (a : H →L[ℂ] H)) (hv i j)
  split_ifs at h ⊢ <;> exact h

theorem internalIsometryRow_adjoint_self (P : VonNeumannAlgebra H) {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then 1 else 0) :
    (internalIsometryRow P v).adjoint.comp (internalIsometryRow P v) =
      ContinuousLinearMap.id ℂ (HilbertCopies H n) := by
  ext x i
  change (sumColumns (fun i => (v i : H →L[ℂ] H))).adjoint
    (sumColumns (fun i => (v i : H →L[ℂ] H)) x) i = x i
  rw [sumColumns_adjoint_apply, sumColumns_apply, map_sum]
  have ht (j : Fin n) : (v i : H →L[ℂ] H).adjoint ((v j : H →L[ℂ] H) (x j)) =
      if i = j then x j else 0 := by
    have h := congrArg (fun T : H →L[ℂ] H => T (x j)) (internal_isometry_relation P v hv i j)
    split_ifs with hij
    · simpa only [hij, ↓reduceIte, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using h
    · simpa only [hij, ↓reduceIte, ContinuousLinearMap.comp_apply, zero_apply] using h
  simp only [ht, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

theorem norm_vonNeumannInnerDerivation (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) :
    ‖vonNeumannInnerDerivation P Y‖ = scalarCommutatorNorm P Y := by
  unfold scalarCommutatorNorm
  congr 1

/-- Dickson's row estimate gives the actual error of the internal isometry row. -/
theorem internalIsometryRow_error (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
    (dickson : DicksonTwoBound (A := P) (RectangularSum H H))
    {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then 1 else 0) :
    ‖Y.comp (internalIsometryRow P v) - (internalIsometryRow P v).comp (amplify Y n)‖ ≤
      (4 * Real.sqrt 2) * scalarCommutatorNorm P Y := by
  let δ := vonNeumannInnerDerivation P Y
  let W : Matrix (Fin 1) (Fin n) P := fun _ i => v i
  have hδ := (rectangularDerivation_row_column (vonNeumannRepresentation P)
    (vonNeumannRepresentation P) δ
    (cornerCommutator_leibniz (vonNeumannRepresentation P) (vonNeumannRepresentation P) Y)
    dickson).1 n W
  have heq (x : HilbertCopies H n) :
      (rectangularMatrixOperator (W.map δ) x) 0 =
        (Y.comp (internalIsometryRow P v) - (internalIsometryRow P v).comp (amplify Y n)) x := by
    rw [rectangularMatrixOperator_apply, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply]
    simp only [internalIsometryRow, sumColumns_apply, amplify_apply]
    change (∑ i, (Y ((v i : H →L[ℂ] H) (x i)) - (v i : H →L[ℂ] H) (Y (x i)))) =
      Y (∑ i, (v i : H →L[ℂ] H) (x i)) - ∑ i, (v i : H →L[ℂ] H) (Y (x i))
    rw [map_sum, Finset.sum_sub_distrib]
  have hnorm :
      ‖Y.comp (internalIsometryRow P v) - (internalIsometryRow P v).comp (amplify Y n)‖ ≤
        ‖rectangularMatrixOperator (W.map δ)‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (rectangularMatrixOperator (W.map δ)))
    intro x
    rw [← heq]
    exact (PiLp.norm_apply_le _ 0).trans ((rectangularMatrixOperator (W.map δ)).le_opNorm x)
  calc
    _ ≤ ((4 * Real.sqrt 2) * ‖δ‖) * ‖CStarMatrix.ofMatrix W‖ := hnorm.trans hδ
    _ ≤ ((4 * Real.sqrt 2) * ‖δ‖) * 1 := mul_le_mul_of_nonneg_left
      (norm_cstar_isometry_row_le_one v hv) (by positivity)
    _ = _ := by rw [mul_one, norm_vonNeumannInnerDerivation]

/-- Dickson's column estimate gives the adjoint-row error independently of
whether the operator being commuted is selfadjoint. -/
theorem internalIsometryRow_adjoint_error (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
    (dickson : DicksonTwoBound (A := P) (RectangularSum H H))
    {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then 1 else 0) :
    ‖(amplify Y n).comp (internalIsometryRow P v).adjoint -
        (internalIsometryRow P v).adjoint.comp Y‖ ≤
      (4 * Real.sqrt 2) * scalarCommutatorNorm P Y := by
  let δ := vonNeumannInnerDerivation P Y
  let W : Matrix (Fin n) (Fin 1) P := fun i _ => star (v i)
  have hδ := (rectangularDerivation_row_column (vonNeumannRepresentation P)
    (vonNeumannRepresentation P) δ
    (cornerCommutator_leibniz (vonNeumannRepresentation P) (vonNeumannRepresentation P) Y)
    dickson).2 n W
  have heq (x : H) :
      rectangularMatrixOperator (W.map δ) (PiLp.single 2 0 x) =
        ((amplify Y n).comp (internalIsometryRow P v).adjoint -
          (internalIsometryRow P v).adjoint.comp Y) x := by
    ext i
    have hzero : (default : Fin 1) = 0 := Subsingleton.elim _ _
    simp only [rectangularMatrixOperator_apply, PiLp.single_apply, Finset.univ_unique,
      Finset.sum_singleton, hzero, ↓reduceIte, sub_apply, ContinuousLinearMap.comp_apply]
    change (δ (star (v i))) x =
      Y ((internalIsometryRow P v).adjoint x i) -
        (internalIsometryRow P v).adjoint (Y x) i
    rw [show (internalIsometryRow P v).adjoint x i = (v i : H →L[ℂ] H).adjoint x
      from sumColumns_adjoint_apply _ _ _,
      show (internalIsometryRow P v).adjoint (Y x) i = (v i : H →L[ℂ] H).adjoint (Y x)
      from sumColumns_adjoint_apply _ _ _]
    rfl
  have hnorm :
      ‖(amplify Y n).comp (internalIsometryRow P v).adjoint -
        (internalIsometryRow P v).adjoint.comp Y‖ ≤ ‖rectangularMatrixOperator (W.map δ)‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (rectangularMatrixOperator (W.map δ)))
    intro x
    rw [← heq]
    simpa only [PiLp.norm_single] using
      (rectangularMatrixOperator (W.map δ)).le_opNorm (PiLp.single 2 0 x)
  calc
    _ ≤ ((4 * Real.sqrt 2) * ‖δ‖) * ‖CStarMatrix.ofMatrix W‖ := hnorm.trans hδ
    _ ≤ ((4 * Real.sqrt 2) * ‖δ‖) * 1 := mul_le_mul_of_nonneg_left
      (norm_cstar_isometry_adjoint_column_le_one v hv) (by positivity)
    _ = _ := by rw [mul_one, norm_vonNeumannInnerDerivation]

theorem internalIsometryRow_compression_mem (P : VonNeumannAlgebra H) {n : ℕ}
    (v : Fin n → P) (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) (hX : ∀ i j, X i j ∈ P) :
    (internalIsometryRow P v).comp
      ((matrixOperator X).comp (internalIsometryRow P v).adjoint) ∈ P := by
  have heq : (internalIsometryRow P v).comp
      ((matrixOperator X).comp (internalIsometryRow P v).adjoint) =
      ∑ i : Fin n, ∑ j : Fin n, (v i : H →L[ℂ] H) * X i j * star (v j : H →L[ℂ] H) := by
    ext x
    simp [internalIsometryRow, sumColumns_apply, matrixOperator_apply, map_sum,
      sumColumns_adjoint_apply, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint]
  rw [heq]
  apply P.sum_mem
  intro i _
  apply P.sum_mem
  intro j _
  exact P.mul_mem (P.mul_mem (v i).property (hX i j))
    (show star (v j : H →L[ℂ] H) ∈ P from star_mem (v j).property)

/-- The properly infinite estimate is derived from internal isometries and
the published row/column estimate, with no row-error hypotheses. -/
theorem properlyInfinite_commutatorEstimate (P : VonNeumannAlgebra H)
    (isometries : HasInternalIsometryRows P)
    (dickson : DicksonTwoBound (A := P) (RectangularSum H H)) :
    CommutatorEstimate P (1 + 2 * (4 * Real.sqrt 2)) := by
  intro Y n X hX
  obtain ⟨v, hv⟩ := isometries n
  apply norm_commutator_le_isometric_transfer Y (amplify Y n) (matrixOperator X)
    (internalIsometryRow P v) (internalIsometryRow_adjoint_self P v hv)
    (scalarCommutatorNorm_nonneg P Y) (by positivity)
  · exact norm_commutator_le_scalarCommutatorNorm P Y _ (internalIsometryRow_compression_mem P v X hX)
  · exact internalIsometryRow_error P Y dickson v hv
  · exact internalIsometryRow_adjoint_error P Y dickson v hv

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FactorAssembly
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three factor branches

The finite branch records only the fixed trace, matrix presentation, and
local published inputs used in the preceding application. The alternatives
are the structural factor classification; no alternative assumes an
operator estimate. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [instance] FiniteFactorModel.cstar FiniteFactorModel.order
  FiniteFactorModel.starOrder FiniteFactorModel.stageNonempty

theorem FiniteMatrixFactorModel.estimate {P : VonNeumannAlgebra H}
    (F : FiniteMatrixFactorModel P) : CommutatorEstimate P 2 := by
  have : NeZero F.size := ⟨F.size_ne_zero⟩
  exact finiteTypeI_commutator_estimate P F.inclusion F.mem F.surjective

/-- Increasing the numerical constant preserves the same estimate. -/
theorem CommutatorEstimate.mono {P : VonNeumannAlgebra H} {c C : ℝ}
    (h : CommutatorEstimate P c) (hc : c ≤ C) : CommutatorEstimate P C := by
  intro Y n X hX
  exact (h Y n X hX).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (scalarCommutatorNorm_nonneg P Y)) (norm_nonneg _))

attribute [local instance] OAI.KadisonSimilarity.instIsClosedContinuousLinearMapComplexIdCoeStarSubalgebra_solutions_2
/-- All three structural alternatives yield the same fixed factor constant. -/
theorem factor_estimate_of_published_cases [TopologicalSpace.SeparableSpace H]
    (P : VonNeumannAlgebra H)
    (cases : PublishedFactorCasesInput P)
    (dickson : DicksonTwoBound (A := P) (RectangularSum H H)) :
    CommutatorEstimate P factorConstant := by
  unfold PublishedFactorCasesInput at cases
  rcases cases with finite | infinite | matrix
  · obtain ⟨F⟩ := finite
    exact F.estimate.mono finiteFactorConstant_le
  · exact (properlyInfinite_commutatorEstimate P infinite dickson).mono infiniteFactorConstant_le
  · obtain ⟨F⟩ := matrix
    exact F.estimate.mono two_le_factorConstant

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CentralDecomposition
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Central decomposition and the uniform separable estimate

The direct-integral input records only representatives of decomposable
operators, their almost-everywhere algebra operations, the scalar and matrix
norm formulas, and countably many dense contraction sections. These are the
specializations of Blackadar, III.1.6.1–4 and III.5.1.10–15 used here (with
Kaplansky density, I.9.1.3, for the contraction tests). Representatives need
satisfy algebraic identities only almost everywhere for each fixed pair.

The scalar fiber bounds, their common conull set, the factor estimates, and
the final perturbation estimate are proved below.
-/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter ContinuousLinearMapWOT
open scoped Topology

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type u) [∀ a, NormedAddCommGroup (K a)]
  [∀ a, InnerProductSpace ℂ (K a)] [∀ a, CompleteSpace (K a)]

variable {μ K} {P : VonNeumannAlgebra H}

/-- Fiber representatives preserve each fixed commutator almost everywhere. -/
theorem CentralDecompositionData.map_commutator
    (D : CentralDecompositionData μ K P)
    (x y : (vonNeumannCenter P).commutant.toStarSubalgebra) :
    ∀ᵐ a ∂μ, D.fiber (commutator x y) a =
      commutator (D.fiber x a) (D.fiber y a) := by
  filter_upwards [D.map_sub (x * y) (y * x), D.map_mul x y, D.map_mul y x]
    with a hs hxy hyx
  simpa only [commutator, hxy, hyx] using hs

/-- The countable sections give one conull set with the full scalar bound. -/
theorem CentralDecompositionData.scalar_bound
    (D : CentralDecompositionData μ K P)
    (Y : (vonNeumannCenter P).commutant.toStarSubalgebra)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : scalarCommutatorNorm P (Y : H →L[ℂ] H) ≤ c) :
    ∀ᵐ a ∂μ, scalarCommutatorNorm (D.algebra a) (D.fiber Y a) ≤ c := by
  apply ae_scalarCommutatorNorm_le_of_countable_tests μ K D.algebra (D.fiber Y)
    (fun a j => D.fiber (centerCommutantInclusion P (D.test j)) a) D.test_dense hc
  intro j
  have hb : ‖commutator (Y : H →L[ℂ] H) (D.test j : H →L[ℂ] H)‖ ≤ c := by
    calc
      _ ≤ scalarCommutatorNorm P (Y : H →L[ℂ] H) *
          ‖(D.test j : H →L[ℂ] H)‖ :=
        norm_commutator_le_scalarCommutatorNorm P Y (D.test j) (D.test j).property
      _ ≤ c * 1 := mul_le_mul hbound (D.test_norm j) (norm_nonneg _) hc
      _ = c := mul_one _
  have hf := (D.norm_le_iff (commutator Y (centerCommutantInclusion P (D.test j))) c hc).mp hb
  filter_upwards [hf, D.map_commutator Y (centerCommutantInclusion P (D.test j))]
    with a ha he
  simpa only [he] using ha

variable [∀ a, TopologicalSpace.SeparableSpace (K a)]

/-- A decomposable operator on the separable direct-integral fibers inherits
the uniform factor bound. -/
theorem CentralDecompositionData.matrix_bound
    (D : CentralDecompositionData μ K P)
    (cases : ∀ᵐ a ∂μ, PublishedFactorCasesInput (D.algebra a))
    (dickson : ∀ᵐ a ∂μ, DicksonTwoBound (A := D.algebra a) (RectangularSum (K a) (K a)))
    (Y : (vonNeumannCenter P).commutant.toStarSubalgebra)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : scalarCommutatorNorm P (Y : H →L[ℂ] H) ≤ c)
    (n : ℕ) (X : Matrix (Fin n) (Fin n) P.toStarSubalgebra) :
    ‖commutator (amplify (Y : H →L[ℂ] H) n)
      (matrixOperator (fun i j => (X i j : H →L[ℂ] H)))‖ ≤
      factorConstant * c * ‖matrixOperator (fun i j => (X i j : H →L[ℂ] H))‖ := by
  let Z := fun i j => centerCommutantInclusion P (X i j)
  let R := ‖matrixOperator (fun i j => (X i j : H →L[ℂ] H))‖
  have hR : 0 ≤ R := norm_nonneg _
  have hnorm : ∀ᵐ a ∂μ, ‖matrixOperator (fun i j => D.fiber (Z i j) a)‖ ≤ R :=
    (D.matrix_norm_le_iff n Z R hR).mp le_rfl
  have hmem : ∀ᵐ a ∂μ, ∀ i j, D.fiber (Z i j) a ∈ D.algebra a := by
    exact eventually_countable_forall.mpr fun i =>
      eventually_countable_forall.mpr fun j => D.mem (X i j)
  have hcomm : ∀ᵐ a ∂μ, ∀ i j,
      D.fiber (commutator Y (Z i j)) a =
        commutator (D.fiber Y a) (D.fiber (Z i j) a) := by
    exact eventually_countable_forall.mpr fun i =>
      eventually_countable_forall.mpr fun j => D.map_commutator Y (Z i j)
  rw [commutator_amplify_matrixOperator (Y : H →L[ℂ] H)
    (X := fun i j => (X i j : H →L[ℂ] H))]
  apply (D.matrix_norm_le_iff n (fun i j => commutator Y (Z i j))
    (factorConstant * c * R)
    (mul_nonneg (mul_nonneg (le_of_lt factorConstant_pos) hc) hR)).mpr
  filter_upwards [cases, dickson, D.scalar_bound Y hc hbound, hnorm, hmem, hcomm]
    with a hcase hd hs hn hm he
  have h := factor_estimate_of_published_cases (D.algebra a) hcase hd
    (D.fiber Y a) n (fun i j => D.fiber (Z i j) a) hm
  have heq : (fun i j => D.fiber (commutator Y (Z i j)) a) =
      (fun i j => commutator (D.fiber Y a) (D.fiber (Z i j) a)) := by
    funext i j
    exact he i j
  rw [heq, ← commutator_amplify_matrixOperator (D.fiber Y a)
    (X := fun i j => D.fiber (Z i j) a)]
  exact h.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hs (le_of_lt factorConstant_pos)) hn (norm_nonneg _)
    (mul_nonneg (le_of_lt factorConstant_pos) hc))

/-- Central averaging followed by the factor estimates proves the
manuscript's constant on this represented algebra. -/
theorem commutatorEstimate_of_centralDecomposition_oai
    (D : CentralDecompositionData μ K P)
    (approximation : SpectralStepApproximation (vonNeumannCenter P))
    (cases : ∀ᵐ a ∂μ, PublishedFactorCasesInput (D.algebra a))
    (dickson : ∀ᵐ a ∂μ, DicksonTwoBound (A := D.algebra a) (RectangularSum (K a) (K a))) :
    CommutatorEstimate P universalConstant := by
  intro Y n X hX
  let δ := scalarCommutatorNorm P Y
  have hδ : 0 ≤ δ := scalarCommutatorNorm_nonneg P Y
  obtain ⟨Y₁, _, hclose, hscalar, hcenter⟩ :=
    exists_central_symmetrization P approximation Y hδ le_rfl
  have hY₁ : Y₁ ∈ (vonNeumannCenter P).commutant := by
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    exact (sub_eq_zero.mp (hcenter a ha)).symm
  have hbound := D.matrix_bound cases dickson ⟨Y₁, hY₁⟩
    (show 0 ≤ 3 * δ by positivity) hscalar n (fun i j => ⟨X i j, hX i j⟩)
  have hperturb : ‖amplify Y n - amplify Y₁ n‖ ≤ δ := by
    have he : amplify Y n - amplify Y₁ n = amplify (Y - Y₁) n := by
      ext ξ i
      simp [amplify_apply, _root_.sub_apply]
    rw [he]
    exact (norm_amplify_le _ _).trans (by simpa only [norm_sub_rev] using hclose)
  calc
    _ ≤ factorConstant * (3 * δ) * ‖matrixOperator X‖ +
        2 * δ * ‖matrixOperator X‖ :=
      norm_commutator_le_of_approx (amplify Y n) (amplify Y₁ n)
        (matrixOperator X) hbound hperturb
    _ = universalConstant * scalarCommutatorNorm P Y * ‖matrixOperator X‖ := by
      dsimp [universalConstant, δ]
      ring

end KadisonSimilarity

end

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonSimilarity.commutatorEstimate_of_centralDecomposition_oai.{u} := @OAI.KadisonSimilarity.commutatorEstimate_of_centralDecomposition_oai.{u}
