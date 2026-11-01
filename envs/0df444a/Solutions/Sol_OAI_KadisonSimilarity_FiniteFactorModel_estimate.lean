-- Prove2me | solution 1 for OAI.KadisonSimilarity.FiniteFactorModel.estimate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T15:18:35.018991+00:00
-- url     : https://prove2.me/submissions/f35e79a8-8a1d-49b8-a57d-029153106c78
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A038
import Theorems.Thm_OAI_KadisonSimilarity_finite_standard_bound_of_local_free_corner
import Theorems.Thm_OAI_KadisonSimilarity_normal_tracial_cyclic_graph_closable

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
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_Amplification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicFactorization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cyclic column factorization from equality of vector functionals

Equality of quadratic forms yields an intertwining column contraction.
Existence of a realizing vector is a consequence of standard form.
-/

noncomputable section
namespace KadisonSimilarity

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The algebraic orbit is dense in its closed cyclic subspace. -/
theorem orbitIntoClosure_dense (N : StarSubalgebra ℂ (K →L[ℂ] K)) (ζ : K) :
    DenseRange (orbitIntoClosure N ζ) := by
  change Dense (Set.range (orbitIntoClosure N ζ))
  rw [Subtype.dense_iff, ← Set.range_comp]
  change closure (Set.range (orbitLinearMap N ζ)) ⊆
    closure (Set.range (orbitLinearMap N ζ))
  exact Set.Subset.rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_CompletelyBounded
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FullColumns
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_FiniteDerivationColumns
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-column passage from the uniform commutator estimate to complete
boundedness of a derivation. The finite implementers need no uniform norm bound;
only their scalar commutator bounds are used. -/

noncomputable section
namespace KadisonSimilarity

open Filter
open scoped Topology

variable {A H I : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Strong convergence is preserved by a fixed finite Hilbert amplification. -/
theorem amplify_tendsto_apply {l : Filter I} (Q : I → H →L[ℂ] H)
    (hQ : ∀ x, Tendsto (fun i => Q i x) l (𝓝 x)) (n : ℕ) (ξ : HilbertCopies H n) :
    Tendsto (fun i => amplify (Q i) n ξ) l (𝓝 ξ) := by
  have hp : Tendsto (fun i => fun j : Fin n => Q i (ξ j)) l (𝓝 (fun j => ξ j)) :=
    tendsto_pi_nhds.mpr fun j => hQ (ξ j)
  have h := ((PiLp.homeomorph 2 (fun _ : Fin n => H)).symm.continuous.tendsto
    (fun j : Fin n => ξ j)).comp hp
  convert h using 1
  · funext i
    apply PiLp.ext
    intro j
    rfl
  · congr 1

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicDecomposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cyclicCommonBaseMeasure_finite _root_.OAI.KadisonSimilarity.cyclicCommonBaseMeasure_regular _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every unital star representation is the orthogonal sum of cyclic reducing
representations. The family is constructed by Zorn's lemma. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type*} [CStarAlgebra A]

/-- The original vector has dense orbit for the restricted action. -/
theorem orbitGenerator_dense (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    DenseRange (fun a : A => orbitRepresentation σ ξ a (orbitGenerator σ ξ)) := by
  change Dense (Set.range (fun a : A => orbitRepresentation σ ξ a (orbitGenerator σ ξ)))
  have hset : Set.range (fun a : A => orbitRepresentation σ ξ a (orbitGenerator σ ξ)) =
      Set.range (orbitIntoClosure σ.range ξ) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨σ.rangeRestrict a, rfl⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := a.property
      refine ⟨b, ?_⟩
      apply Subtype.ext
      change σ b ξ = (a : H →L[ℂ] H) ξ
      change σ b = (a : H →L[ℂ] H) at hb
      rw [hb]
  rw [hset]
  exact orbitIntoClosure_dense σ.range ξ

namespace CyclicDecompositionData

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData σ.range)

theorem generator_dense (i : D.generators) :
    DenseRange (fun a : A => D.representation σ i a (D.generator σ i)) :=
  orbitGenerator_dense σ i

theorem representation_intertwines (i : D.generators) (a : A) :
    (σ a).comp (D.summands.inclusion i).toContinuousLinearMap =
      (D.summands.inclusion i).toContinuousLinearMap.comp (D.representation σ i a) := by
  ext x
  rfl

end CyclicDecompositionData

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_WeakOperatorLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm estimates and commutation identities used in symmetrization
persist under weak-operator limits. -/

noncomputable section
namespace KadisonSimilarity

open Filter ContinuousLinearMapWOT
open scoped Topology

variable {H K ι : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable [CompleteSpace K]

/-- Bounded closed balls are weak-operator closed, in the sequential or
general-filter form needed by the averaging argument. -/
theorem norm_le_of_weakOperator_tendsto {l : Filter ι} [l.NeBot]
    (T : ι → H →L[ℂ] K) (S : H →L[ℂ] K)
    (ht : Tendsto (fun i => ofCLM (T i)) l (𝓝 (ofCLM S)))
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ᶠ i in l, ‖T i‖ ≤ c) : ‖S‖ ≤ c := by
  apply norm_le_of_matrix_coefficients S hc
  intro x y
  have hlim := (tendsto_iff_forall_inner_apply_tendsto.mp ht x y).norm
  apply le_of_tendsto hlim
  filter_upwards [hbound] with i hi
  calc
    ‖inner ℂ y (T i x)‖ ≤ ‖y‖ * ‖T i x‖ := norm_inner_le_norm _ _
    _ ≤ ‖y‖ * (‖T i‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((T i).le_opNorm x) (norm_nonneg y)
    _ ≤ ‖y‖ * (c * ‖x‖) := by gcongr
    _ = c * ‖y‖ * ‖x‖ := by ring

variable [CompleteSpace H]

omit [CompleteSpace H] in
/-- Commutation against a fixed bounded operator is weak-operator continuous. -/
theorem weakOperator_tendsto_commutator {l : Filter ι}
    (T : ι → H →L[ℂ] H) (S A : H →L[ℂ] H)
    (ht : Tendsto (fun i => ofCLM (T i)) l (𝓝 (ofCLM S))) :
    Tendsto (fun i => ofCLM (commutator (T i) A)) l
      (𝓝 (ofCLM (commutator S A))) := by
  change Tendsto (fun i => ofCLM (T i) * ofCLM A - ofCLM A * ofCLM (T i)) l
    (𝓝 (ofCLM S * ofCLM A - ofCLM A * ofCLM S))
  exact (ht.mul_const _).sub (ht.const_mul _)

/-- A fixed commutator estimate survives weak-operator convergence. -/
theorem norm_commutator_le_of_weakOperator_tendsto {l : Filter ι} [l.NeBot]
    (T : ι → H →L[ℂ] H) (S A : H →L[ℂ] H)
    (ht : Tendsto (fun i => ofCLM (T i)) l (𝓝 (ofCLM S)))
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ᶠ i in l, ‖commutator (T i) A‖ ≤ c) :
    ‖commutator S A‖ ≤ c :=
  norm_le_of_weakOperator_tendsto _ _ (weakOperator_tendsto_commutator T S A ht) hc hbound

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_StrongCompressionTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite-compression estimates pass to the full representation.
Only strong convergence of the selfadjoint compressions is needed: the
two projection factors are moved to the two test vectors in the weak
operator matrix coefficients. -/

noncomputable section
namespace KadisonSimilarity
open Filter ContinuousLinearMapWOT
open scoped Topology

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {l : Filter I}

theorem weakOperator_tendsto_selfadjoint_compressions
    (Q : I → H →L[ℂ] H) (hQ : ∀ i, (Q i).adjoint = Q i)
    (hlim : ∀ x, Tendsto (fun i => Q i x) l (𝓝 x)) (T : H →L[ℂ] H) :
    Tendsto (fun i => ofCLM ((Q i).comp (T.comp (Q i)))) l (𝓝 (ofCLM T)) := by
  apply tendsto_iff_forall_inner_apply_tendsto.mpr
  intro x y
  have h := (hlim y).inner (𝕜 := ℂ) ((T.continuous.tendsto x).comp (hlim x))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  change inner ℂ y (Q i (T (Q i x))) = inner ℂ (Q i y) (T (Q i x))
  rw [← ContinuousLinearMap.adjoint_inner_left, hQ]

/-- A fixed matrix commutator estimate for all finite compressions survives
the limit, with exactly the same constant. -/
theorem matrix_commutator_bound_of_selfadjoint_compressions
    (Q : I → H →L[ℂ] H) (hQ : ∀ i, (Q i).adjoint = Q i)
    (hlim : ∀ x, Tendsto (fun i => Q i x) l (𝓝 x))
    [l.NeBot] (T : H →L[ℂ] H) (n : ℕ)
    (X : HilbertCopies H n →L[ℂ] HilbertCopies H n) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ᶠ i in l,
      ‖commutator (amplify ((Q i).comp (T.comp (Q i))) n) X‖ ≤ c) :
    ‖commutator (amplify T n) X‖ ≤ c := by
  have hconv := weakOperator_tendsto_selfadjoint_compressions
    (fun i => amplify (Q i) n)
    (fun i => by rw [adjoint_amplify, hQ])
    (amplify_tendsto_apply Q hlim n) (amplify T n)
  have heq (i : I) :
      (amplify (Q i) n).comp ((amplify T n).comp (amplify (Q i) n)) =
        amplify ((Q i).comp (T.comp (Q i))) n := by
    ext x j
    rfl
  simp only [heq] at hconv
  exact norm_commutator_le_of_weakOperator_tendsto _ (amplify T n) X hconv hc hbound

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SquareArrayPadding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Zero padding of Hilbert arrays

The coordinate inclusion along an arbitrary finite injection is isometric.
Extension of an operator by zero consequently preserves scalar commutator
norms and the norms of their matrix amplifications. No dimension factor occurs.
-/

noncomputable section
namespace KadisonSimilarity

section ContractiveRetraction

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem commutator_split_extension (J : E →L[ℂ] F) (R : F →L[ℂ] E)
    (T A : E →L[ℂ] E) (B : F →L[ℂ] F)
    (hJA : J.comp A = B.comp J) (hRB : R.comp B = A.comp R) :
    commutator (J.comp (T.comp R)) B = J.comp ((commutator T A).comp R) := by
  ext x
  have hr := congrArg (fun L : F →L[ℂ] E => L x) hRB
  have hj := congrArg (fun L : E →L[ℂ] F => L (T (R x))) hJA
  simp only [ContinuousLinearMap.comp_apply] at hr hj
  simp only [commutator, sub_apply, mul_apply_eq_comp,
    ContinuousLinearMap.comp_apply, map_sub, hr, ← hj]

end ContractiveRetraction

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_UltrapowerCommutators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.vonNeumannInnerDerivation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinatewise commutator estimates pass to the Hilbert ultrapower,
and then to any reducing closed subspace. -/

noncomputable section
namespace KadisonSimilarity

open NuclearUltrapower
open scoped ENNReal

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Compression to a reducing subspace preserves a commutator estimate.
The operator being tested need not preserve that subspace. -/
theorem norm_reducing_compression_commutator_le (V : K →ₗᵢ[ℂ] H)
    (T X : H →L[ℂ] H) (X₀ : K →L[ℂ] K)
    (hXV : X.comp V.toContinuousLinearMap = V.toContinuousLinearMap.comp X₀)
    (hXVstar : X.adjoint.comp V.toContinuousLinearMap =
      V.toContinuousLinearMap.comp X₀.adjoint)
    {c : ℝ} (hbound : ‖commutator T X‖ ≤ c) :
    ‖commutator (V.toContinuousLinearMap.adjoint.comp (T.comp V.toContinuousLinearMap)) X₀‖
      ≤ c := by
  have hAdj : V.toContinuousLinearMap.adjoint.comp X =
      X₀.comp V.toContinuousLinearMap.adjoint := by
    have h := congrArg ContinuousLinearMap.adjoint hXVstar
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] using h
  have heq : commutator
      (V.toContinuousLinearMap.adjoint.comp (T.comp V.toContinuousLinearMap)) X₀ =
      V.toContinuousLinearMap.adjoint.comp ((commutator T X).comp V.toContinuousLinearMap) := by
    symm
    simp only [commutator, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc]
    rw [hXV]
    simp only [← ContinuousLinearMap.comp_assoc]
    rw [hAdj]
  rw [heq]
  calc
    ‖V.toContinuousLinearMap.adjoint.comp ((commutator T X).comp V.toContinuousLinearMap)‖
        ≤ ‖V.toContinuousLinearMap.adjoint‖ *
          (‖commutator T X‖ * ‖V.toContinuousLinearMap‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖commutator T X‖ * 1) := by
      apply mul_le_mul
      · simpa only [ContinuousLinearMap.adjoint.norm_map] using V.norm_toContinuousLinearMap_le
      · exact mul_le_mul_of_nonneg_left V.norm_toContinuousLinearMap_le (norm_nonneg _)
      · positivity
      · norm_num
    _ ≤ c := by simpa only [one_mul, mul_one] using hbound

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CountableAmplification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite standard multiplicities exhaust the countable standard
representation.  The first-coordinate projections and all intertwining
identities below are constructed on the actual Hilbert direct sum. -/

noncomputable section
namespace KadisonSimilarity

open Filter ContinuousLinearMap
open scoped ENNReal Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

theorem norm_firstCopiesInclusion_le (n : ℕ) : ‖firstCopiesInclusion (H := H) n‖ ≤ 1 :=
  (firstCopiesIsometry (H := H) n).norm_toContinuousLinearMap_le

theorem firstCopiesProjection_tendsto (x : CountableCopies H) :
    Tendsto (fun n => firstCopiesProjection n x) atTop (𝓝 x) := by
  have h := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x).tendsto_sum_nat
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  simp only [firstCopiesProjection, comp_apply, firstCopiesInclusion_apply,
    firstCopiesInclusion_adjoint_apply]
  exact Fin.sum_univ_eq_sum_range (fun i => lp.single 2 i (x i)) n

omit [CompleteSpace H] in
theorem countableAmplify_firstCopiesInclusion (T : H →L[ℂ] H) (n : ℕ) :
    (countableAmplify T).comp (firstCopiesInclusion n) =
      (firstCopiesInclusion n).comp (amplify T n) := by
  ext x k
  simp only [comp_apply, firstCopiesInclusion_apply, map_sum, lp.coeFn_sum,
    Finset.sum_apply, countableAmplify_apply, lp.single_apply, Pi.single_apply,
    amplify_apply, apply_ite, map_zero]

theorem firstCopiesInclusion_adjoint_countableAmplify (T : H →L[ℂ] H) (n : ℕ) :
    (firstCopiesInclusion n).adjoint.comp (countableAmplify T) =
      (amplify T n).comp (firstCopiesInclusion n).adjoint := by
  ext x i
  simp only [comp_apply, firstCopiesInclusion_adjoint_apply,
    countableAmplify_apply, amplify_apply]

/-- Scalar commutators can only decrease on the first finite block. -/
theorem norm_firstCopies_compression_commutator_le
    (Y : CountableCopies H →L[ℂ] CountableCopies H) (T : H →L[ℂ] H) (r : ℕ)
    {c : ℝ} (h : ‖commutator Y (countableAmplify T)‖ ≤ c) :
    ‖commutator ((firstCopiesInclusion r).adjoint.comp
      (Y.comp (firstCopiesInclusion r))) (amplify T r)‖ ≤ c := by
  apply norm_reducing_compression_commutator_le (firstCopiesIsometry r)
    Y (countableAmplify T) (amplify T r)
  · exact countableAmplify_firstCopiesInclusion T r
  · change (countableAmplify T).adjoint.comp (firstCopiesInclusion r) =
      (firstCopiesInclusion r).comp (amplify T r).adjoint
    rw [countableAmplify_adjoint, adjoint_amplify]
    exact countableAmplify_firstCopiesInclusion T.adjoint r
  · exact h

omit [CompleteSpace H] in
private theorem matrix_firstCopies_intertwines (r n : ℕ)
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    (mapCopies (firstCopiesInclusion r) n).comp
      (matrixOperator (fun i j => amplify (X i j) r)) =
    (matrixOperator (fun i j => countableAmplify (X i j))).comp
      (mapCopies (firstCopiesInclusion r) n) :=
  mapCopies_intertwines_matrix (K := HilbertCopies H r) (F := CountableCopies H)
    (n := n) (firstCopiesInclusion (H := H) r)
    (fun i j => amplify (X i j) r) (fun i j => countableAmplify (X i j))
    (fun i j => (countableAmplify_firstCopiesInclusion (X i j) r).symm)

private theorem matrix_firstCopies_adjoint_intertwines (r n : ℕ)
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    (mapCopies (firstCopiesInclusion r).adjoint n).comp
      (matrixOperator (fun i j => countableAmplify (X i j))) =
    (matrixOperator (fun i j => amplify (X i j) r)).comp
      (mapCopies (firstCopiesInclusion r).adjoint n) :=
  mapCopies_intertwines_matrix (K := CountableCopies H) (F := HilbertCopies H r)
    (n := n) (firstCopiesInclusion (H := H) r).adjoint
    (fun i j => countableAmplify (X i j)) (fun i j => amplify (X i j) r)
    (fun i j => firstCopiesInclusion_adjoint_countableAmplify (X i j) r)

/-- Extending the compressed matrix commutator by zero preserves its norm. -/
theorem norm_firstCopies_matrix_compression (r n : ℕ)
    (Y : CountableCopies H →L[ℂ] CountableCopies H)
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    ‖commutator (amplify ((firstCopiesProjection r).comp
      (Y.comp (firstCopiesProjection r))) n)
      (matrixOperator (fun i j => countableAmplify (X i j)))‖ =
    ‖commutator (amplify ((firstCopiesInclusion r).adjoint.comp
      (Y.comp (firstCopiesInclusion r))) n)
      (matrixOperator (fun i j => amplify (X i j) r))‖ := by
  let J := mapCopies (firstCopiesInclusion (H := H) r) n
  let R := mapCopies (firstCopiesInclusion (H := H) r).adjoint n
  have hJ : ‖J‖ ≤ 1 := (norm_mapCopies_le _ _).trans (norm_firstCopiesInclusion_le r)
  have hR : ‖R‖ ≤ 1 := (norm_mapCopies_le _ _).trans (by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using norm_firstCopiesInclusion_le (H := H) r)
  have hRJ : R.comp J = ContinuousLinearMap.id ℂ (HilbertCopies (HilbertCopies H r) n) := by
    apply ContinuousLinearMap.ext
    intro x
    apply PiLp.ext
    intro i
    exact congrArg (fun T => T (x i)) (firstCopiesInclusion_adjoint_self r)
  have hext : amplify ((firstCopiesProjection r).comp (Y.comp (firstCopiesProjection r))) n =
      J.comp ((amplify ((firstCopiesInclusion r).adjoint.comp
        (Y.comp (firstCopiesInclusion r))) n).comp R) := by
    ext x i
    rfl
  rw [hext, commutator_split_extension J R _ _ _
    (matrix_firstCopies_intertwines r n X)
    (matrix_firstCopies_adjoint_intertwines r n X), norm_split_extension J R hJ hR hRJ]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The first-finite-copy estimates imply the same estimate on the countable
standard representation.  The finite-copy premise is a downstream estimate,
not an additional published input. -/
theorem countable_amplification_bound_of_finite
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {C : ℝ} (hC : 0 ≤ C)
    (hfinite : ∀ (r : ℕ) (T : HilbertCopies H r →L[ℂ] HilbertCopies H r)
      (d : ℝ), 0 ≤ d →
      (∀ a, ‖commutator T (amplify (σ a) r)‖ ≤ d * ‖a‖) →
      ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A),
        ‖commutator (amplify T n)
          (representedMatrix (amplifiedScalarRepresentation σ r) X)‖ ≤ C * d * ‖X‖)
    (Y : CountableCopies H →L[ℂ] CountableCopies H) {d : ℝ} (hd : 0 ≤ d)
    (hscalar : ∀ a, ‖commutator Y (countableRepresentation σ a)‖ ≤ d * ‖a‖)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖commutator (amplify Y n) (representedMatrix (countableRepresentation σ) X)‖ ≤
      C * d * ‖X‖ := by
  refine matrix_commutator_bound_of_selfadjoint_compressions
    (H := CountableCopies H) (l := (atTop : Filter ℕ))
    (firstCopiesProjection (H := H)) (firstCopiesProjection_adjoint (H := H))
    (firstCopiesProjection_tendsto (H := H)) Y n
    (representedMatrix (countableRepresentation σ) X) (by positivity) ?_
  filter_upwards with r
  change ‖commutator (amplify ((firstCopiesProjection r).comp
    (Y.comp (firstCopiesProjection r))) n)
    (matrixOperator (fun i j => countableAmplify (σ (X i j))))‖ ≤ _
  rw [norm_firstCopies_matrix_compression (H := H) r n Y (fun i j => σ (X i j))]
  apply hfinite r _ d hd
  intro a
  exact norm_firstCopies_compression_commutator_le Y (σ a) r (hscalar a)

/-- The actual GNS representation is a direct instance of the countable
amplification transfer, with its original finite-copy constant. -/
theorem gns_countable_amplification_bound (τ : A →ₚ[ℂ] ℂ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfinite : ∀ (r : ℕ) (T : HilbertCopies τ.GNS r →L[ℂ] HilbertCopies τ.GNS r)
      (d : ℝ), 0 ≤ d →
      (∀ a, ‖commutator T (amplify (τ.gnsStarAlgHom a) r)‖ ≤ d * ‖a‖) →
      ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A),
        ‖commutator (amplify T n)
          (representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom r) X)‖ ≤
        C * d * ‖X‖)
    (Y : CountableCopies τ.GNS →L[ℂ] CountableCopies τ.GNS)
    {d : ℝ} (hd : 0 ≤ d)
    (hscalar : ∀ a, ‖commutator Y (countableRepresentation τ.gnsStarAlgHom a)‖ ≤ d * ‖a‖)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖commutator (amplify Y n) (representedMatrix (countableRepresentation τ.gnsStarAlgHom) X)‖ ≤
      C * d * ‖X‖ :=
  countable_amplification_bound_of_finite τ.gnsStarAlgHom hC hfinite Y hd hscalar n X

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ReducingRepresentationTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.vonNeumannInnerDerivation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transfer from a reducing representation to a larger one. Extension
by zero preserves scalar and matrix commutator norms, so a standard-form
embedding costs no constant in the finite-factor estimate. -/

noncomputable section
namespace KadisonSimilarity

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
  (I : H →ₗᵢ[ℂ] K)
  (hI : ∀ a, I.toContinuousLinearMap.comp (σ a) =
    (ρ a).comp I.toContinuousLinearMap)

include hI in
/-- A star intertwiner also intertwines in the reverse direction through
its Hilbert adjoint. -/
theorem adjoint_intertwines_representations (a : A) :
    I.toContinuousLinearMap.adjoint.comp (ρ a) =
      (σ a).comp I.toContinuousLinearMap.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint (hI (star a))
  simpa only [ContinuousLinearMap.adjoint_comp, map_star,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] using h.symm

include hI in
/-- The scalar commutator has exactly its original norm. -/
theorem norm_reducingExtension_commutator (Y : H →L[ℂ] H) (a : A) :
    ‖commutator (reducingExtension I Y) (ρ a)‖ = ‖commutator Y (σ a)‖ := by
  rw [reducingExtension, commutator_split_extension _ _ _ _ _ (hI a)
    (adjoint_intertwines_representations σ ρ I hI a)]
  exact norm_split_extension _ _ I.norm_toContinuousLinearMap_le
    (by simpa only [ContinuousLinearMap.adjoint.norm_map] using I.norm_toContinuousLinearMap_le)
    I.adjoint_comp_self _

include hI in
/-- The same exact identity holds at every finite matrix level. -/
theorem norm_reducingExtension_matrix_commutator
    (Y : H →L[ℂ] H) (n : ℕ) (X : Matrix (Fin n) (Fin n) A) :
    ‖commutator (amplify (reducingExtension I Y) n)
      (matrixOperator (X.map ρ))‖ =
    ‖commutator (amplify Y n) (matrixOperator (X.map σ))‖ := by
  let J := mapCopies I.toContinuousLinearMap n
  let R := mapCopies I.toContinuousLinearMap.adjoint n
  have hJ : ‖J‖ ≤ 1 := (norm_mapCopies_le _ _).trans I.norm_toContinuousLinearMap_le
  have hR : ‖R‖ ≤ 1 := (norm_mapCopies_le _ _).trans (by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using I.norm_toContinuousLinearMap_le)
  have hRJ : R.comp J = ContinuousLinearMap.id ℂ (HilbertCopies H n) := by
    dsimp [R, J]
    rw [← mapCopies_comp_eq, I.adjoint_comp_self]
    exact mapCopies_id_eq n
  have hJA : J.comp (matrixOperator (X.map σ)) =
      (matrixOperator (X.map ρ)).comp J :=
    mapCopies_intertwines_matrix _ _ _ (fun i j => hI (X i j))
  have hRB : R.comp (matrixOperator (X.map ρ)) =
      (matrixOperator (X.map σ)).comp R :=
    mapCopies_intertwines_matrix _ _ _
      (fun i j => adjoint_intertwines_representations σ ρ I hI (X i j))
  have hext : amplify (reducingExtension I Y) n = J.comp ((amplify Y n).comp R) := by
    ext ξ i
    rfl
  rw [hext, commutator_split_extension _ _ _ _ _ hJA hRB,
    norm_split_extension J R hJ hR hRJ]

variable [PartialOrder A] [StarOrderedRing A]

/-- A faithful star representation preserves the norm of every actual
C-star matrix, including the zero-size case. -/
theorem norm_representedMatrix_of_injective
    (hσ : Function.Injective σ) (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖representedMatrix σ X‖ = ‖X‖ := by
  apply NonUnitalStarAlgHom.norm_map (representedMatrixHom σ n) _ X
  intro S T h
  have hentry : (CStarMatrix.ofMatrix.symm S).map σ =
      (CStarMatrix.ofMatrix.symm T).map σ :=
    operatorMatrixRepresentation_injective n h
  apply CStarMatrix.ofMatrix.symm.injective
  ext i j
  exact hσ (congrFun (congrFun hentry i) j)

include hI in
/-- Any complete commutator bound for the larger representation restricts
to its reducing subrepresentation without loss. The scalar premise uses
the actual C-star norm of the represented algebra's source. -/
theorem finite_estimate_of_reducing_representation {C : ℝ}
    (estimate : ∀ (Z : K →L[ℂ] K) (δ : ℝ), 0 ≤ δ →
      (∀ a, ‖commutator Z (ρ a)‖ ≤ δ * ‖a‖) →
      ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A),
        ‖commutator (amplify Z n) (representedMatrix ρ X)‖ ≤ C * δ * ‖X‖)
    (Y : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : ∀ a, ‖commutator Y (σ a)‖ ≤ δ * ‖a‖)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖commutator (amplify Y n) (representedMatrix σ X)‖ ≤ C * δ * ‖X‖ := by
  have hlarge : ∀ a, ‖commutator (reducingExtension I Y) (ρ a)‖ ≤ δ * ‖a‖ := by
    intro a
    rw [norm_reducingExtension_commutator σ ρ I hI]
    exact hscalar a
  have h := estimate (reducingExtension I Y) δ hδ hlarge n X
  change ‖commutator (amplify (reducingExtension I Y) n)
    (matrixOperator ((CStarMatrix.ofMatrix.symm X).map ρ))‖ ≤ _ at h
  rw [norm_reducingExtension_matrix_commutator σ ρ I hI] at h
  exact h

/-- For the faithful concrete subtype representation, the C-star matrix
estimate is exactly the paper's operator-matrix `CommutatorEstimate`. -/
theorem commutatorEstimate_of_subtype_bound (P : VonNeumannAlgebra H)
    [IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H))] {C : ℝ}
    (estimate : ∀ (Y : H →L[ℂ] H) (δ : ℝ), 0 ≤ δ →
      (∀ a : P.toStarSubalgebra,
        ‖commutator Y (a : H →L[ℂ] H)‖ ≤ δ * ‖a‖) →
      ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) P.toStarSubalgebra),
        ‖commutator (amplify Y n) (representedMatrix P.toStarSubalgebra.subtype X)‖ ≤
          C * δ * ‖X‖) : CommutatorEstimate P C := by
  intro Y n X hX
  let Z : CStarMatrix (Fin n) (Fin n) P.toStarSubalgebra :=
    CStarMatrix.ofMatrix (fun i j => ⟨X i j, hX i j⟩)
  have hnorm := norm_representedMatrix_of_injective P.toStarSubalgebra.subtype
    Subtype.val_injective n Z
  have h := estimate Y (scalarCommutatorNorm P Y) (scalarCommutatorNorm_nonneg P Y)
    (fun a => norm_commutator_le_scalarCommutatorNorm P Y a a.property) n Z
  rw [← hnorm] at h
  exact h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NormalRepresentationReduction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normal representations and countable tracial multiplicity

The published input below is local to a fixed finite von Neumann algebra with
faithful normal finite trace and a fixed normal representation on a separable
Hilbert space.  Hiai, *Concise lectures on selected topics of von Neumann
algebras*, arXiv:2004.02383v1 (2020), Corollary 5.14 and Remark 5.15, printed
page 50, represent every normal positive functional by a vector in the tracial
standard form.  Applied on each cyclic reducing summand, the usual countable
cyclic decomposition gives the displayed isometric intertwiner.  This is the
normal-representation consequence used in the manuscript's global section;
it is not asserted here for arbitrary C-star representations or arbitrary
positive functionals.  The countable cyclic decomposition is the standard
representation theory cited there to Takesaki, *Theory of Operator Algebras I*
(1979).

All commutator and matrix estimates below are derived from that geometric
input and the already proved finite-to-countable transfer.
-/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A countable standard-form estimate transfers to the given normal
representation with exactly the same constant. -/
theorem normal_representation_bound_of_countable
    (τ : A →ₚ[ℂ] ℂ) (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (embedding : HiaiNormalStandardEmbeddingInput τ σ) {C : ℝ}
    (hcountable : ∀ (Z : CountableCopies τ.GNS →L[ℂ] CountableCopies τ.GNS)
      (δ : ℝ), 0 ≤ δ →
      (∀ a, ‖commutator Z (countableRepresentation τ.gnsStarAlgHom a)‖ ≤ δ * ‖a‖) →
      ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A),
        ‖commutator (amplify Z n)
          (representedMatrix (countableRepresentation τ.gnsStarAlgHom) X)‖ ≤
          C * δ * ‖X‖)
    (Y : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : ∀ a, ‖commutator Y (σ a)‖ ≤ δ * ‖a‖)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖commutator (amplify Y n) (representedMatrix σ X)‖ ≤ C * δ * ‖X‖ := by
  obtain ⟨I, hI⟩ := embedding
  exact finite_estimate_of_reducing_representation σ
    (countableRepresentation τ.gnsStarAlgHom) I hI hcountable Y hδ hscalar n X

/-- The finite tracial multiplicity estimates imply the estimate for any
normal representation supplied by the local standard-form input. -/
theorem normal_representation_bound_of_finite
    (τ : A →ₚ[ℂ] ℂ) (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (embedding : HiaiNormalStandardEmbeddingInput τ σ) {C : ℝ} (hC : 0 ≤ C)
    (hfinite : ∀ (r : ℕ) (T : HilbertCopies τ.GNS r →L[ℂ] HilbertCopies τ.GNS r)
      (δ : ℝ), 0 ≤ δ →
      (∀ a, ‖commutator T (amplify (τ.gnsStarAlgHom a) r)‖ ≤ δ * ‖a‖) →
      ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A),
        ‖commutator (amplify T n)
          (representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom r) X)‖ ≤
          C * δ * ‖X‖)
    (Y : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : ∀ a, ‖commutator Y (σ a)‖ ≤ δ * ‖a‖)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖commutator (amplify Y n) (representedMatrix σ X)‖ ≤ C * δ * ‖X‖ := by
  apply normal_representation_bound_of_countable τ σ embedding
    (fun Z δ hδ hscalar n X =>
      gns_countable_amplification_bound τ hC hfinite Z hδ hscalar n X)
    Y hδ hscalar n X

/-- In the faithful concrete representation this is the paper's full
operator-matrix commutator estimate. -/
theorem normal_factor_commutatorEstimate_of_finite
    (P : VonNeumannAlgebra H)
    [IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H))]
    (τ : P.toStarSubalgebra →ₚ[ℂ] ℂ)
    (embedding : HiaiNormalStandardEmbeddingInput τ P.toStarSubalgebra.subtype)
    {C : ℝ} (hC : 0 ≤ C)
    (hfinite : ∀ (r : ℕ) (T : HilbertCopies τ.GNS r →L[ℂ] HilbertCopies τ.GNS r)
      (δ : ℝ), 0 ≤ δ →
      (∀ a, ‖commutator T (amplify (τ.gnsStarAlgHom a) r)‖ ≤ δ * ‖a‖) →
      ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) P.toStarSubalgebra),
        ‖commutator (amplify T n)
          (representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom r) X)‖ ≤
          C * δ * ‖X‖) :
    CommutatorEstimate P C := by
  apply commutatorEstimate_of_subtype_bound P
  intro Y δ hδ hscalar n X
  exact normal_representation_bound_of_finite τ P.toStarSubalgebra.subtype
    embedding hC hfinite Y hδ hscalar n X

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_StandardEmbeddingAssembly
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cyclicCommonBaseMeasure_finite _root_.OAI.KadisonSimilarity.cyclicCommonBaseMeasure_regular _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble embeddings of the cyclic summands into the countable standard
representation. The countability and Hilbert-sum construction are proved;
only the embeddings of the individual cyclic representations are parameters. -/

noncomputable section
namespace KadisonSimilarity

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

namespace CyclicDecompositionData

variable {N : StarSubalgebra ℂ (H →L[ℂ] H)} (D : CyclicDecompositionData N)

/-- The actual total orthogonal cyclic family is a Hilbert direct sum. -/
theorem isHilbertSum : IsHilbertSum ℂ D.Space D.summands.inclusion := by
  apply IsHilbertSum.mk D.summands.orthogonal
  have heq : (⨆ i, LinearMap.range (D.summands.inclusion i).toLinearMap) =
      Submodule.span ℂ (⋃ i, Set.range (D.summands.inclusion i)) := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      rintro x ⟨y, rfl⟩
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, y, rfl⟩)
    · refine Submodule.span_le.mpr ?_
      intro x hx
      obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
      exact Submodule.mem_iSup_of_mem i ⟨y, rfl⟩
  rw [heq, D.summands.dense_span]

end CyclicDecompositionData

omit [CompleteSpace K] in
private theorem countableAmplify_single (T : K →L[ℂ] K) (n : ℕ) (x : K) :
    countableAmplify T (lp.single 2 n x) = lp.single 2 n (T x) := by
  ext j
  simp only [countableAmplify_apply, lp.single_apply, Pi.single_apply]
  split_ifs <;> simp only [map_zero]

/-- Countably many cyclic intertwiners combine into one isometric
intertwiner on the original separable representation. -/
theorem countable_embedding_of_cyclic_embeddings
    [TopologicalSpace.SeparableSpace H]
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (D : CyclicDecompositionData σ.range)
    (J : ∀ i, D.Space i →ₗᵢ[ℂ] K)
    (hJ : ∀ i a, (J i).toContinuousLinearMap.comp (D.representation σ i a) =
      (ρ a).comp (J i).toContinuousLinearMap) :
    ∃ I : H →ₗᵢ[ℂ] CountableCopies K,
      ∀ a, I.toContinuousLinearMap.comp (σ a) =
        (countableAmplify (ρ a)).comp I.toContinuousLinearMap := by
  classical
  let := D.generators_countable
  obtain ⟨f, hf⟩ := exists_injective_nat D.generators
  let W : ∀ i, D.Space i →ₗᵢ[ℂ] CountableCopies K := fun i =>
    (countableSingleIsometry (f i)).comp (J i)
  have hW : OrthogonalFamily ℂ D.Space W := by
    intro i j hij x y
    change inner ℂ (lp.single (E := fun _ : ℕ => K) 2 (f i) (J i x))
      (lp.single (E := fun _ : ℕ => K) 2 (f j) (J j y)) = 0
    rw [lp.inner_single_left]
    simp only [lp.single_apply, Pi.single_apply, hf.ne hij, ite_false, inner_zero_right]
  let E := D.isHilbertSum.linearIsometryEquiv
  let I := hW.linearIsometry.comp E.toLinearIsometry
  have hI (i : D.generators) (x : D.Space i) :
      I (D.summands.inclusion i x) = lp.single 2 (f i) (J i x) := by
    have hE : E (D.summands.inclusion i x) = lp.single 2 i x := by
      apply E.symm.injective
      rw [E.symm_apply_apply]
      exact (D.isHilbertSum.linearIsometryEquiv_symm_apply_single x).symm
    change hW.linearIsometry (E (D.summands.inclusion i x)) = _
    rw [hE, hW.linearIsometry_apply_single]
    rfl
  refine ⟨I, fun a => ?_⟩
  have hdense : Dense (Submodule.span ℂ (⋃ i, Set.range (D.summands.inclusion i)) : Set H) := by
    intro x
    change x ∈ (Submodule.span ℂ (⋃ i, Set.range (D.summands.inclusion i))).topologicalClosure
    rw [D.summands.dense_span]
    trivial
  apply ContinuousLinearMap.ext_on hdense
  intro x hx
  obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
  have hσ := congrArg (fun T => T y) (D.representation_intertwines σ i a)
  have hj := congrArg (fun T => T y) (hJ i a)
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap] at hσ hj ⊢
  rw [hσ, hI, hI, countableAmplify_single, hj]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_IntertwinerPolar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polar isometry of an injective bounded intertwiner. This form allows
different source and target Hilbert spaces, as needed for closed cyclic
graphs in the normal representation argument. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- An injective bounded intertwiner has an isometric polar part, even when
its range is not closed. -/
theorem isometry_of_injective_intertwiner
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L : H →L[ℂ] K) (hLi : Function.Injective L)
    (hL : ∀ a, L.comp (σ a) = (ρ a).comp L) :
    ∃ J : H →ₗᵢ[ℂ] K,
      (∀ a, J.toContinuousLinearMap.comp (σ a) = (ρ a).comp J.toContinuousLinearMap) ∧
      Set.range L ⊆ Set.range J := by
  let R : H →L[ℂ] H := L.adjoint.comp L
  have hR : 0 ≤ R :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr L.isPositive_adjoint_comp_self
  let S : H →L[ℂ] H := CFC.sqrt R
  have hS : S.adjoint = S := (CFC.sqrt_nonneg R).isSelfAdjoint.star_eq
  have hSS : S.comp S = R := CFC.sqrt_mul_sqrt_self R hR
  have hn (x : H) : ‖S x‖ = ‖L x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,
      ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right, hS, hSS]
  have hSk : S.ker = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro x y hxy
    change S x = S y at hxy
    apply hLi
    apply sub_eq_zero.mp
    rw [← L.map_sub, ← norm_eq_zero, ← hn, S.map_sub, hxy, sub_self, norm_zero]
  have hd : DenseRange S := by
    have ht : S.range.topologicalClosure = ⊤ := by
      rw [← Submodule.orthogonal_orthogonal_eq_closure,
        ContinuousLinearMap.orthogonal_range, hS, hSk, Submodule.bot_orthogonal_eq_top]
    intro x
    change x ∈ S.range.topologicalClosure
    rw [ht]
    trivial
  let J : H →ₗᵢ[ℂ] K := L.toLinearMap.extendOfIsometry (e := S.toLinearMap) hd
    (fun x => (hn x).symm)
  have he (x : H) : J (S x) = L x :=
    LinearMap.extendOfIsometry_eq L.toLinearMap hd (fun x => (hn x).symm) x
  have hLa (a : A) : (σ a).comp L.adjoint = L.adjoint.comp (ρ a) := by
    have h := congrArg ContinuousLinearMap.adjoint (hL (star a))
    simpa only [ContinuousLinearMap.adjoint_comp, map_star,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] using h
  have hRc (a : A) : Commute R (σ a) := by
    change (L.adjoint.comp L).comp (σ a) = (σ a).comp (L.adjoint.comp L)
    rw [ContinuousLinearMap.comp_assoc, hL a,
      ← ContinuousLinearMap.comp_assoc, ← hLa a, ContinuousLinearMap.comp_assoc]
  have hSc (a : A) : S.comp (σ a) = (σ a).comp S :=
    (hRc a).cfcₙ_nnreal NNReal.sqrt
  refine ⟨J, fun a => ?_, ?_⟩
  · ext x
    refine hd.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro y
    change J (σ a (S y)) = ρ a (J (S y))
    rw [← show S (σ a y) = σ a (S y) from
      congrArg (fun T : H →L[ℂ] H => T y) (hSc a), he, he]
    exact congrArg (fun T : H →L[ℂ] K => T y) (hL a)
  · rintro _ ⟨x, rfl⟩
    exact ⟨S x, he x⟩

/-- A closed correspondence with injective first coordinate and dense second
coordinate gives an isometric embedding of its second representation into
its first. This is the operator step for a closable cyclic graph. -/
theorem isometry_of_injective_dense_correspondence
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (ν : A →⋆ₐ[ℂ] (Q →L[ℂ] Q))
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (X : Q →L[ℂ] H) (Y : Q →L[ℂ] K)
    (hX : Function.Injective X) (hY : DenseRange Y)
    (hXν : ∀ a, X.comp (ν a) = (σ a).comp X)
    (hYν : ∀ a, Y.comp (ν a) = (ρ a).comp Y) :
    ∃ J : K →ₗᵢ[ℂ] H, ∀ a,
      J.toContinuousLinearMap.comp (ρ a) = (σ a).comp J.toContinuousLinearMap := by
  have ht : Y.range.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hY
  have hYi : Function.Injective Y.adjoint := by
    apply LinearMap.ker_eq_bot.mp
    rw [← ContinuousLinearMap.orthogonal_range,
      ← Submodule.orthogonal_closure, ht, Submodule.top_orthogonal_eq_bot]
  have hYa (a : A) : Y.adjoint.comp (ρ a) = (ν a).comp Y.adjoint := by
    have h := congrArg ContinuousLinearMap.adjoint (hYν (star a))
    simpa only [ContinuousLinearMap.adjoint_comp, map_star,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] using h.symm
  obtain ⟨J₁, hJ₁, -⟩ := isometry_of_injective_intertwiner ν σ X hX hXν
  obtain ⟨J₂, hJ₂, -⟩ := isometry_of_injective_intertwiner ρ ν Y.adjoint hYi hYa
  refine ⟨J₁.comp J₂, fun a => ?_⟩
  change (J₁.toContinuousLinearMap.comp J₂.toContinuousLinearMap).comp (ρ a) =
    (σ a).comp (J₁.toContinuousLinearMap.comp J₂.toContinuousLinearMap)
  rw [ContinuousLinearMap.comp_assoc, hJ₂ a,
    ← ContinuousLinearMap.comp_assoc, hJ₁ a, ContinuousLinearMap.comp_assoc]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicGraphEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A closable cyclic orbit map gives an isometric subrepresentation. The
closed graph is itself a cyclic reducing representation, and its two
coordinate maps yield the embedding by polar decomposition. -/

noncomputable section
namespace KadisonSimilarity

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Trivial vertical part of the closed cyclic graph is exactly the
closability condition needed by the polar construction. -/
theorem cyclic_embedding_of_closable_graph
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (Ω : H) (ξ : K) (hξ : DenseRange (fun a : A => ρ a ξ))
    (hclose : ∀ x : cyclicGraph σ ρ Ω ξ,
      (x : RectangularSum H K).fst = 0 → (x : RectangularSum H K).snd = 0) :
    ∃ J : K →ₗᵢ[ℂ] H, ∀ a,
      J.toContinuousLinearMap.comp (ρ a) = (σ a).comp J.toContinuousLinearMap := by
  let π := pairRepresentation σ ρ
  let ζ : RectangularSum H K := WithLp.toLp 2 (Ω, ξ)
  let Q := cyclicGraph σ ρ Ω ξ
  let ν := orbitRepresentation π ζ
  let X : Q →L[ℂ] H := (WithLp.fstL 2 ℂ H K).comp Q.toSubmodule.subtypeL
  let Y : Q →L[ℂ] K := (WithLp.sndL 2 ℂ H K).comp Q.toSubmodule.subtypeL
  have hXi : Function.Injective X := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply Subtype.ext
    apply (WithLp.equiv 2 (H × K)).injective
    apply Prod.ext
    · change (x : RectangularSum H K).fst - (y : RectangularSum H K).fst = 0
      exact sub_eq_zero.mpr hxy
    · exact hclose (x - y) (by
        change (x : RectangularSum H K).fst - (y : RectangularSum H K).fst = 0
        exact sub_eq_zero.mpr hxy)
  have hYd : DenseRange Y := by
    have hsub : Set.range (fun a : A => ρ a ξ) ⊆ Set.range Y := by
      rintro _ ⟨a, rfl⟩
      let q : Q := ⟨π a ζ, orbitClosure_invariant π.range ζ (π.rangeRestrict a) ζ
        (self_mem_orbitClosure π.range ζ)⟩
      refine ⟨q, ?_⟩
      change (pairRepresentation σ ρ a ζ).snd = ρ a ξ
      rw [pairRepresentation_snd]
      rfl
    intro y
    exact closure_mono hsub (hξ y)
  apply isometry_of_injective_dense_correspondence ν σ ρ X Y hXi hYd
  · intro a
    ext x
    exact pairRepresentation_fst σ ρ a x
  · intro a
    ext x
    exact pairRepresentation_snd σ ρ a x

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NormalStandardEmbedding
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.cyclicCommonBaseMeasure_finite _root_.OAI.KadisonSimilarity.cyclicCommonBaseMeasure_regular _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The standard embedding of a separable concrete finite algebra is
constructed from its faithful normal GNS trace. No vector-realization or
standard-embedding result is an additional hypothesis. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

attribute [local instance] OAI.KadisonSimilarity.normalEmbedding_closed
/-- A faithful normal tracial geometry supplies a countable standard embedding. -/
theorem countable_embedding_of_normal_geometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (M : VonNeumannAlgebra H) (G : TracialCornerGeometry M.toStarSubalgebra E)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hτ : ∀ a, τ a = G.trace a)
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra E) (hN : G.left.range = N.toStarSubalgebra) :
    ∃ I : H →ₗᵢ[ℂ] CountableCopies E, ∀ a : M.toStarSubalgebra,
      I.toContinuousLinearMap.comp (a : H →L[ℂ] H) =
        (countableAmplify (G.left a)).comp I.toContinuousLinearMap := by
  let π := M.toStarSubalgebra.subtype
  let D := cyclicDecompositionData π.range
  have hlocal (i : D.generators) : ∃ J : D.Space i →ₗᵢ[ℂ] E, ∀ a,
      J.toContinuousLinearMap.comp (D.representation π i a) =
        (G.left a).comp J.toContinuousLinearMap := by
    apply cyclic_embedding_of_closable_graph G.left (D.representation π i)
      (G.vector 1) (D.generator π i) (D.generator_dense π i)
    exact normal_tracial_cyclic_graph_closable M G τ hτ h1 hf N hN
      (D.representation π i) (D.summands.inclusion i)
      (fun a => (D.representation_intertwines π i a).symm) (D.generator π i)
  choose J hJ using hlocal
  exact countable_embedding_of_cyclic_embeddings π G.left D J hJ

/-- The local Hiai standard-embedding consequence, proved from the
faithful normal trace by spectral truncation and cyclic decomposition. -/
theorem normal_standard_embedding_of_normal_gns
    (M : VonNeumannAlgebra H) (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (h1 : τ 1 = 1) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (hf : ∀ a, τ (star a * a) = 0 → a = 0) (hN : HasNormalGNS τ) :
    HiaiNormalStandardEmbeddingInput τ M.toStarSubalgebra.subtype := by
  exact countable_embedding_of_normal_geometry M (gnsTracialGeometry τ htr)
    τ (fun _ => rfl) h1 (gnsTracialVector_injective τ hf)
    (representationVonNeumannAlgebra τ.gnsStarAlgHom) hN

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixDiffuse
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrarily small full-matrix corners and comparison split every
nonzero projection in the source algebra. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) G.trace G.vector)

include M in
/-- A nonzero projection contains a proper nonzero subprojection. -/
theorem proper_subprojection_of_matrix_tower
    (hf : Function.Injective G.vector)
    (comparison : FiniteFactorProjectionComparison (fun a => (G.trace a).re))
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    (p : P) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : P, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q := by
  have hv : G.vector p ≠ 0 := by
    intro h
    exact hp0 (hf (h.trans (map_zero G.vector).symm))
  have hpnorm : ‖G.vector p‖ ^ 2 = (G.trace p).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), G.inner_vector,
      hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
    rfl
  have hppos : 0 < (G.trace p).re := by
    rw [← hpnorm]
    exact sq_pos_of_pos (norm_pos_iff.mpr hv)
  obtain ⟨n, _, t, ht, htp, F, hF⟩ := M.exists_small_trace_frame hsize hppos
  have hFp : (G.trace F.corner).re ≤ (G.trace p).re := by
    rw [hF, Complex.ofReal_re]
    exact htp.le
  obtain ⟨v, hv, hpv⟩ := comparison p F.corner hp F.corner_projection hFp
  let q := v * star v
  have hq : IsStarProjection q := range_projection_of_initial_projection
    F.corner v F.corner_projection hv
  have hτq : G.trace q = (t : ℂ) := by
    change G.trace (v * star v) = _
    rw [G.tracial, hv, hF]
  have hq0 : q ≠ 0 := by
    intro h
    have hh := congrArg Complex.re hτq
    rw [h, map_zero] at hh
    simp only [Complex.zero_re, Complex.ofReal_re] at hh
    exact (ne_of_gt ht) hh.symm
  have hqp : q ≠ p := by
    intro h
    have hh := congrArg Complex.re hτq
    rw [h, Complex.ofReal_re] at hh
    exact (ne_of_lt htp) hh.symm
  refine ⟨q, hq, hq0, hqp, hpv, ?_⟩
  have hpq : p * q = q := hpv
  have h := congrArg star hpq
  simpa only [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using h

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_NormalSmallCorners
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct small diffuse corners in the original algebra through its
actual faithful normal range, then transport the entire frame back. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped CStarAlgebra
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) G.trace G.vector)

include M in
/-- The normal represented source has no nonzero minimal projection. -/
theorem normalRange_diffuse_of_matrix_tower
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra H) (hN : G.left.range = N.toStarSubalgebra)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop) :
    ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧
        p * q = q ∧ q * p = q := by
  let e := equivalenceOfConcreteRange N G.left (G.left_injective hf) hN
  have comparison := G.projectionComparison_of_normal_range h1 hf N hN
    (G.scalar_center_of_matrix_tower M hf)
  intro p hp hp0
  let a := e.symm p
  have ha : IsStarProjection a := hp.map e.symm
  have hea : e a = p := e.apply_symm_apply p
  have ha0 : a ≠ 0 := by
    intro h
    apply hp0
    rw [← hea, h, map_zero]
  obtain ⟨q, hq, hq0, hqa, haq, hqa'⟩ :=
    G.proper_subprojection_of_matrix_tower M hf comparison hsize a ha ha0
  refine ⟨e q, hq.map e, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hq0 (e.injective (h.trans (map_zero e).symm))
  · intro h
    exact hqa (e.injective (h.trans hea.symm))
  · rw [← hea, ← map_mul, haq]
  · rw [← hea, ← map_mul, hqa']

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_NormalRealSequence
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real trace-orthonormal sequence is constructed in the normal source
and transported back, so its existence need not be part of a factor model. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) G.trace G.vector)

local instance normalRealSequence_closed_r8a64ca_1 (N : VonNeumannAlgebra H) :
    IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := base_norm_closed N
include M in
/-- The fixed matrix source supplies its own real centered sequence. -/
theorem exists_realTracialSequence_of_normal_matrix_tower
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra H) (hN : G.left.range = N.toStarSubalgebra)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop) :
    Nonempty (RealTracialSequence G.trace) := by
  let τ := G.normalTracialRepresentation h1 hf N hN
  let e := equivalenceOfConcreteRange N G.left (G.left_injective hf) hN
  let S := concreteRealTracialSequence τ
    (G.normalRange_diffuse_of_matrix_tower M h1 hf N hN hsize)
  have ht (a : N.toStarSubalgebra) : G.trace (e.symm a) = concreteTraceLinear τ a := by
    have h := G.normalTracialRepresentation_trace h1 hf N hN (e.symm a)
    change τ.trace (e (e.symm a)) = G.trace (e.symm a) at h
    rw [e.apply_symm_apply] at h
    exact h.symm
  refine ⟨{
    vector := fun n => e.symm (S.vector n)
    trace_zero := ?_
    selfadjoint := ?_
    inner := ?_ }⟩
  · intro n
    rw [ht]
    exact S.trace_zero n
  · intro n
    have hs : e.symm (star (S.vector n)) = star (e.symm (S.vector n)) :=
      e.symm.map_star' _
    rw [← hs, S.selfadjoint]
  · intro n m
    have hs : e.symm (star (S.vector n)) = star (e.symm (S.vector n)) :=
      e.symm.map_star' _
    have hm : e.symm (star (S.vector n) * S.vector m) =
        e.symm (star (S.vector n)) * e.symm (S.vector m) := e.symm.map_mul' _ _
    rw [← hs, ← hm, ht]
    exact S.inner n m

end TracialCornerGeometry
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

attribute [local instance] OAI.KadisonSimilarity.instIsClosedContinuousLinearMapComplexIdCoeStarSubalgebra_solutions_2
/-- Every finite presentation gives the concrete represented estimate. -/
theorem FiniteFactorModel.estimate_oai [TopologicalSpace.SeparableSpace H]
    {P : VonNeumannAlgebra H} (F : FiniteFactorModel P) :
    CommutatorEstimate P (3 * cornerConstant + 2) := by
  obtain ⟨S⟩ := (gnsTracialGeometry F.traceR F.tracialR).exists_realTracialSequence_of_normal_matrix_tower
    F.matrices F.oneR (gnsTracialVector_injective F.traceR F.faithfulR) _ F.normalR F.size_tendsto
  apply normal_factor_commutatorEstimate_of_finite P F.traceP
    (normal_standard_embedding_of_normal_gns P F.traceP F.oneP F.tracialP
      F.faithfulP F.normalP)
    (by have := cornerConstant_pos; positivity)
  intro r T δ hδ hscalar n X
  exact finite_standard_bound_of_local_free_corner F.traceR F.traceP F.oneR F.oneP
    F.omega F.tracialR F.tracialP F.inclusion F.trace_inclusion F.faithfulR F.faithfulP
    F.matrices F.omega_cofinite F.localInputs
    F.normalR F.normalP
    S F.size_tendsto T hδ hscalar n X

end KadisonSimilarity

end

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonSimilarity.FiniteFactorModel.estimate_oai.{u} := @OAI.KadisonSimilarity.FiniteFactorModel.estimate_oai.{u}
