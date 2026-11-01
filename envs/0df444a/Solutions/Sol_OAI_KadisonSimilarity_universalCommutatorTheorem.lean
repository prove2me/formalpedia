-- Prove2me | solution 1 for OAI.KadisonSimilarity.universalCommutatorTheorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T15:09:30.85069+00:00
-- url     : https://prove2.me/submissions/a69ff440-b6d1-4643-862d-cb10ee6ffd4d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A033
import Theorems.Thm_OAI_KadisonSimilarity_commutatorEstimate_of_centralDecomposition
import Theorems.Thm_OAI_KadisonSimilarity_dicksonTwoBound_proved
import Theorems.Thm_OAI_KadisonSimilarity_publishedUniformInputs

section
-- module Solutions.OAIQ075_KS.Compat
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- d13f23b's `IsSelfAdjoint.norm_le_max_of_le_of_le`: a selfadjoint element squeezed between `a` and `b`
has norm at most `max ‖a‖ ‖b‖` (Kadison similarity, oaiq-075). -/
theorem _root_.IsSelfAdjoint.norm_le_max_of_le_of_le {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {a b x : A} (hlo : a ≤ x) (hhi : x ≤ b) (hx : IsSelfAdjoint x) :
    ‖x‖ ≤ max ‖a‖ ‖b‖ := by
  by_cases! nontriv : Nontrivial A
  swap
  · have : x = 0 := Subsingleton.elim _ _
    simp [this]
  have hb : IsSelfAdjoint b := by
    have h1 : IsSelfAdjoint (b - x) := IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hhi)
    simpa using h1.add hx
  have ha : IsSelfAdjoint a := by
    have h1 : IsSelfAdjoint (x - a) := IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hlo)
    simpa using hx.sub h1
  have hbx : x ≤ algebraMap ℝ A ‖b‖ := hhi.trans hb.le_algebraMap_norm_self
  have hax : -(algebraMap ℝ A ‖a‖) ≤ x := ha.neg_algebraMap_norm_le_self.trans hlo
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum hx with h | h
  · exact ((le_algebraMap_iff_spectrum_le hx).mp hbx _ h).trans (le_max_right _ _)
  · have hax' : algebraMap ℝ A (-‖a‖) ≤ x := by simpa using hax
    have := (algebraMap_le_cfc_iff (R := ℝ) id (-‖a‖) x).mp (by rwa [cfc_id ℝ x hx]) _ h
    simp only [id] at this
    exact (by linarith : ‖x‖ ≤ ‖a‖).trans (le_max_left _ _)
end OAICompat434

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
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralStepDischarge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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


/-- A positive operator supported by a projection is bounded by its norm
 times that projection. -/
theorem nonneg_le_norm_smul_support (B p : H →L[ℂ] H)
    (hB : 0 ≤ B) (hp : IsStarProjection p) (hpB : p * B = B) (hBp : B * p = B) :
    B ≤ ‖B‖ • p := by
  simpa only [hp.isSelfAdjoint.star_eq, hpB, hBp, hp.isIdempotentElem.eq] using
    CStarAlgebra.star_left_conjugate_le_norm_smul (a := p) (b := B) hB.isSelfAdjoint

/-- Binary rounding halves the norm bound without changing the algebra. -/
theorem norm_sub_binarySpectralCorrection_le (B : H →L[ℂ] H)
    (hB : IsSelfAdjoint B) {r : ℝ} (hr : 0 ≤ r) (hBr : ‖B‖ ≤ r) :
    ‖B - binarySpectralCorrection B r‖ ≤ r / 2 := by
  let p := rangeSupport B⁺
  have hp : IsStarProjection p := rangeSupport_isStarProjection _
  have hq : IsStarProjection (1 - p) := hp.one_sub
  have hpos : 0 ≤ B⁺ := CFC.posPart_nonneg B
  have hneg : 0 ≤ B⁻ := CFC.negPart_nonneg B
  have hpn : B⁻ * p = 0 := mul_rangeSupport_eq_zero B⁺ B⁻ (CFC.negPart_mul_posPart B)
  have hnp : p * B⁻ = 0 := by
    have h := congrArg star hpn
    simpa only [star_mul, hp.isSelfAdjoint.star_eq, hneg.isSelfAdjoint.star_eq,
      star_zero] using h
  have hposBound : B⁺ ≤ r • p :=
    (nonneg_le_norm_smul_support B⁺ p hpos hp
      (rangeSupport_mul _) (mul_rangeSupport _ hpos.isSelfAdjoint)).trans
      (smul_le_smul_of_nonneg_right
        ((CStarAlgebra.norm_posPart_le B).trans hBr) hp.nonneg)
  have hnegBound : B⁻ ≤ r • (1 - p) := by
    apply (nonneg_le_norm_smul_support B⁻ (1 - p) hneg hq
      (by simp only [sub_mul, one_mul, hnp, sub_zero])
      (by simp only [mul_sub, mul_one, hpn, sub_zero])).trans
    exact smul_le_smul_of_nonneg_right
      ((CStarAlgebra.norm_negPart_le B).trans hBr) hq.nonneg
  have hupper : B ≤ r • p := by
    calc
      B = B⁺ - B⁻ := (CFC.posPart_sub_negPart B hB).symm
      _ ≤ B⁺ := sub_le_self _ hneg
      _ ≤ r • p := hposBound
  have hlower : r • p - r • 1 ≤ B := by
    calc
      r • p - r • 1 = -(r • (1 - p)) := by module
      _ ≤ -B⁻ := neg_le_neg hnegBound
      _ ≤ B⁺ - B⁻ := by simpa only [zero_sub] using sub_le_sub_right hpos B⁻
      _ = B := CFC.posPart_sub_negPart B hB
  have hlo : -((r / 2) • (1 : H →L[ℂ] H)) ≤ B - binarySpectralCorrection B r := by
    have h := add_le_add_right (sub_le_sub_right hlower (r • p)) ((r / 2) • 1)
    convert h using 1 <;> dsimp [binarySpectralCorrection, p] <;> module
  have hhi : B - binarySpectralCorrection B r ≤ (r / 2) • (1 : H →L[ℂ] H) := by
    have h := add_le_add_right (sub_le_sub_right hupper (r • p)) ((r / 2) • 1)
    convert h using 1 <;> dsimp [binarySpectralCorrection, p] <;> module
  have hself : IsSelfAdjoint (B - binarySpectralCorrection B r) :=
    hB.sub (((IsSelfAdjoint.all r).smul hp.isSelfAdjoint).sub
      ((IsSelfAdjoint.all (r / 2)).smul (IsSelfAdjoint.one (H →L[ℂ] H))))
  have hnormOne : ‖(r / 2) • (1 : H →L[ℂ] H)‖ ≤ r / 2 := by
    calc
      _ = |r / 2| * ‖(1 : H →L[ℂ] H)‖ := norm_smul _ _
      _ ≤ (r / 2) * 1 := by rw [abs_of_nonneg (by positivity)]; gcongr; exact ContinuousLinearMap.norm_id_le
      _ = r / 2 := mul_one _
  exact (IsSelfAdjoint.norm_le_max_of_le_of_le hlo hhi hself).trans
    (by simpa only [norm_neg, max_self] using hnormOne)

omit [CompleteSpace H] in
theorem binarySpectralRadius_nonneg (A : H →L[ℂ] H) (k : ℕ) :
    0 ≤ binarySpectralRadius A k := by unfold binarySpectralRadius; positivity

omit [CompleteSpace H] in
theorem binarySpectralRadius_succ (A : H →L[ℂ] H) (k : ℕ) :
    binarySpectralRadius A (k + 1) = binarySpectralRadius A k / 2 := by
  simp only [binarySpectralRadius, pow_succ]
  ring

theorem binarySpectralResidual_selfAdjoint (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (k : ℕ) : IsSelfAdjoint (binarySpectralResidual A k) := by
  induction k with
  | zero => exact hA
  | succ k ih =>
    exact ih.sub (((IsSelfAdjoint.all _).smul
      (rangeSupport_isStarProjection _).isSelfAdjoint).sub
      ((IsSelfAdjoint.all _).smul (IsSelfAdjoint.one (H →L[ℂ] H))))

theorem binarySpectralResidual_norm_le (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (k : ℕ) : ‖binarySpectralResidual A k‖ ≤ binarySpectralRadius A k := by
  induction k with
  | zero => simp [binarySpectralResidual, binarySpectralRadius]
  | succ k ih =>
    rw [binarySpectralRadius_succ]
    exact norm_sub_binarySpectralCorrection_le _
      (binarySpectralResidual_selfAdjoint A hA k) (binarySpectralRadius_nonneg A k) ih

theorem real_smul_mem_vonNeumann (P : VonNeumannAlgebra H) (r : ℝ)
    (T : H →L[ℂ] H) (hT : T ∈ P) : r • T ∈ P := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact P.toStarSubalgebra.smul_mem hT (r : ℂ)

theorem binarySpectralResidual_mem (P : VonNeumannAlgebra H)
    (A : H →L[ℂ] H) (hA : A ∈ P) (k : ℕ) : binarySpectralResidual A k ∈ P := by
  induction k with
  | zero => exact hA
  | succ k ih =>
    exact P.toStarSubalgebra.sub_mem ih (P.toStarSubalgebra.sub_mem
      (real_smul_mem_vonNeumann P _ _ (positive_rangeSupport_mem P _ ih))
      (real_smul_mem_vonNeumann P _ _ P.one_mem))

theorem binarySpectralResidual_eq_sub_sum (A : H →L[ℂ] H) (n : ℕ) :
    binarySpectralResidual A n = A - ∑ k ∈ Finset.range n,
      binarySpectralCorrection (binarySpectralResidual A k) (binarySpectralRadius A k) := by
  induction n with
  | zero => simp [binarySpectralResidual]
  | succ n ih =>
    change binarySpectralResidual A n -
      binarySpectralCorrection (binarySpectralResidual A n) (binarySpectralRadius A n) = _
    rw [Finset.sum_range_succ]
    exact (congrArg (fun T => T -
      binarySpectralCorrection (binarySpectralResidual A n) (binarySpectralRadius A n)) ih).trans
      (by abel)

omit [CompleteSpace H] in
theorem sum_binarySpectralRadius_le (A : H →L[ℂ] H) (n : ℕ) :
    ∑ i : Fin n, |binarySpectralRadius A i| ≤ 2 * ‖A‖ := by
  simp_rw [abs_of_nonneg (binarySpectralRadius_nonneg A _)]
  unfold binarySpectralRadius
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ‖A‖ * (1 / 2 : ℝ) ^ i) n, ← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (sum_geometric_two_le n) (norm_nonneg A)
  simpa only [mul_comm] using h

omit [CompleteSpace H] in
theorem binarySpectralRadius_tendsto_zero (A : H →L[ℂ] H) :
    Filter.Tendsto (binarySpectralRadius A) Filter.atTop (nhds 0) := by
  change Filter.Tendsto (fun k : ℕ => ‖A‖ * (1 / 2 : ℝ) ^ k) _ _
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 1 by norm_num)).const_mul ‖A‖

/-- The accumulated binary corrections have exactly the required scalar
 offset and projection coefficients. -/
theorem spectralStep_binary_eq_sum (A : H →L[ℂ] H) (n : ℕ) :
    spectralStep (-(∑ i : Fin n, binarySpectralRadius A i / 2))
      (fun i : Fin n => binarySpectralRadius A i)
      (fun i : Fin n => rangeSupport (binarySpectralResidual A i)⁺) =
      ∑ k ∈ Finset.range n,
        binarySpectralCorrection (binarySpectralResidual A k) (binarySpectralRadius A k) := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [spectralStep, binarySpectralCorrection, Finset.sum_sub_distrib,
    RCLike.real_smul_eq_coe_smul (K := ℂ), Complex.ofReal_neg, Complex.ofReal_sum,
    neg_smul, ← Finset.sum_smul]
  module

/-- The required published spectral approximation is constructed directly:
 each binary correction halves the residual norm, while all coefficients
 together cost at most twice the original norm. -/
theorem spectralStepApproximation (P : VonNeumannAlgebra H) : SpectralStepApproximation P := by
  intro A hAP hA δ hδ
  have hself : IsSelfAdjoint A := hA
  obtain ⟨n, hn⟩ := ((binarySpectralRadius_tendsto_zero A).eventually
    (gt_mem_nhds hδ)).exists
  refine ⟨n, -(∑ i : Fin n, binarySpectralRadius A i / 2),
    (fun i : Fin n => binarySpectralRadius A i),
    (fun i : Fin n => rangeSupport (binarySpectralResidual A i)⁺), ?_,
    sum_binarySpectralRadius_le A n, ?_⟩
  · intro i
    exact ⟨positive_rangeSupport_mem P _ (binarySpectralResidual_mem P A hAP i),
      (rangeSupport_isStarProjection _).isSelfAdjoint.star_eq,
      (rangeSupport_isStarProjection _).isIdempotentElem.eq⟩
  · rw [spectralStep_binary_eq_sum, ← binarySpectralResidual_eq_sub_sum]
    exact (binarySpectralResidual_norm_le A hself n).trans hn.le

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
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ReducingRepresentationTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

end KadisonSimilarity

end

end OAI
end

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
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SeparableReducingTest
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separable reducing subspaces for finitely many tests

Take the closed complex span of the orbit of finitely many vectors under
words in finitely many operators and their adjoints. The orbit is countable,
so the resulting Hilbert subspace is separable. No representation estimate
or separability assumption on the ambient space is used.
-/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {m r : ℕ}

theorem mem_separableReducingTestSpace (T : Fin m → H →L[ℂ] H)
    (ξ : Fin r → H) (i : Fin r) : ξ i ∈ separableReducingTestSpace T ξ := by
  apply (Submodule.span ℂ (testOrbit T ξ)).le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨([], i), rfl⟩

private theorem testLetter_invariant (T : Fin m → H →L[ℂ] H)
    (ξ : Fin r → H) (a : Fin m × Bool) (x : H)
    (hx : x ∈ separableReducingTestSpace T ξ) :
    testLetter T a x ∈ separableReducingTestSpace T ξ := by
  have hspan : Submodule.span ℂ (testOrbit T ξ) ≤
      (Submodule.span ℂ (testOrbit T ξ)).comap (testLetter T a).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro y ⟨⟨w, i⟩, rfl⟩
    apply Submodule.subset_span
    exact ⟨(a :: w, i), rfl⟩
  have hmap : Set.MapsTo (testLetter T a)
      (Submodule.span ℂ (testOrbit T ξ) : Set H)
      (Submodule.span ℂ (testOrbit T ξ) : Set H) := fun _ hy => hspan hy
  exact hmap.closure (testLetter T a).continuous hx

theorem separableReducingTestSpace_invariant (T : Fin m → H →L[ℂ] H)
    (ξ : Fin r → H) (i : Fin m) (x : H)
    (hx : x ∈ separableReducingTestSpace T ξ) :
    T i x ∈ separableReducingTestSpace T ξ :=
  testLetter_invariant T ξ (i, false) x hx

theorem separableReducingTestSpace_adjoint_invariant (T : Fin m → H →L[ℂ] H)
    (ξ : Fin r → H) (i : Fin m) (x : H)
    (hx : x ∈ separableReducingTestSpace T ξ) :
    (T i).adjoint x ∈ separableReducingTestSpace T ξ :=
  testLetter_invariant T ξ (i, true) x hx

/-- Reduction is an actual projection identity, not merely invariance. -/
theorem separableReducingTestSpace_projection_commutes
    (T : Fin m → H →L[ℂ] H) (ξ : Fin r → H) (i : Fin m) :
    Commute (separableReducingTestSpace T ξ).toSubmodule.starProjection (T i) := by
  let M := separableReducingTestSpace T ξ
  change M.toSubmodule.starProjection * T i = T i * M.toSubmodule.starProjection
  ext x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact separableReducingTestSpace_invariant T ξ i _
      (Submodule.starProjection_apply_mem _ _)
  · intro w hw
    simp only [mul_apply_eq_comp]
    have hzero : inner ℂ (T i (x - M.toSubmodule.starProjection x)) w = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right]
      exact M.toSubmodule.starProjection_inner_eq_zero x _
        (separableReducingTestSpace_adjoint_invariant T ξ i w hw)
    simpa only [map_sub, ContinuousLinearMap.coe_coe] using hzero

/-- Every finite collection of bounded operators and test vectors admits
a common separable closed reducing Hilbert subspace. -/
theorem exists_separable_reducing_test_space
    (T : Fin m → H →L[ℂ] H) (ξ : Fin r → H) :
    ∃ M : ClosedSubmodule ℂ H, TopologicalSpace.SeparableSpace M ∧
      (∀ i, ξ i ∈ M) ∧
      (∀ i x, x ∈ M → T i x ∈ M) ∧
      (∀ i x, x ∈ M → (T i).adjoint x ∈ M) ∧
      (∀ i, Commute M.toSubmodule.starProjection (T i)) :=
  ⟨separableReducingTestSpace T ξ, inferInstance,
    mem_separableReducingTestSpace T ξ,
    separableReducingTestSpace_invariant T ξ,
    separableReducingTestSpace_adjoint_invariant T ξ,
    separableReducingTestSpace_projection_commutes T ξ⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NonseparableReduction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing separability from the uniform commutator estimate

Each operator-norm test involves finitely many matrix entries and finitely
many vectors. Their common reducing subspace is separable. We restrict the
actual C-star algebra generated by those entries, use the two-vector
Kaplansky specialization to reach its bicommutant, and recover the original
vector test by the isometric inclusion.
-/

noncomputable section
universe u
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem matrix_entry_mem_test_algebra {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) (i j : Fin n) :
    X i j ∈ finiteMatrixTestAlgebra X :=
  StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ _ ⟨(i, j), rfl⟩)

theorem finiteMatrixTestAlgebra_le {n : ℕ}
    (P : VonNeumannAlgebra H) (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H))
    (hX : ∀ i j, X i j ∈ P) : finiteMatrixTestAlgebra X ≤ P.toStarSubalgebra := by
  apply StarSubalgebra.topologicalClosure_minimal
  · apply StarAlgebra.adjoin_le
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact hX i j
  · change IsClosed P.carrier
    rw [← P.centralizer_centralizer']
    exact Set.isClosed_centralizer _

/-- A common reducing space for the entries reduces their generated algebra. -/
theorem finiteMatrixTestAlgebra_invariant {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) (M : ClosedSubmodule ℂ H)
    (hX : ∀ i j, Commute M.toSubmodule.starProjection (X i j)) :
    ∀ a : finiteMatrixTestAlgebra X, ∀ x : H, x ∈ M → (a : H →L[ℂ] H) x ∈ M := by
  let q := M.toSubmodule.starProjection
  have hqstar : star q = q := isSelfAdjoint_starProjection M.toSubmodule
  have hle : finiteMatrixTestAlgebra X ≤ StarSubalgebra.centralizer ℂ {q} := by
    apply StarSubalgebra.topologicalClosure_minimal
    · apply StarAlgebra.adjoin_le
      rintro _ ⟨⟨i, j⟩, rfl⟩
      apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
      intro g hg
      obtain rfl := Set.mem_singleton_iff.mp hg
      exact ⟨(hX i j).eq, by simpa only [hqstar] using (hX i j).eq⟩
    · exact Set.isClosed_centralizer _
  intro a x hx
  have hcomm : q * (a : H →L[ℂ] H) = (a : H →L[ℂ] H) * q :=
    ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle a.property) q (Set.mem_singleton q)).1
  apply Submodule.starProjection_eq_self_iff.mp
  have h := congrArg (fun T : H →L[ℂ] H => T x) hcomm
  change q ((a : H →L[ℂ] H) x) = _
  have hfix : q x = x := Submodule.starProjection_eq_self_iff.mpr hx
  simpa only [mul_apply_eq_comp, hfix] using h

/-- A fixed finite test fits in a separable reducing subspace. -/
theorem exists_matrix_test_reducing_space {n : ℕ}
    (Y : H →L[ℂ] H) (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H))
    (ξ : HilbertCopies H n) :
    ∃ M : ClosedSubmodule ℂ H, TopologicalSpace.SeparableSpace M ∧
      (∀ i, ξ i ∈ M) ∧ (∀ x, x ∈ M → Y x ∈ M) ∧
      (∀ i j, Commute M.toSubmodule.starProjection (X i j)) := by
  let e := Fintype.equivFin (Option (Fin n × Fin n))
  let T : Fin (Fintype.card (Option (Fin n × Fin n))) → H →L[ℂ] H := fun k =>
    match e.symm k with
    | none => Y
    | some ij => X ij.1 ij.2
  obtain ⟨M, hsep, hξ, hinv, _, hcomm⟩ := exists_separable_reducing_test_space T (fun i => ξ i)
  refine ⟨M, hsep, hξ, ?_, ?_⟩
  · intro x hx
    simpa only [T, Equiv.symm_apply_apply] using hinv (e none) x hx
  · intro i j
    simpa only [T, Equiv.symm_apply_apply] using hcomm (e (some (i, j)))

omit [CompleteSpace H] in
private theorem norm_mapCopies_subtype (M : ClosedSubmodule ℂ H) (n : ℕ)
    (ξ : HilbertCopies M n) :
    ‖mapCopies M.toSubmodule.subtypeL n ξ‖ = ‖ξ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  rfl

omit [CompleteSpace H] in
private theorem intertwines_commutator {K : Type*}
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (I : K →L[ℂ] H) (Y₀ X₀ : K →L[ℂ] K) (Y X : H →L[ℂ] H)
    (hY : I.comp Y₀ = Y.comp I) (hX : I.comp X₀ = X.comp I) :
    I.comp (commutator Y₀ X₀) = (commutator Y X).comp I := by
  have hy z : I (Y₀ z) = Y (I z) := congrArg (fun T : K →L[ℂ] H => T z) hY
  have hx z : I (X₀ z) = X (I z) := congrArg (fun T : K →L[ℂ] H => T z) hX
  ext z
  change I (Y₀ (X₀ z) - X₀ (Y₀ z)) = Y (X (I z)) - X (Y (I z))
  rw [map_sub, hy, hx, hx, hy]

/-- The uniform estimate on separable Hilbert spaces implies the same
estimate, with the identical constant, on arbitrary Hilbert spaces. -/
theorem uniformCommutatorEstimate_of_separable {C : ℝ} (hC : 0 ≤ C)
    (estimate : SeparableUniformCommutatorEstimate.{u} C)
    (kaplansky : SeparableTwoVectorKaplanskyInput.{u}) : UniformCommutatorEstimate.{u} C := by
  intro H _ _ _ P Y n X hX
  let δ := scalarCommutatorNorm P Y
  have hδ : 0 ≤ δ := scalarCommutatorNorm_nonneg P Y
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro ξ
  obtain ⟨M, hsep, hξ, hY, hXM⟩ := exists_matrix_test_reducing_space Y X ξ
  let : TopologicalSpace.SeparableSpace M := hsep
  let B := finiteMatrixTestAlgebra X
  have hB := finiteMatrixTestAlgebra_le P X hX
  have hM := finiteMatrixTestAlgebra_invariant X M hXM
  let σ := invariantStarRepresentation B M hM
  let Z : M →L[ℂ] M := Y.restrict hY
  let a : Fin n → Fin n → B := fun i j => ⟨X i j, matrix_entry_mem_test_algebra X i j⟩
  let X₀ : Matrix (Fin n) (Fin n) (M →L[ℂ] M) := fun i j => σ (a i j)
  have hZ (b : B) : ‖commutator Z (σ b)‖ ≤ δ * ‖b‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hδ (norm_nonneg b))
    intro x
    change ‖(commutator Y (b : H →L[ℂ] H)) (x : H)‖ ≤ _
    calc
      _ ≤ ‖commutator Y (b : H →L[ℂ] H)‖ * ‖x‖ :=
        (commutator Y (b : H →L[ℂ] H)).le_opNorm x
      _ ≤ (δ * ‖b‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right
          (norm_commutator_le_scalarCommutatorNorm P Y b (hB b.property)) (norm_nonneg x)
  have hscalar : scalarCommutatorNorm (representationVonNeumannAlgebra σ) Z ≤ δ :=
    scalarKaplanskyClosure_of_twoVector σ (representationVonNeumannAlgebra σ)
      (kaplansky M B σ) Z δ hδ hZ
  have hsmall := estimate M (representationVonNeumannAlgebra σ) Z n X₀
    (fun i j => mem_representationVonNeumannAlgebra σ (a i j))
  have hmatrix : ‖matrixOperator X₀‖ ≤ ‖matrixOperator X‖ := by
    let A₀ : CStarMatrix (Fin n) (Fin n) B := CStarMatrix.ofMatrix a
    calc
      ‖matrixOperator X₀‖ = ‖representedMatrix σ A₀‖ := rfl
      _ ≤ ‖A₀‖ := NonUnitalStarAlgHom.norm_apply_le (representedMatrixHom σ n) A₀
      _ = ‖matrixOperator X‖ :=
        (norm_representedMatrix_of_injective B.subtype Subtype.val_injective n A₀).symm
  have hbound : ‖commutator (amplify Z n) (matrixOperator X₀)‖ ≤
      C * δ * ‖matrixOperator X‖ :=
    hsmall.trans (mul_le_mul (mul_le_mul_of_nonneg_left hscalar hC) hmatrix
      (norm_nonneg (matrixOperator X₀)) (mul_nonneg hC hδ))
  let I := mapCopies M.toSubmodule.subtypeL n
  let ξ₀ : HilbertCopies M n := WithLp.toLp 2 (fun i => ⟨ξ i, hξ i⟩)
  have hIξ : I ξ₀ = ξ := by ext i; rfl
  have hIY : I.comp (amplify Z n) = (amplify Y n).comp I := by ext x i; rfl
  have hIX : I.comp (matrixOperator X₀) = (matrixOperator X).comp I :=
    mapCopies_intertwines_matrix M.toSubmodule.subtypeL X₀ X (fun _ _ => rfl)
  have hIcomm := intertwines_commutator I (amplify Z n) (matrixOperator X₀)
    (amplify Y n) (matrixOperator X) hIY hIX
  have he : I (commutator (amplify Z n) (matrixOperator X₀) ξ₀) =
      commutator (amplify Y n) (matrixOperator X) ξ := by
    simpa only [ContinuousLinearMap.comp_apply, hIξ] using
      congrArg (fun T : HilbertCopies M n →L[ℂ] HilbertCopies H n => T ξ₀) hIcomm
  calc
    ‖commutator (amplify Y n) (matrixOperator X) ξ‖ =
        ‖commutator (amplify Z n) (matrixOperator X₀) ξ₀‖ := by
      rw [← he]
      exact norm_mapCopies_subtype M n _
    _ ≤ ‖commutator (amplify Z n) (matrixOperator X₀)‖ * ‖ξ₀‖ :=
      (commutator (amplify Z n) (matrixOperator X₀)).le_opNorm ξ₀
    _ ≤ (C * δ * ‖matrixOperator X‖) * ‖ξ‖ := by
      have hnorm : ‖ξ₀‖ = ‖ξ‖ := by
        rw [← norm_mapCopies_subtype M n ξ₀]
        exact congrArg norm hIξ
      rw [hnorm]
      exact mul_le_mul_of_nonneg_right hbound (norm_nonneg ξ)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_ConditionalMain
attribute [-instance] _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform commutator estimates, hyperreflexivity, and similarity
from central factor models and derivation implementation. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [instance] PublishedSeparableModel.measurable PublishedSeparableModel.normed
  PublishedSeparableModel.inner PublishedSeparableModel.complete
  PublishedSeparableModel.separableFiber

/-- The universal matrix estimate with the manuscript's fixed constant. -/
theorem uniformCommutatorEstimate_of_published (inputs : PublishedUniformInputs.{u}) :
    UniformCommutatorEstimate.{u} universalConstant := by
  apply uniformCommutatorEstimate_of_separable (le_of_lt universalConstant_pos) _ (by
    intro K _ _ _ _ A _ _ _ σ
    exact twoVectorKaplanskyInput σ)
  intro K _ _ _ _ P
  obtain ⟨D⟩ := inputs.separable K P
  exact commutatorEstimate_of_centralDecomposition D.decomposition
    (spectralStepApproximation (vonNeumannCenter P)) D.cases
    (Filter.Eventually.of_forall fun _ => dicksonTwoBound_proved)

/-- Theorem `thm:universal`, conditional only on the named published inputs. -/
theorem universalCommutatorTheorem_of_published (inputs : PublishedUniformInputs.{u}) :
    UniversalCommutatorTheorem.{u} :=
  ⟨universalConstant, le_of_lt universalConstant_pos,
    uniformCommutatorEstimate_of_published inputs⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_UnconditionalMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform matrix commutator estimates and universal hyperreflexivity,
with the numerical constant obtained from the factor estimates and central decomposition. -/

noncomputable section
namespace KadisonSimilarity

universe u v

/-- Theorem `thm:universal` of the manuscript. -/
theorem universalCommutatorTheorem_oai : UniversalCommutatorTheorem.{u} :=
  universalCommutatorTheorem_of_published publishedUniformInputs

end KadisonSimilarity

end

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonSimilarity.universalCommutatorTheorem_oai.{u} := @OAI.KadisonSimilarity.universalCommutatorTheorem_oai.{u}
