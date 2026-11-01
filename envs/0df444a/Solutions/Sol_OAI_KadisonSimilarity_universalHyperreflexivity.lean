-- Prove2me | solution 1 for OAI.KadisonSimilarity.universalHyperreflexivity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T15:12:43.954278+00:00
-- url     : https://prove2.me/submissions/c248d6fe-2c4b-4dab-80d4-cb6456c89114
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A033
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_factorization_of_complete_bound
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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

theorem norm_one_sub_projection_le_one (e : H →L[ℂ] H) (hstar : star e = e)
    (hsq : e * e = e) : ‖1 - e‖ ≤ 1 := by
  apply norm_projection_le_one
  · simp [hstar]
  · calc
      (1 - e) * (1 - e) = 1 - e - e + e * e := by noncomm_ring
      _ = 1 - e := by rw [hsq]; abel

end KadisonSimilarity

end

end OAI
end

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
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Hyperreflexivity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Arveson commutant-distance formula reduces hyperreflexivity to
uniform matrix commutator bounds and the scalar spectral estimate.
The formula is recorded in Christensen, Sinclair, Smith and White,
*Perturbations of C*-algebraic invariants*, Geom. Funct. Anal. 20 (2010),
368–397, Equation (2.1). -/

noncomputable section

namespace KadisonSimilarity

universe u

open scoped ENNReal

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A uniform concrete matrix estimate controls the completely bounded norm. -/
theorem completeCommutatorNorm_le (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
    {C : ℝ} (hC : 0 ≤ C) (estimate : CommutatorEstimate P C) :
    completeCommutatorNorm P Y ≤ ENNReal.ofReal (C * scalarCommutatorNorm P Y) := by
  refine iSup_le fun n => iSup_le fun X => iSup_le fun hXP => iSup_le fun hX => ?_
  apply ENNReal.ofReal_le_ofReal
  calc
    ‖commutator (amplify Y n) (matrixOperator X)‖ ≤
        C * scalarCommutatorNorm P Y * ‖matrixOperator X‖ := estimate Y n X hXP
    _ ≤ C * scalarCommutatorNorm P Y :=
      mul_le_of_le_one_right (mul_nonneg hC (scalarCommutatorNorm_nonneg P Y)) hX

/-- Application of the published distance formula. This deduction contains no
additional analytic hypothesis beyond the stated matrix estimate. -/
theorem twice_distance_le_of_arveson (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    {C : ℝ} (hC : 0 ≤ C) (arveson : ArvesonDistanceFormula M T)
    (estimate : CommutatorEstimate M.commutant C) :
    2 * Metric.infDist T (M : Set (H →L[ℂ] H)) ≤
      C * scalarCommutatorNorm M.commutant T := by
  have h := completeCommutatorNorm_le M.commutant T hC estimate
  rw [arveson] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hC (scalarCommutatorNorm_nonneg M.commutant T))).mp h

/-- The quantitative hyperreflexivity bound from the commutant-distance
formula, a uniform matrix estimate, and the scalar spectral bound. -/
theorem hyperreflexivity_bound_of_arveson (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    {C : ℝ} (hC : 0 ≤ C) (arveson : ArvesonDistanceFormula M T)
    (estimate : CommutatorEstimate M.commutant C)
    (scalarBound : scalarCommutatorNorm M.commutant T ≤ 4 * offDiagonalSeminorm M T) :
    Metric.infDist T (M : Set (H →L[ℂ] H)) ≤ 2 * C * offDiagonalSeminorm M T := by
  have h := twice_distance_le_of_arveson M T hC arveson estimate
  have h' := mul_le_mul_of_nonneg_left scalarBound hC
  nlinarith

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ProjectionCommutators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.vonNeumannInnerDerivation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orthogonal block estimate used before the spectral step approximation. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open ContinuousLinearMap

/-- For a projection, the two off-diagonal blocks control its commutator by
their maximum. The proof uses orthogonal input and output decompositions. -/
theorem norm_commutator_projection_le (T e : H →L[ℂ] H)
    (hstar : star e = e) (hsq : e * e = e) {a : ℝ}
    (hleft : ‖(1 - e) * T * e‖ ≤ a) (hright : ‖e * T * (1 - e)‖ ≤ a) :
    ‖commutator T e‖ ≤ a := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hleft
  have he (ξ : H) : e (e ξ) = e ξ :=
    congrArg (fun R : H →L[ℂ] H => R ξ) hsq
  have hsym (ξ η : H) : inner ℂ (e ξ) η = inner ℂ ξ (e η) := by
    have hself : e.adjoint = e := hstar
    exact (ContinuousLinearMap.eq_adjoint_iff e e).mp hself.symm ξ η
  apply ContinuousLinearMap.opNorm_le_bound _ ha
  intro ξ
  let p : H := e ξ
  let q : H := ξ - e ξ
  let u : H := (1 - e) (T p)
  let v : H := e (T q)
  have heq : e q = 0 := by simp [q, he]
  have hep : e p = p := he ξ
  have heu : e u = 0 := by simp [u, he]
  have hpq : inner ℂ p q = 0 := by
    rw [show p = e ξ from rfl, hsym, heq, inner_zero_right]
  have huv : inner ℂ u v = 0 := by
    rw [show v = e (T q) from rfl, ← hsym, heu, inner_zero_left]
  have hpqnorm : ‖ξ‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p q hpq
    have hpqsum : p + q = ξ := by dsimp [p, q]; abel
    simpa only [hpqsum, ← pow_two] using h
  have huvnorm : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u (-v) (by
      simpa using huv)
    simpa only [sub_eq_add_neg, norm_neg, ← pow_two] using h
  have hcomm : (commutator T e) ξ = u - v := by
    simp only [commutator, sub_apply, u, v, q, p, map_sub]
    abel
  have hu : ‖u‖ ≤ a * ‖p‖ := by
    calc
      ‖u‖ = ‖((1 - e) * T * e) p‖ := by simp [u, hep]
      _ ≤ ‖(1 - e) * T * e‖ * ‖p‖ := le_opNorm _ _
      _ ≤ a * ‖p‖ := mul_le_mul_of_nonneg_right hleft (norm_nonneg p)
  have hv : ‖v‖ ≤ a * ‖q‖ := by
    calc
      ‖v‖ = ‖(e * T * (1 - e)) q‖ := by simp [v, heq]
      _ ≤ ‖e * T * (1 - e)‖ * ‖q‖ := le_opNorm _ _
      _ ≤ a * ‖q‖ := mul_le_mul_of_nonneg_right hright (norm_nonneg q)
  have hsqbound : ‖(commutator T e) ξ‖ ^ 2 ≤ (a * ‖ξ‖) ^ 2 := by
    calc
      ‖(commutator T e) ξ‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by rw [hcomm, huvnorm]
      _ ≤ (a * ‖p‖) ^ 2 + (a * ‖q‖) ^ 2 :=
        add_le_add (pow_le_pow_left₀ (norm_nonneg u) hu 2)
          (pow_le_pow_left₀ (norm_nonneg v) hv 2)
      _ = a ^ 2 * (‖p‖ ^ 2 + ‖q‖ ^ 2) := by ring
      _ = (a * ‖ξ‖) ^ 2 := by rw [← hpqnorm]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha (norm_nonneg ξ))).mp hsqbound

private theorem offDiagonalValue_le_norm (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) (e : CommutantProjection M) :
    ‖(1 - e.val) * T * e.val‖ ≤ ‖T‖ := by
  have he := norm_projection_le_one e.val e.property.2.1 e.property.2.2
  have he' := norm_one_sub_projection_le_one e.val e.property.2.1 e.property.2.2
  calc
    ‖(1 - e.val) * T * e.val‖ ≤ (‖1 - e.val‖ * ‖T‖) * ‖e.val‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg e.val))
    _ ≤ (1 * ‖T‖) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right he' (norm_nonneg T)) he
        (norm_nonneg e.val) (by positivity)
    _ = ‖T‖ := by ring

/-- Each defining off-diagonal block is bounded by the distance seminorm. -/
theorem norm_offDiagonal_le (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (e : CommutantProjection M) :
    ‖(1 - e.val) * T * e.val‖ ≤ offDiagonalSeminorm M T := by
  apply le_csSup
  · refine ⟨‖T‖, ?_⟩
    rintro r ⟨f, rfl⟩
    exact offDiagonalValue_le_norm M T f
  · exact ⟨e, rfl⟩

/-- The off-diagonal distance seminorm is nonnegative. -/
theorem offDiagonalSeminorm_nonneg (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    0 ≤ offDiagonalSeminorm M T := by
  let e₀ : CommutantProjection M := ⟨0, by simp⟩
  exact (norm_nonneg _).trans (norm_offDiagonal_le M T e₀)

/-- The first estimate in the manuscript's hyperreflexivity proof. -/
theorem norm_commutator_projection_le_offDiagonal (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) (e : CommutantProjection M) :
    ‖commutator T e.val‖ ≤ offDiagonalSeminorm M T := by
  apply norm_commutator_projection_le T e.val e.property.2.1 e.property.2.2
  · exact norm_offDiagonal_le M T e
  · have h := norm_offDiagonal_le M T (complementProjection e)
    simpa only [complementProjection, sub_sub_cancel] using h

/-- Real/imaginary decomposition reduces the scalar estimate to a bound on
selfadjoint elements. -/
theorem scalarCommutatorNorm_le_four_of_selfAdjoint (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H)
    (selfAdjointBound : ∀ A : H →L[ℂ] H, A ∈ M.commutant → star A = A →
      ‖commutator T A‖ ≤ 2 * offDiagonalSeminorm M T * ‖A‖) :
    scalarCommutatorNorm M.commutant T ≤ 4 * offDiagonalSeminorm M T := by
  have hα := offDiagonalSeminorm_nonneg M T
  apply (scalarCommutatorNorm_le_iff M.commutant T (by positivity)).mpr
  intro A hA
  have hAstar : star A ∈ M.commutant := star_mem hA
  let b : H →L[ℂ] H := realPart A
  let c : H →L[ℂ] H := imaginaryPart A
  have hb : b ∈ M.commutant := by
    dsimp [b]
    rw [realPart_apply_coe, ← Complex.coe_smul]
    exact M.commutant.toStarSubalgebra.smul_mem
      (M.commutant.add_mem hA hAstar) _
  have hc : c ∈ M.commutant := by
    dsimp [c]
    rw [imaginaryPart_apply_coe, ← Complex.coe_smul]
    exact M.commutant.toStarSubalgebra.smul_mem
      (M.commutant.toStarSubalgebra.smul_mem
        (M.commutant.sub_mem hA hAstar) _) _
  have hbself : star b = b := (realPart A).property
  have hcself : star c = c := (imaginaryPart A).property
  have hsplit : commutator T A = commutator T b + Complex.I • commutator T c := by
    change innerDerivation T A = innerDerivation T b + Complex.I • innerDerivation T c
    rw [← realPart_add_I_smul_imaginaryPart A]
    simp only [map_add, map_smul, b, c]
  calc
    ‖commutator T A‖ ≤ ‖commutator T b‖ + ‖commutator T c‖ := by
      rw [hsplit]
      simpa only [norm_smul, Complex.norm_I, one_mul] using
        norm_add_le (commutator T b) (Complex.I • commutator T c)
    _ ≤ 2 * offDiagonalSeminorm M T * ‖b‖ + 2 * offDiagonalSeminorm M T * ‖c‖ :=
      add_le_add (selfAdjointBound b hb hbself) (selfAdjointBound c hc hcself)
    _ ≤ 2 * offDiagonalSeminorm M T * ‖A‖ + 2 * offDiagonalSeminorm M T * ‖A‖ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (realPart.norm_le A) (by positivity)
      · exact mul_le_mul_of_nonneg_left (imaginaryPart.norm_le A) (by positivity)
    _ = 4 * offDiagonalSeminorm M T * ‖A‖ := by ring

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralSteps
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- A finite spectral sum is controlled by the total variation of its coefficients. -/
theorem norm_commutator_spectralStep_le (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    {n : ℕ} (r : ℝ) (c : Fin n → ℝ) (e : Fin n → H →L[ℂ] H)
    (he : ∀ i, e i ∈ M.commutant ∧ star (e i) = e i ∧ e i * e i = e i) :
    ‖commutator T (spectralStep r c e)‖ ≤
      (∑ i, |c i|) * offDiagonalSeminorm M T := by
  rw [commutator_spectralStep]
  calc
    ‖∑ i, (c i : ℂ) • commutator T (e i)‖ ≤
        ∑ i, ‖(c i : ℂ) • commutator T (e i)‖ := norm_sum_le _ _
    _ = ∑ i, |c i| * ‖commutator T (e i)‖ := by simp [norm_smul]
    _ ≤ ∑ i, |c i| * offDiagonalSeminorm M T := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (norm_commutator_projection_le_offDiagonal M T ⟨e i, he i⟩) (abs_nonneg _)
    _ = (∑ i, |c i|) * offDiagonalSeminorm M T := by rw [Finset.sum_mul]

/-- The projection approximation yields the claimed sharp scalar-level factor
`2` for a selfadjoint input. -/
theorem norm_commutator_selfAdjoint_of_spectralSteps (M : VonNeumannAlgebra H)
    (approximation : SpectralStepApproximation M.commutant) (T A : H →L[ℂ] H)
    (hA : A ∈ M.commutant) (hAstar : star A = A) :
    ‖commutator T A‖ ≤ 2 * offDiagonalSeminorm M T * ‖A‖ := by
  have hα := offDiagonalSeminorm_nonneg M T
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (2 * ‖T‖ + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨n, r, c, e, he, hc, herr⟩ := approximation A hA hAstar δ hδ
  have hstep := norm_commutator_spectralStep_le M T r c e he
  have hclose : ‖commutator T A - commutator T (spectralStep r c e)‖ ≤ 2 * ‖T‖ * δ := by
    have heq : commutator T A - commutator T (spectralStep r c e) =
        commutator T (A - spectralStep r c e) := by
      change innerDerivation T A - innerDerivation T (spectralStep r c e) =
        innerDerivation T (A - spectralStep r c e)
      exact (map_sub _ _ _).symm
    rw [heq]
    exact (norm_commutator_le _ _).trans (mul_le_mul_of_nonneg_left herr (by positivity))
  have hδε : 2 * ‖T‖ * δ ≤ ε := by
    have hden : 0 < 2 * ‖T‖ + 1 := by positivity
    dsimp [δ]
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith
  calc
    ‖commutator T A‖ ≤ ‖commutator T (spectralStep r c e)‖ +
        ‖commutator T A - commutator T (spectralStep r c e)‖ := norm_le_insert' _ _
    _ ≤ (2 * ‖A‖) * offDiagonalSeminorm M T + 2 * ‖T‖ * δ :=
      add_le_add (hstep.trans (mul_le_mul_of_nonneg_right hc hα)) hclose
    _ ≤ 2 * offDiagonalSeminorm M T * ‖A‖ + ε := by nlinarith

/-- The real/imaginary decomposition now yields the scalar factor `4`. -/
theorem scalarCommutatorNorm_le_four_of_spectralSteps (M : VonNeumannAlgebra H)
    (approximation : SpectralStepApproximation M.commutant) (T : H →L[ℂ] H) :
    scalarCommutatorNorm M.commutant T ≤ 4 * offDiagonalSeminorm M T := by
  apply scalarCommutatorNorm_le_four_of_selfAdjoint M T
  intro A hA hAstar
  exact norm_commutator_selfAdjoint_of_spectralSteps M approximation T A hA hAstar

/-- Spectral approximation and the uniform commutator estimate imply the
hyperreflexivity bound with constant `2 * C`. -/
theorem hyperreflexivity_of_spectralSteps_and_arveson (M : VonNeumannAlgebra H)
    (approximation : SpectralStepApproximation M.commutant) (T : H →L[ℂ] H)
    {C : ℝ} (hC : 0 ≤ C) (arveson : ArvesonDistanceFormula M T)
    (estimate : CommutatorEstimate M.commutant C) :
    Metric.infDist T (M : Set (H →L[ℂ] H)) ≤ 2 * C * offDiagonalSeminorm M T :=
  hyperreflexivity_bound_of_arveson M T hC arveson estimate
    (scalarCommutatorNorm_le_four_of_spectralSteps M approximation T)

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
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_ArvesonLowerBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.vonNeumannInnerDerivation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary direction of the Arveson distance identity: subtracting
an element of the commutant bounds every matrix commutator by twice the
distance. The converse distance estimate remains a separate input. -/

noncomputable section
namespace KadisonSimilarity
open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem amplified_commutator_eq_zero_of_mem
    (M : VonNeumannAlgebra H) (S : H →L[ℂ] H) (hS : S ∈ M)
    {n : ℕ} (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H))
    (hX : ∀ i j, X i j ∈ M.commutant) :
    commutator (amplify S n) (matrixOperator X) = 0 := by
  rw [commutator_amplify_matrixOperator]
  have he (i j : Fin n) : commutator S (X i j) = 0 := by
    have h := VonNeumannAlgebra.mem_commutant_iff.mp (hX i j) S hS
    exact sub_eq_zero.mpr h
  have hfun : (fun i j => commutator S (X i j)) =
      (0 : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) := by
    funext i j
    exact he i j
  rw [hfun]
  apply ContinuousLinearMap.ext
  intro ξ
  apply PiLp.ext
  intro i
  simp [matrixOperator]

theorem matrix_commutator_le_twice_distance
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    {n : ℕ} (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H))
    (hX : ∀ i j, X i j ∈ M.commutant) (hXn : ‖matrixOperator X‖ ≤ 1) :
    ‖commutator (amplify T n) (matrixOperator X)‖ ≤
      2 * Metric.infDist T (M : Set (H →L[ℂ] H)) := by
  have hdist : ‖commutator (amplify T n) (matrixOperator X)‖ / 2 ≤
      Metric.infDist T (M : Set (H →L[ℂ] H)) := by
    apply (Metric.le_infDist ⟨0, M.zero_mem⟩).mpr
    intro S hS
    have hzero := amplified_commutator_eq_zero_of_mem M S hS X hX
    have hb := norm_commutator_le_of_approx (amplify T n) (amplify S n)
      (matrixOperator X) (a := 0) (d := ‖T - S‖)
      (by rw [hzero, norm_zero]) (norm_amplify_sub_le T S n)
    have hc : 2 * ‖T - S‖ * ‖matrixOperator X‖ ≤ 2 * ‖T - S‖ :=
      mul_le_of_le_one_right (by positivity) hXn
    rw [dist_eq_norm]
    linarith
  linarith

/-- The completely bounded commutator norm never exceeds twice the distance. -/
theorem completeCommutatorNorm_le_twice_distance
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    completeCommutatorNorm M.commutant T ≤
      ENNReal.ofReal (2 * Metric.infDist T (M : Set (H →L[ℂ] H))) := by
  refine iSup_le fun n => iSup_le fun X => iSup_le fun hX => iSup_le fun hXn => ?_
  exact ENNReal.ofReal_le_ofReal (matrix_commutator_le_twice_distance M T X hX hXn)

/-- Thus only the reverse distance bound is needed for the exact identity. -/
theorem arvesonDistanceFormula_iff_reverse_bound
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    ArvesonDistanceFormula M T ↔
      ENNReal.ofReal (2 * Metric.infDist T (M : Set (H →L[ℂ] H))) ≤
        completeCommutatorNorm M.commutant T := by
  constructor
  · intro h
    exact h.ge
  · intro h
    exact le_antisymm (completeCommutatorNorm_le_twice_distance M T) h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_DerivationDefectSpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reducing defect space of a factorized derivation. It will provide
the sharp implementing operator in the commutant-distance formula. -/

noncomputable section
namespace KadisonSimilarity
open scoped Topology

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem derivationDefect_mem (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) (a : A) (x : H) :
    derivationDefect σ π W a x ∈ derivationDefectSpace σ π W := by
  apply (Submodule.span ℂ (Set.range fun p : A × H =>
    derivationDefect σ π W p.1 p.2)).le_topologicalClosure
  exact Submodule.subset_span ⟨(a, x), rfl⟩

theorem derivationDefect_mul (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) (b a : A) :
    (π b).comp (derivationDefect σ π W a) =
      derivationDefect σ π W (b * a) - (derivationDefect σ π W b).comp (σ a) := by
  ext x
  simp only [derivationDefect, ContinuousLinearMap.comp_apply, _root_.sub_apply,
    map_sub, map_mul, mul_apply_eq_comp]
  abel

theorem derivationDefectSpace_invariant (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K)
    (b : A) (x : K) (hx : x ∈ derivationDefectSpace σ π W) :
    π b x ∈ derivationDefectSpace σ π W := by
  let Q := derivationDefectSpace σ π W
  have hspan : Submodule.span ℂ (Set.range fun p : A × H =>
      derivationDefect σ π W p.1 p.2) ≤ Q.toSubmodule.comap (π b).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro y ⟨⟨a, z⟩, rfl⟩
    change π b (derivationDefect σ π W a z) ∈ Q
    have he := congrArg (fun T : H →L[ℂ] K => T z) (derivationDefect_mul σ π W b a)
    change π b (derivationDefect σ π W a z) =
      derivationDefect σ π W (b * a) z - derivationDefect σ π W b (σ a z) at he
    rw [he]
    exact Q.sub_mem (derivationDefect_mem σ π W _ _) (derivationDefect_mem σ π W _ _)
  exact closure_minimal hspan (Q.isClosed.preimage (π b).continuous) hx

/-- The left factor intertwines the two representations on the defect space. -/
theorem derivationDefectSpace_intertwines
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (π : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (U : K →L[ℂ] H) (W : H →L[ℂ] K) (δ : A →L[ℂ] (H →L[ℂ] H))
    (hδ : ∀ a b, δ (a * b) = (σ a).comp (δ b) + (δ a).comp (σ b))
    (hF : ∀ a, U.comp ((π a).comp W) = δ a) (hUW : U.comp W = 0)
    (b : A) (x : K) (hx : x ∈ derivationDefectSpace σ π W) :
    U (π b x) = σ b (U x) := by
  have hUd (a : A) : U.comp (derivationDefect σ π W a) = δ a := by
    simp only [derivationDefect, ContinuousLinearMap.comp_sub,
      ← ContinuousLinearMap.comp_assoc, hUW, ContinuousLinearMap.zero_comp, sub_zero]
    exact hF a
  have hgen (a : A) :
      U.comp ((π b).comp (derivationDefect σ π W a)) = (σ b).comp (δ a) := by
    rw [derivationDefect_mul, ContinuousLinearMap.comp_sub,
      ← ContinuousLinearMap.comp_assoc U (derivationDefect σ π W b) (σ a),
      hUd, hUd, hδ]
    abel
  have hspan : Submodule.span ℂ (Set.range fun p : A × H =>
      derivationDefect σ π W p.1 p.2) ≤
      (U.comp (π b) - (σ b).comp U).ker := by
    apply Submodule.span_le.mpr
    rintro y ⟨⟨a, z⟩, rfl⟩
    change U (π b (derivationDefect σ π W a z)) -
      σ b (U (derivationDefect σ π W a z)) = 0
    have hg := congrArg (fun T : H →L[ℂ] H => T z) (hgen a)
    have hd := congrArg (fun T : H →L[ℂ] H => T z) (hUd a)
    change U (π b (derivationDefect σ π W a z)) = σ b (δ a z) at hg
    change U (derivationDefect σ π W a z) = δ a z at hd
    rw [hg, hd, sub_self]
  have hc := closure_minimal hspan
    (U.comp (π b) - (σ b).comp U).isClosed_ker hx
  exact sub_eq_zero.mp hc

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CenteredProjectionNorm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centering an orthogonal projection at one half gives norm at most one half. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_projection_sub_half_le (P : H →L[ℂ] H) (hP : IsStarProjection P) :
    ‖P - (1 / 2 : ℝ) • 1‖ ≤ 1 / 2 := by
  have hP1 : P ≤ 1 := sub_nonneg.mp hP.one_sub.nonneg
  have hlo : -((1 / 2 : ℝ) • (1 : H →L[ℂ] H)) ≤ P - (1 / 2 : ℝ) • 1 := by
    simpa only [zero_sub] using sub_le_sub_right hP.nonneg ((1 / 2 : ℝ) • 1)
  have hone : (1 : H →L[ℂ] H) - (1 / 2 : ℝ) • 1 = (1 / 2 : ℝ) • 1 := by
    calc
      _ = (1 : ℝ) • (1 : H →L[ℂ] H) - (1 / 2 : ℝ) • 1 := by rw [one_smul]
      _ = (1 - 1 / 2 : ℝ) • (1 : H →L[ℂ] H) := (sub_smul _ _ _).symm
      _ = (1 / 2 : ℝ) • (1 : H →L[ℂ] H) := by norm_num
  have hhi : P - (1 / 2 : ℝ) • 1 ≤ (1 / 2 : ℝ) • 1 := by
    simpa only [hone] using sub_le_sub_right hP1 ((1 / 2 : ℝ) • 1)
  have hself : IsSelfAdjoint (P - (1 / 2 : ℝ) • 1) :=
    hP.isSelfAdjoint.sub ((IsSelfAdjoint.all (1 / 2 : ℝ)).smul (IsSelfAdjoint.one _))
  have h := IsSelfAdjoint.norm_le_max_of_le_of_le hlo hhi hself
  have hn : ‖(1 / 2 : ℝ) • (1 : H →L[ℂ] H)‖ ≤ 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_of_le_one_right (by norm_num) ContinuousLinearMap.norm_id_le
  exact h.trans (by simpa only [norm_neg, max_self] using hn)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_SharpDerivationImplementation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A factorized derivation has an implementer with half the product norm.
The defect projection can be centered because the two factors have zero product. -/

noncomputable section
namespace KadisonSimilarity

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem sharp_implementation_of_factorization
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (π : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (U : K →L[ℂ] H) (W : H →L[ℂ] K) (δ : A →L[ℂ] (H →L[ℂ] H))
    (hδ : ∀ a b, δ (a * b) = (σ a).comp (δ b) + (δ a).comp (σ b))
    (hF : ∀ a, U.comp ((π a).comp W) = δ a) (hUW : U.comp W = 0) :
    ∃ V : H →L[ℂ] H, (∀ a, δ a = V.comp (σ a) - (σ a).comp V) ∧
      ‖V‖ ≤ ‖U‖ * ‖W‖ / 2 := by
  let Q := derivationDefectSpace σ π W
  let P := Q.toSubmodule.starProjection
  have hP : IsStarProjection P := isStarProjection_starProjection (U := Q.toSubmodule)
  have hmem (x : K) : P x ∈ Q := Q.toSubmodule.starProjection_apply_mem x
  have hcomm (a : A) : Commute P (π a) :=
    orthogonal_projection_commutes π (fun a => π.map_star' a) Q
      (fun a x hx => derivationDefectSpace_invariant σ π W a x hx) a
  have hfix (a : A) (x : H) : P (derivationDefect σ π W a x) =
      derivationDefect σ π W a x :=
    Q.toSubmodule.starProjection_eq_self_iff.mpr (derivationDefect_mem σ π W a x)
  have hUd (a : A) : U.comp (derivationDefect σ π W a) = δ a := by
    simp only [derivationDefect, ContinuousLinearMap.comp_sub,
      ← ContinuousLinearMap.comp_assoc, hUW, ContinuousLinearMap.zero_comp, sub_zero]
    exact hF a
  let Z : H →L[ℂ] H := U.comp (P.comp W)
  have himpl (a : A) : δ a = (σ a).comp Z - Z.comp (σ a) := by
    ext x
    have hd := congrArg (fun T : H →L[ℂ] H => T x) (hUd a)
    change U (derivationDefect σ π W a x) = δ a x at hd
    have hc := congrArg (fun T : K →L[ℂ] K => T (W x)) (hcomm a).eq
    change P (π a (W x)) = π a (P (W x)) at hc
    calc
      δ a x = U (P (derivationDefect σ π W a x)) := by rw [hfix]; exact hd.symm
      _ = U (P (π a (W x))) - U (P (W (σ a x))) := by
        simp only [derivationDefect, _root_.sub_apply, ContinuousLinearMap.comp_apply, map_sub]
      _ = U (π a (P (W x))) - U (P (W (σ a x))) := by rw [hc]
      _ = σ a (U (P (W x))) - U (P (W (σ a x))) := by
        rw [derivationDefectSpace_intertwines σ π U W δ hδ hF hUW a _ (hmem (W x))]
      _ = ((σ a).comp Z - Z.comp (σ a)) x := rfl
  have hcenter : Z = U.comp ((P - (1 / 2 : ℝ) • 1).comp W) := by
    ext x
    have hz := congrArg (fun T : H →L[ℂ] H => T x) hUW
    change U (W x) = 0 at hz
    change U (P (W x)) = U ((P - (1 / 2 : ℝ) • 1) (W x))
    simp only [_root_.sub_apply, _root_.smul_apply, one_apply_eq_self, map_sub]
    rw [U.map_smul_of_tower (1 / 2 : ℝ), hz, smul_zero, sub_zero]
  have hnorm : ‖Z‖ ≤ ‖U‖ * ‖W‖ / 2 := by
    rw [hcenter]
    calc
      _ ≤ ‖U‖ * ‖(P - (1 / 2 : ℝ) • 1).comp W‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖U‖ * (‖P - (1 / 2 : ℝ) • 1‖ * ‖W‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ ≤ ‖U‖ * ((1 / 2 : ℝ) * ‖W‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (norm_projection_sub_half_le P hP) (norm_nonneg _))
          (norm_nonneg _)
      _ = ‖U‖ * ‖W‖ / 2 := by ring
  refine ⟨-Z, ?_, by simpa only [norm_neg] using hnorm⟩
  intro a
  rw [himpl]
  ext x
  simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply, neg_apply, map_neg]
  abel

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_SharpCompletelyBoundedDerivation
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp implementation bound for completely bounded derivations,
using the proved completely bounded factorization. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
theorem derivation_map_one_eq_zero
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (δ : A →L[ℂ] (H →L[ℂ] H))
    (hδ : ∀ a b, δ (a * b) = (σ a).comp (δ b) + (δ a).comp (σ b)) : δ 1 = 0 := by
  have h := hδ 1 1
  simp only [one_mul, map_one, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] at h
  have hz : δ 1 + 0 = δ 1 + δ 1 := by simpa only [add_zero] using h
  exact (add_left_cancel hz).symm

theorem sharp_implementation_of_complete_bound
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (δ : A →L[ℂ] (H →L[ℂ] H))
    (hδ : ∀ a b, δ (a * b) = (σ a).comp (δ b) + (δ a).comp (σ b))
    {C : ℝ} (hC : 0 < C)
    (hcb : ∀ n (X : CStarMatrix (Fin n) (Fin n) A), ‖X.map δ.toLinearMap‖ ≤ C * ‖X‖) :
    ∃ V : H →L[ℂ] H, (∀ a, δ a = V.comp (σ a) - (σ a).comp V) ∧ ‖V‖ ≤ C / 2 := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · let := hH
    refine ⟨0, fun _ => Subsingleton.elim _ _, ?_⟩
    simpa only [norm_zero] using (div_nonneg hC.le (by norm_num : (0 : ℝ) ≤ 2))
  · let := hH
    have h01 : (0 : A) ≠ 1 := by
      intro h
      have he := congrArg σ h
      exact zero_ne_one (by simpa only [map_zero, map_one] using he)
    let : Nontrivial A := ⟨⟨0, 1, h01⟩⟩
    obtain ⟨F⟩ := BoundedHochschild.KadisonRingrose.factorization_of_complete_bound
      δ.toLinearMap hC hcb
    have hUW : F.leftMap.adjoint.comp F.rightMap = 0 := by
      have h := F.factorization 1
      change δ 1 = F.leftMap.adjoint.comp ((F.representation 1).comp F.rightMap) at h
      rw [derivation_map_one_eq_zero σ δ hδ] at h
      simpa only [map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] using h.symm
    obtain ⟨V, hV, hn⟩ := sharp_implementation_of_factorization σ F.representation
      F.leftMap.adjoint F.rightMap δ hδ (fun a => (F.factorization a).symm) hUW
    refine ⟨V, hV, hn.trans ?_⟩
    apply div_le_div_of_nonneg_right _ (by norm_num)
    simpa only [ContinuousLinearMap.adjoint.norm_map] using F.bound

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_ArvesonCompleteNorm
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete completely bounded commutator norm controls the actual
entrywise C-star matrix amplifications needed for factorization. -/

noncomputable section
namespace KadisonSimilarity
open scoped ENNReal ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem entrywise_bound_of_unit_ball (T : A →ₗ[ℂ] (H →L[ℂ] H)) {C : ℝ}
    (hunit : ∀ n (X : CStarMatrix (Fin n) (Fin n) A), ‖X‖ ≤ 1 → ‖X.map T‖ ≤ C)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) : ‖X.map T‖ ≤ C * ‖X‖ := by
  by_cases hx : X = 0
  · subst X
    have hz : CStarMatrix.map (0 : CStarMatrix (Fin n) (Fin n) A) T = 0 := by
      apply CStarMatrix.ext
      intro i j
      exact T.map_zero
    simp only [hz, norm_zero, mul_zero, le_refl]
  have hr : 0 < ‖X‖ := norm_pos_iff.mpr hx
  let c : ℂ := (‖X‖ : ℂ)⁻¹
  have hc : ‖c‖ = ‖X‖⁻¹ := by
    simp only [c, norm_inv, Complex.norm_real, norm_norm]
  have hy : ‖c • X‖ ≤ 1 := by
    rw [norm_smul, hc, inv_mul_cancel₀ hr.ne']
  have he : (c • X).map T = c • X.map T := by
    apply CStarMatrix.ext
    intro i j
    exact T.map_smul c (X i j)
  have hb := hunit n (c • X) hy
  rw [he, norm_smul, hc] at hb
  calc
    ‖X.map T‖ = ‖X‖ * (‖X‖⁻¹ * ‖X.map T‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
    _ ≤ ‖X‖ * C := mul_le_mul_of_nonneg_left hb hr.le
    _ = C * ‖X‖ := mul_comm _ _

attribute [local instance] OAI.KadisonSimilarity.arvesonComplete_closed
theorem commutantDerivation_leibniz (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (a b : M.commutant.toStarSubalgebra) :
    commutantDerivation M T (a * b) =
      (a : H →L[ℂ] H).comp (commutantDerivation M T b) +
      (commutantDerivation M T a).comp (b : H →L[ℂ] H) := by
  change T * ((a : H →L[ℂ] H) * (b : H →L[ℂ] H)) -
    ((a : H →L[ℂ] H) * (b : H →L[ℂ] H)) * T =
      (a : H →L[ℂ] H) * (T * (b : H →L[ℂ] H) - (b : H →L[ℂ] H) * T) +
      (T * (a : H →L[ℂ] H) - (a : H →L[ℂ] H) * T) * (b : H →L[ℂ] H)
  noncomm_ring

theorem commutantDerivation_complete_bound (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (hb : completeCommutatorNorm M.commutant T ≤ ENNReal.ofReal C)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) M.commutant.toStarSubalgebra) :
    ‖X.map (commutantDerivation M T).toLinearMap‖ ≤ C * ‖X‖ := by
  apply entrywise_bound_of_unit_ball
  intro m Y hY
  let Z : Matrix (Fin m) (Fin m) (H →L[ℂ] H) := fun i j => (Y i j : H →L[ℂ] H)
  have hZ : ‖matrixOperator Z‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le
      (representedMatrixHom M.commutant.toStarSubalgebra.subtype m) Y).trans hY
  have hsup : ENNReal.ofReal ‖commutator (amplify T m) (matrixOperator Z)‖ ≤
      completeCommutatorNorm M.commutant T := by
    exact le_iSup_of_le m (le_iSup_of_le Z
      (le_iSup_of_le (fun i j => (Y i j).property) (le_iSup_of_le hZ le_rfl)))
  have hn := (ENNReal.ofReal_le_ofReal_iff hC).mp (hsup.trans hb)
  rw [← norm_matrixOperator_eq m]
  have he : matrixOperator
      (CStarMatrix.ofMatrix.symm (Y.map (commutantDerivation M T).toLinearMap)) =
      commutator (amplify T m) (matrixOperator Z) := by
    rw [commutator_amplify_matrixOperator]
    rfl
  rw [he]
  exact hn

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_ArvesonDischarge
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Arveson commutant-distance identity follows from the sharp
implementation theorem for completely bounded derivations. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped ENNReal Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance arvesonDischarge_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed M.carrier
  rw [← M.centralizer_centralizer']
  exact Set.isClosed_centralizer _

theorem twice_distance_le_of_complete_bound (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) {C : ℝ} (hC : 0 < C)
    (hb : completeCommutatorNorm M.commutant T ≤ ENNReal.ofReal C) :
    2 * Metric.infDist T (M : Set (H →L[ℂ] H)) ≤ C := by
  let σ := M.commutant.toStarSubalgebra.subtype
  let δ := commutantDerivation M T
  obtain ⟨V, hV, hn⟩ := sharp_implementation_of_complete_bound σ δ
    (commutantDerivation_leibniz M T) hC (commutantDerivation_complete_bound M T hC.le hb)
  have hmem : T - V ∈ M := by
    rw [← M.commutant_commutant]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    have he := hV ⟨a, ha⟩
    change commutator T a = commutator V a at he
    have hz : commutator (T - V) a = 0 := by rw [commutator_sub_left, he, sub_self]
    exact (sub_eq_zero.mp hz).symm
  have hd := Metric.infDist_le_dist_of_mem hmem (x := T)
  have he : T - (T - V) = V := by abel
  rw [dist_eq_norm, he] at hd
  linarith

/-- The precise CSSW (2010), Equation (2.1), specialization is proved. -/
theorem arvesonDistanceFormula (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    ArvesonDistanceFormula M T := by
  let b := completeCommutatorNorm M.commutant T
  have hb : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (completeCommutatorNorm_le_twice_distance M T)
  let r := b.toReal
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  have happrox (n : ℕ) : 2 * Metric.infDist T (M : Set (H →L[ℂ] H)) ≤
      r + (1 / 2 : ℝ) ^ n := by
    apply twice_distance_le_of_complete_bound M T (by positivity)
    change b ≤ ENNReal.ofReal (r + (1 / 2 : ℝ) ^ n)
    calc
      b = ENNReal.ofReal r := (ENNReal.ofReal_toReal hb).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (by positivity))
  have hlim : Tendsto (fun n : ℕ => r + (1 / 2 : ℝ) ^ n) atTop (𝓝 r) := by
    have hc : Tendsto (fun _ : ℕ => r) atTop (𝓝 r) := tendsto_const_nhds
    have h := hc.add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
    simpa only [add_zero] using h
  have hd : 2 * Metric.infDist T (M : Set (H →L[ℂ] H)) ≤ r :=
    ge_of_tendsto hlim (Eventually.of_forall happrox)
  apply (arvesonDistanceFormula_iff_reverse_bound M T).mpr
  calc
    _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal hd
    _ = b := ENNReal.ofReal_toReal hb

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

/-- Corollary `cor:hyperreflexivity`, with the same universal constant and
the commutant-distance formula now proved. -/
theorem universalHyperreflexivity_of_published (inputs : PublishedUniformInputs.{u}) :
    UniversalHyperreflexivity.{u} universalConstant := by
  intro K _ _ _ M T
  exact hyperreflexivity_of_spectralSteps_and_arveson M (spectralStepApproximation M.commutant) T
    (le_of_lt universalConstant_pos) (arvesonDistanceFormula M T)
    (uniformCommutatorEstimate_of_published inputs K M.commutant)

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

/-- Corollary `cor:hyperreflexivity` of the manuscript. -/
theorem universalHyperreflexivity_oai : UniversalHyperreflexivity.{u} universalConstant :=
  universalHyperreflexivity_of_published publishedUniformInputs

end KadisonSimilarity

end

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonSimilarity.universalHyperreflexivity_oai.{u} := @OAI.KadisonSimilarity.universalHyperreflexivity_oai.{u}
