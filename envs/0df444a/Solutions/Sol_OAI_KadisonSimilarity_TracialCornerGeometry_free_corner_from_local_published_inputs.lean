-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_from_local_published_inputs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T14:58:57.202928+00:00
-- url     : https://prove2.me/submissions/162274eb-84b6-4664-b1ce-5b4cb363ccef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A034
import Definitions.Def_OAIQ075A037
import Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_free_corner_of_published_local_models
import Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_generated_dihedral_spectralInput
import Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_l2Generated_tracialExpectation

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ProperlyInfiniteEstimate
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

end NativeMatrixNorm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralStepDischarge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_RegularizedPolarFactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contractive approximate polar factors inside the original C-star algebra.
These avoid any bidual extension in the row-bound argument. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem positiveShiftReciprocal_continuous (h : A) (hh : 0 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun t : ℝ => (t + ε)⁻¹) (spectrum ℝ h) := by
  apply ContinuousOn.inv₀ (by fun_prop)
  intro t ht
  exact ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hh ht) hε)

omit [PartialOrder A] [StarOrderedRing A] in
theorem positiveShiftReciprocal_selfAdjoint (h : A) (ε : ℝ) :
    IsSelfAdjoint (positiveShiftReciprocal h ε) := cfc_predicate _ h

omit [PartialOrder A] [StarOrderedRing A] in
theorem positiveShiftReciprocal_commute (h : A) (ε : ℝ) :
    Commute (positiveShiftReciprocal h ε) h := (Commute.refl h).cfc_real _

theorem positiveShiftReciprocal_inverse (h : A) (hh : 0 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    (h + ε • (1 : A)) * positiveShiftReciprocal h ε = 1 := by
  have hc := positiveShiftReciprocal_continuous h hh hε
  have hid : cfc (fun t : ℝ => t + ε) h = h + ε • (1 : A) := by
    rw [cfc_add h (fun t : ℝ => t) (fun _ => ε) continuousOn_id continuousOn_const,
      cfc_id' ℝ h hh.isSelfAdjoint, cfc_const ε h hh.isSelfAdjoint]
    simp only [Algebra.algebraMap_eq_smul_one]
  rw [positiveShiftReciprocal, ← hid, ← cfc_mul _ _ h (by fun_prop) hc]
  calc
    cfc (fun t : ℝ => (t + ε) * (t + ε)⁻¹) h = cfc (fun _ : ℝ => 1) h := by
      apply cfc_congr
      intro t ht
      exact mul_inv_cancel₀ (ne_of_gt
        (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hh ht) hε))
    _ = 1 := cfc_const_one ℝ h hh.isSelfAdjoint

theorem positiveShiftReciprocal_mul_norm_le (h : A) (hh : 0 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    ‖h * positiveShiftReciprocal h ε‖ ≤ 1 := by
  have hc := positiveShiftReciprocal_continuous h hh hε
  change ‖h * cfc (fun t : ℝ => (t + ε)⁻¹) h‖ ≤ 1
  conv_lhs => arg 1; arg 1; rw [← cfc_id' ℝ h hh.isSelfAdjoint]
  rw [← cfc_mul (fun t : ℝ => t) (fun t : ℝ => (t + ε)⁻¹) h continuousOn_id hc]
  apply norm_cfc_le zero_le_one
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg hh ht
  have hp : 0 < t + ε := add_pos_of_nonneg_of_pos ht0 hε
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 (inv_nonneg.mpr hp.le))]
  change t / (t + ε) ≤ 1
  exact (div_le_one hp).mpr (by linarith)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicColumnPolar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contractive regularized polar columns inside the source algebra. These
columns will supply dense cyclic vector tests with a varying unit vector. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder WithCStarModule

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A column is contractive when its positive column square is contractive. -/
theorem norm_column_le_of_starSquare {n : ℕ} (a : Fin n → A)
    (ha : ‖∑ i, star (a i) * a i‖ ≤ 1) :
    ‖CStarMatrix.ofMatrix (fun i (_ : Fin 1) => a i)‖ ≤ 1 := by
  let M := CStarMatrix.ofMatrix (fun i (_ : Fin 1) => a i)
  rw [← norm_cstarMatrix_conjTranspose M]
  change ‖CStarMatrix.toCLM M.conjTranspose‖ ≤ 1
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  have hv : ‖v (0 : Fin 1)‖ ≤ ‖v‖ := WithCStarModule.norm_apply_le_norm _ _
  have hi : inner A (CStarMatrix.toCLM M.conjTranspose v)
      (CStarMatrix.toCLM M.conjTranspose v) =
      v 0 * (∑ i, star (a i) * a i) * star (v 0) := by
    rw [CStarMatrix.toCLM_apply_eq_sum]
    change (∑ i : Fin n, (∑ j : Fin 1, v j * star (a i)) *
      star (∑ j : Fin 1, v j * star (a i))) = _
    simp only [Fin.sum_univ_one, star_mul, star_star, Finset.mul_sum, Finset.sum_mul,
      mul_assoc]
  have hn : ‖CStarMatrix.toCLM M.conjTranspose v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    calc
      _ = ‖v 0 * (∑ i, star (a i) * a i) * star (v 0)‖ := by
        rw [CStarModule.norm_sq_eq A, hi]
      _ ≤ (‖v 0‖ * ‖∑ i, star (a i) * a i‖) * ‖v 0‖ :=
        (norm_mul_le _ _).trans (by
          rw [norm_star]
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (‖v‖ * 1) * ‖v‖ := by gcongr
      _ = ‖v‖ ^ 2 := by ring
  simpa only [one_mul] using
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg v)).mp hn

theorem cyclicColumnRoot_nonneg {n : ℕ} (a : Fin n → A) : 0 ≤ cyclicColumnRoot a :=
  CFC.sqrt_nonneg _

theorem cyclicColumnRoot_sq {n : ℕ} (a : Fin n → A) :
    cyclicColumnRoot a * cyclicColumnRoot a = ∑ i, star (a i) * a i :=
  CFC.sqrt_mul_sqrt_self _ (Finset.sum_nonneg fun _ _ => star_mul_self_nonneg _)

theorem cyclicPolarColumn_contract {n : ℕ} (a : Fin n → A) {ε : ℝ} (hε : 0 < ε) :
    ‖CStarMatrix.ofMatrix (cyclicPolarColumn a ε)‖ ≤ 1 := by
  let h := cyclicColumnRoot a
  let r := positiveShiftReciprocal h ε
  have hstar : star r = r := (positiveShiftReciprocal_selfAdjoint h ε).star_eq
  have hc : r * h = h * r := (positiveShiftReciprocal_commute h ε).eq
  have he : (∑ i, star (a i * r) * (a i * r)) = (h * r) * (h * r) := by
    calc
      _ = r * (∑ i, star (a i) * a i) * r := by
        simp only [star_mul, hstar, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ = r * (h * h) * r := by rw [← cyclicColumnRoot_sq a]
      _ = (r * h) * (h * r) := by noncomm_ring
      _ = (h * r) * (h * r) := by rw [hc]
  apply norm_column_le_of_starSquare
  change ‖∑ i, star (a i * r) * (a i * r)‖ ≤ 1
  rw [he]
  have hn := positiveShiftReciprocal_mul_norm_le h (cyclicColumnRoot_nonneg a) hε
  exact (norm_mul_le _ _).trans <| (mul_le_mul hn hn (norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

/-- Multiplication by the shifted root recovers every original column entry. -/
theorem cyclicPolarColumn_recover {n : ℕ} (a : Fin n → A) {ε : ℝ} (hε : 0 < ε)
    (i : Fin n) : cyclicPolarColumn a ε i 0 * (cyclicColumnRoot a + ε • (1 : A)) = a i := by
  let h := cyclicColumnRoot a
  let r := positiveShiftReciprocal h ε
  have hr : star r = r := (positiveShiftReciprocal_selfAdjoint h ε).star_eq
  have hi := congrArg star (positiveShiftReciprocal_inverse h (cyclicColumnRoot_nonneg a) hε)
  have hrev : r * (h + ε • (1 : A)) = 1 := by
    simp only [star_mul, star_add, star_smul, star_trivial, star_one] at hi
    change star r * (star h + ε • (1 : A)) = 1 at hi
    have hh : star h = h := (cyclicColumnRoot_nonneg a).star_eq
    rwa [hr, hh] at hi
  change (a i * r) * (h + ε • (1 : A)) = a i
  rw [mul_assoc, hrev, mul_one]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicColumnTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.hilbertArrayFlatten_apply _root_.OAI.KadisonSimilarity.hilbertFourfoldFlatten_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.hilbertTripleFlatten_apply _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.matrixLeftArray_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.representedDoubleMatrix_apply _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-- A finite orbit column and its positive square root have the same vector norm. -/
theorem norm_cyclicColumnRoot_action (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    {n : ℕ} (a : Fin n → A) :
    ‖σ (cyclicColumnRoot a) Ω‖ = ‖cyclicOrbitColumn σ Ω a‖ := by
  have hsa : (σ (cyclicColumnRoot a)).adjoint = σ (cyclicColumnRoot a) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star,
      (cyclicColumnRoot_nonneg a).star_eq]
  have hsq : (σ (cyclicColumnRoot a)).adjoint.comp (σ (cyclicColumnRoot a)) =
      ∑ i, (σ (a i)).adjoint.comp (σ (a i)) := by
    rw [hsa]
    change σ (cyclicColumnRoot a) * σ (cyclicColumnRoot a) = _
    rw [← map_mul, cyclicColumnRoot_sq, map_sum]
    simp only [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
  have hi := congrArg (fun T : K →L[ℂ] K => (inner ℂ Ω (T Ω)).re) hsq
  simp only [ContinuousLinearMap.comp_apply, sum_apply, inner_sum,
    ContinuousLinearMap.adjoint_inner_right] at hi
  have hre (f : Fin n → ℂ) : (∑ i, f i).re = ∑ i, (f i).re :=
    map_sum Complex.reLm f Finset.univ
  have hself (x : K) : (inner ℂ x x).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  rw [hre, hself] at hi
  simp_rw [hself] at hi
  have hv := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => K) (cyclicOrbitColumn σ Ω a)
  simp only [cyclicOrbitColumn_apply] at hv
  nlinarith [norm_nonneg (σ (cyclicColumnRoot a) Ω), norm_nonneg (cyclicOrbitColumn σ Ω a)]

theorem cyclicShiftVector_norm_le (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    {n : ℕ} (a : Fin n → A) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖cyclicShiftVector σ Ω a ε‖ ≤ ‖cyclicOrbitColumn σ Ω a‖ + ε * ‖Ω‖ := by
  have he : cyclicShiftVector σ Ω a ε = σ (cyclicColumnRoot a) Ω + ε • Ω := by
    change σ (cyclicColumnRoot a + ε • (1 : A)) Ω = _
    have hs : σ (ε • (1 : A)) = ε • σ 1 :=
      σ.toLinearMap.map_smul_of_tower ε (1 : A)
    rw [map_add, hs, map_one]
    rfl
  rw [he, ← norm_cyclicColumnRoot_action σ Ω a]
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul, Real.norm_of_nonneg hε])

theorem cyclicPolarColumn_action_recover (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    {n : ℕ} (a : Fin n → A) {ε : ℝ} (hε : 0 < ε) :
    columnAction σ (cyclicPolarColumn a ε) (cyclicShiftVector σ Ω a ε) =
      cyclicOrbitColumn σ Ω a := by
  apply PiLp.ext
  intro i
  rw [columnAction_apply, cyclicShiftVector, cyclicOrbitColumn_apply]
  change ((σ (cyclicPolarColumn a ε i 0) * σ (cyclicColumnRoot a + ε • (1 : A))) Ω) = _
  rw [← map_mul, cyclicPolarColumn_recover a hε i]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Cyclicity supplies simultaneous approximation in every finite Hilbert sum. -/
theorem cyclicOrbitColumn_dense (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    (hΩ : DenseRange (fun a : A => σ a Ω)) (n : ℕ) :
    DenseRange (cyclicOrbitColumn (n := n) σ Ω) := by
  let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => K)).symm
  have hpi : DenseRange (Pi.map (fun _ : Fin n => fun a : A => σ a Ω)) :=
    DenseRange.piMap (fun _ => hΩ)
  exact e.surjective.denseRange.comp hpi e.continuous

/-- A dense cyclic orbit gives all the required bounded column tests. -/
theorem cyclicColumnTests_of_dense_orbit (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    (hΩ : DenseRange (fun a : A => σ a Ω)) : CyclicColumnTests σ := by
  intro n ξ hξ η hη
  let δ := min η (1 / 4 : ℝ)
  have hδ : 0 < δ := lt_min hη (by norm_num)
  obtain ⟨a, ha⟩ := (cyclicOrbitColumn_dense σ Ω hΩ n).exists_dist_lt ξ hδ
  rw [dist_eq_norm, norm_sub_rev] at ha
  let c := cyclicOrbitColumn σ Ω a
  have hc : ‖c - ξ‖ < δ := ha
  have hcn : ‖c‖ < 1 + δ := by
    have h := norm_le_norm_sub_add c ξ
    rw [hξ] at h
    linarith
  have hc0 : c ≠ 0 := by
    intro he
    rw [he, zero_sub, norm_neg, hξ] at hc
    have hd := min_le_right η (1 / 4 : ℝ)
    change δ ≤ 1 / 4 at hd
    linarith
  let ε := (1 / 4 : ℝ) / (‖Ω‖ + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have he : ε * (‖Ω‖ + 1) = 1 / 4 := by
    dsimp [ε]
    exact div_mul_cancel₀ _ (by positivity)
  have hεΩ : ε * ‖Ω‖ ≤ 1 / 4 := by nlinarith [norm_nonneg Ω]
  let z := cyclicShiftVector σ Ω a ε
  let P : Matrix (Fin n) (Fin 1) A := cyclicPolarColumn a ε
  have hrec : columnAction σ P z = c := cyclicPolarColumn_action_recover σ Ω a hε
  have hzn : ‖z‖ ≤ 2 := by
    have h := cyclicShiftVector_norm_le σ Ω a hε.le
    have hd := min_le_right η (1 / 4 : ℝ)
    change δ ≤ 1 / 4 at hd
    change ‖z‖ ≤ ‖c‖ + ε * ‖Ω‖ at h
    linarith
  have hz0 : z ≠ 0 := by
    intro hz
    apply hc0
    rw [← hrec, hz]
    apply PiLp.ext
    intro i
    simp only [columnAction_apply, map_zero, PiLp.zero_apply]
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  let ζ := (‖z‖ : ℂ)⁻¹ • z
  let W : Matrix (Fin n) (Fin 1) A := (‖z‖ : ℂ) • P
  refine ⟨ζ, W, ?_, ?_, ?_⟩
  · change ‖(‖z‖ : ℂ)⁻¹ • z‖ = 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ hnz]
  · change ‖(‖z‖ : ℂ) • CStarMatrix.ofMatrix P‖ ≤ 2
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact (mul_le_of_le_one_right (norm_nonneg z) (cyclicPolarColumn_contract a hε)).trans hzn
  · have hv : columnAction σ W ζ = c := by
      apply PiLp.ext
      intro i
      rw [columnAction_apply]
      change σ ((‖z‖ : ℂ) • P i 0) ((‖z‖ : ℂ)⁻¹ • z) = c i
      have hscalar : σ ((‖z‖ : ℂ) • P i 0) = (‖z‖ : ℂ) • σ (P i 0) :=
        map_smul σ _ _
      rw [hscalar, smul_apply, map_smul, smul_smul,
        mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hnz), one_smul]
      simpa only [columnAction_apply] using
        congrArg (fun x : HilbertCopies K n => x i) hrec
    rw [hv]
    exact hc.trans_le (min_le_left _ _)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_FinalDerivations
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The passage from the uniform commutator bound to similarity through
cyclic summands and their finite-column implementers. -/

noncomputable section
namespace KadisonSimilarity

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The direct regularized-column construction supplies every cyclic case. -/
theorem publishedDerivationInputs : PublishedDerivationInputs.{u,v} A := by
  constructor
  intro K _ _ _ σ hσ
  obtain ⟨Ω, hΩ⟩ := hσ
  exact cyclicColumnTests_of_dense_orbit σ Ω hΩ

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialWordIsometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of the completed free-product word inclusions from the
proved Gram identities and totality of elementary tensors. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

/-- Ricard--Xu's regrouped word coordinates follow from tracial freeness. -/
theorem ricardXuWordDecompositionInput : RicardXuWordDecompositionInput G A D := by
  intro hτ _ hf hgen
  refine ⟨tracialOrthogonalWordLevels G A D hτ hf hgen, ?_⟩
  intro n d b a c ha hc
  exact tracialWordInclusion_family G A D hτ hf n
    (((fun i => ⟨a i, ha i⟩), b), (d, (fun i => ⟨c i, hc i⟩)))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeCreationDischarge
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two elementary creation maps in the published interface, constructed
on the actual tracial Hilbert space. -/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

theorem ricardXuCreationInput : RicardXuCreationInput G A D := by
  intro hτ _ hf hgen
  exact ⟨reducedWordCreationModel G A D hτ hf hgen⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeCompressionDischarge
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first-letter compression model on the concrete reduced product. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

theorem ricardXuCompressionInput : RicardXuCompressionInput G A D := by
  intro hτ _ hf hgen
  exact ⟨reducedWordCompressionModel G A D hτ hf hgen⟩

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

/-- Algebra-vector density of the seed is built into the construction,
including when the seed is merely the algebraic factor algebra. -/
theorem l2GeneratedAlgebra_vector_mem (S : StarSubalgebra ℂ P)
    (x : G.l2GeneratedAlgebra S) :
    G.vector (x : P) ∈ closure (Set.range (G.baseAlgebraVectors S)) := by
  have : IsClosed (S.topologicalClosure : Set P) := S.isClosed_topologicalClosure
  have hx : G.vector (x : P) ∈ G.baseSpace S.topologicalClosure := x.property
  rw [G.baseSpace_topologicalClosure S] at hx
  exact hx

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_GeneratedDihedralAlgebras
attribute [-instance] _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.oppositeGeometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.positiveTrace_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightRepresentation_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.tracialWordInclusion_family
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two auxiliary algebras in the spectral test are the actual bounded
L² closures of their algebraic generators. Their inclusions and the density
premises in the free-corner theorem follow from this construction. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

/-- Bounded L² generation is monotone in its algebraic generators. -/
theorem l2GeneratedAlgebra_mono {S T : StarSubalgebra ℂ P} (hST : S ≤ T) :
    G.l2GeneratedAlgebra S ≤ G.l2GeneratedAlgebra T := by
  intro x hx
  have hx' : G.vector x ∈ G.baseSpace S := by
    have : G.vector x ∈ G.baseSpace S.topologicalClosure := hx
    simpa only [G.baseSpace_topologicalClosure S] using this
  have hxT := G.baseSpace_mono hST hx'
  change G.vector x ∈ G.baseSpace T.topologicalClosure
  simpa only [G.baseSpace_topologicalClosure T] using hxT

/-- The constructed algebra has precisely the algebra-vector density used
in the Fourier test, in the linear-span formulation of that theorem. -/
theorem l2GeneratedAlgebra_vector_mem_span (S : StarSubalgebra ℂ P)
    (x : G.l2GeneratedAlgebra S) :
    G.vector (x : P) ∈ (Submodule.span ℂ
      (G.vector '' (S : Set P))).topologicalClosure := by
  have hx := G.l2GeneratedAlgebra_vector_mem S x
  apply closure_mono (s := Set.range (G.baseAlgebraVectors S)) ?_ hx
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, a.property, rfl⟩

theorem second_mem_generatedDihedralAlgebra (d s : P) :
    s ∈ G.generatedDihedralAlgebra d s :=
  G.le_l2GeneratedAlgebra _ (StarAlgebra.subset_adjoin ℂ _ (by simp))

theorem le_generatedTestAlgebra (D : StarSubalgebra ℂ P) (s : P) :
    D ≤ G.generatedTestAlgebra D s := by
  intro x hx
  exact G.le_l2GeneratedAlgebra _ (StarAlgebra.subset_adjoin ℂ _ (Or.inl hx))

theorem generatedDihedralAlgebra_le_test (D : StarSubalgebra ℂ P)
    (d : D) (s : P) :
    G.generatedDihedralAlgebra (d : P) s ≤ G.generatedTestAlgebra D s := by
  apply G.l2GeneratedAlgebra_mono
  apply StarAlgebra.adjoin_mono
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact Or.inl d.property
  · exact Or.inr hx

theorem generatedDihedralAlgebra_density (d s : P)
    (x : G.generatedDihedralAlgebra d s) :
    G.vector (x : P) ∈ (Submodule.span ℂ (G.vector ''
      (StarAlgebra.adjoin ℂ ({d, s} : Set P) : Set P))).topologicalClosure :=
  G.l2GeneratedAlgebra_vector_mem_span _ x

theorem generatedTestAlgebra_density (D : StarSubalgebra ℂ P) (s : P)
    (x : G.generatedTestAlgebra D s) :
    G.vector (x : P) ∈ (Submodule.span ℂ (G.vector ''
      (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {s}) : Set P))).topologicalClosure :=
  G.l2GeneratedAlgebra_vector_mem_span _ x

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialHalfProjectionData
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered reflection used by the dihedral test is constructed from a
half-trace projection. Completing a smaller projection by an orthogonal
projection of the complementary trace supplies that projection; no centered
symmetry is assumed in this algebraic step. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

namespace HalfTraceProjectionData

variable {τ : P →ₗ[ℂ] ℂ} {e : P} (Q : HalfTraceProjectionData τ e)

/-- Its half projection is the chosen completion, so all corner supports
are the original concrete multiplication identities. -/
theorem reflection_half :
    dihedralHalfProjection (symmetryUnit Q.reflection Q.reflection_square) = Q.projection :=
  dihedralHalfProjection_projectionReflection Q.isProjection

end HalfTraceProjectionData
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeCornerApplication
attribute [-instance] _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the proved free-corner theorem using the chosen matrix frame,
its containing half projection, and the actual L²-generated test algebras.
All ordinary generation and support identities are derived here. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

universe u v

variable {P : Type u} [CStarAlgebra P]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  {b : ℝ} (Q : SmallFreeCornerData (G.baseGeometry D).trace b)
  (s : A) (hsstar : star s = s) (hssq : s * s = 1)

local notation "d" => Q.half.reflection
local notation "dU" => symmetryUnit (d : P)
  (congrArg (fun x : D => (x : P)) Q.half.reflection_square)
local notation "p" => dihedralHalfProjection dU
local notation "hp" => symmetryHalfProjectionProof d Q.half.reflection_star
  Q.half.reflection_square
local notation "C" => G.generatedDihedralAlgebra (d : P) (s : P)
local notation "K" => StarSubalgebra.topologicalClosure (factorAlgebra
  (CStarCorner.subalgebra p hp D
    (symmetryHalfProjection_mem D d Q.half.reflection_square Q.half.reflection.property))
  (CStarCorner.subalgebra p hp C
    (symmetryHalfProjection_mem C d Q.half.reflection_square
      (G.first_mem_generatedDihedralAlgebra (d : P) (s : P)))))

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.smallFrameCorner_isClosed
omit [IsClosed (A : Set P)] in
/-- The constructed reduced-word model supplies the half-corner input. -/
theorem smallFrameCompressionInput_proved (hτ : G.trace 1 = 1) :
    G.smallFrameCompressionInput A D Q s hτ := by
  unfold smallFrameCompressionInput
  exact ricardXuCompressionInput _ _ _

include hsstar in
/-- The free-corner estimate with the matrix frame and both generated
algebras fixed by construction. The remaining premises are the local
published word, spectral, comparison, and cyclic-implementation inputs. -/
theorem free_corner_from_smallFrame
    (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
    (hext : ∀ j, G.MatrixConjugationExtensionInput D (M.embedding j) A)
    (S : RealTracialSequence (G.baseGeometry D).trace)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
    (words : RicardXuWordDecompositionInput G A D)
    (creation : RicardXuCreationInput G A D)
    (support : TracialRightSupportInput (fun a => (G.trace a).re)
      (Q.frame.corner : P) A)
    (comparison : FiniteFactorProjectionComparison (fun a => (G.trace a).re))
    (published : PublishedDerivationInputs.{u,v} (CStarCorner (Q.frame.corner : P)
      ⟨congrArg (fun x : D => (x : P)) Q.frame.corner_projection.isIdempotentElem.eq,
        congrArg (fun x : D => (x : P)) Q.frame.corner_projection.isSelfAdjoint.star_eq⟩))
    (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
    (compression : G.smallFrameCompressionInput A D Q s hτ)
    (E : TracialExpectation G.trace A) (EC : TracialExpectation G.trace C)
    (spectral : DihedralSpectralArcInput G.trace C
      (dU * symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq)) dU)
    (hs0 : G.trace (s : P) = 0)
    (T : H →L[ℂ] H)
    (hTD : ∀ x : D, T.comp (G.left (x : P)) = (G.left (x : P)).comp T)
    {ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D T Q.trace ε) :
    ‖G.baseOperator A (commutator T (G.left (s : P)))‖ ≤
      6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε := by
  have hd0 : G.trace (d : P) = 0 := Q.half.reflection_trace hτ
  have hframe (i j : Fin Q.size) :
      star (Q.frame.column i : P) * (Q.frame.column j : P) =
        if i = j then (Q.frame.corner : P) else 0 := by
    change ((star (Q.frame.column i) * Q.frame.column j : D) : P) = _
    rw [Q.frame.initial]
    split_ifs <;> rfl
  have hsum : ∑ i, (Q.frame.column i : P) * star (Q.frame.column i : P) = 1 := by
    have h := congrArg D.subtype Q.frame.resolution
    simp only [map_sum, map_mul, map_star, map_one] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have hhalf : p = (Q.half.projection : P) := by
    have h := congrArg D.subtype Q.half.reflection_half
    change (1 / 2 : ℂ) • (1 + (d : P)) = (Q.half.projection : P) at h
    exact h
  have hpe : p * (Q.frame.corner : P) = (Q.frame.corner : P) := by
    rw [hhalf]
    exact congrArg D.subtype Q.half.left_support
  have hep : (Q.frame.corner : P) * p = (Q.frame.corner : P) := by
    rw [hhalf]
    exact congrArg D.subtype Q.half.right_support
  let R := G.generatedTestAlgebra D (s : P)
  exact G.free_corner_of_published_local_models A D M hgen hfaithful hext S hsize
    hτ hf words creation Q.haar Q.trace_pos Q.corner_trace Q.moments
    (fun a => (G.trace a).re) support comparison d s Q.frame.corner
    Q.half.reflection_star Q.half.reflection_square hd0 hsstar hssq hs0
    Q.frame.corner_projection Q.trace_pos Q.corner_trace (le_refl _) Q.size_pos
    Q.frame.column hframe hsum published commutation C R
    (G.first_mem_generatedDihedralAlgebra (d : P) (s : P))
    (G.second_mem_generatedDihedralAlgebra (d : P) (s : P))
    K rfl compression E EC
    (G.generatedDihedralAlgebra_le_test D d (s : P))
    (G.le_generatedTestAlgebra D (s : P))
    (fun x hx => G.generatedTestAlgebra_density D (s : P) ⟨x, hx⟩)
    (fun x hx => G.generatedDihedralAlgebra_density (d : P) (s : P) ⟨x, hx⟩)
    hpe hep spectral T hTD hε hcorner

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_PolarPartialIsometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete right supports in a finite tracial von Neumann algebra

The partial isometry is constructed by extending the isometry
`sqrt(x* x) ξ ↦ x ξ` from its dense range and setting it to zero on the
orthogonal complement. Bicommutant closure keeps that operator in the algebra.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem polarPartialIsometry_mul_modulus (x : H →L[ℂ] H) :
    polarPartialIsometry x * polarModulus x = x := by
  ext ξ
  have he : (operatorRangeClosure (polarModulus x)).orthogonalProjectionOnto
      (polarModulus x ξ) = rangeIntoClosure (polarModulus x) ξ := by
    apply Subtype.ext
    exact Submodule.starProjection_eq_self_iff.mpr
      (Submodule.le_topologicalClosure _ ⟨ξ, rfl⟩)
  change polarRangeIsometry x
    ((operatorRangeClosure (polarModulus x)).orthogonalProjectionOnto (polarModulus x ξ)) = x ξ
  rw [he, polarRangeIsometry_apply]

theorem polarPartialIsometry_initial (x : H →L[ℂ] H) :
    star (polarPartialIsometry x) * polarPartialIsometry x = rangeSupport (polarModulus x) := by
  let M := operatorRangeClosure (polarModulus x)
  let J := (polarRangeIsometry x).toContinuousLinearMap
  let Q := M.orthogonalProjectionOnto
  change (J.comp Q).adjoint.comp (J.comp Q) = M.starProjection
  rw [ContinuousLinearMap.adjoint_comp]
  calc
    (Q.adjoint.comp J.adjoint).comp (J.comp Q) =
        Q.adjoint.comp ((J.adjoint.comp J).comp Q) := by simp only [ContinuousLinearMap.comp_assoc]
    _ = M.subtypeL.comp Q := by
      rw [(polarRangeIsometry x).adjoint_comp_self, ContinuousLinearMap.one_def,
        ContinuousLinearMap.id_comp, Submodule.adjoint_orthogonalProjectionOnto]
    _ = M.starProjection := rfl

theorem polarPartialIsometry_mul_initial (x : H →L[ℂ] H) :
    polarPartialIsometry x * rangeSupport (polarModulus x) = polarPartialIsometry x := by
  ext ξ
  change polarRangeIsometry x
      ((operatorRangeClosure (polarModulus x)).orthogonalProjectionOnto
        ((operatorRangeClosure (polarModulus x)).starProjection ξ)) =
    polarRangeIsometry x ((operatorRangeClosure (polarModulus x)).orthogonalProjectionOnto ξ)
  congr 1
  apply Subtype.ext
  exact congrArg (fun T : H →L[ℂ] H => T ξ)
    (rangeSupport_isStarProjection (polarModulus x)).isIdempotentElem.eq

theorem polarPartialIsometry_final (x : H →L[ℂ] H) :
    IsStarProjection (polarPartialIsometry x * star (polarPartialIsometry x)) := by
  constructor
  · change (polarPartialIsometry x * star (polarPartialIsometry x)) *
      (polarPartialIsometry x * star (polarPartialIsometry x)) = _
    calc
      _ = (polarPartialIsometry x *
          (star (polarPartialIsometry x) * polarPartialIsometry x)) *
          star (polarPartialIsometry x) := by simp only [mul_assoc]
      _ = polarPartialIsometry x * star (polarPartialIsometry x) := by
        rw [polarPartialIsometry_initial, polarPartialIsometry_mul_initial]
  · exact IsSelfAdjoint.mul_star_self _

/-- A left support of x is also a left support of its polar partial isometry. -/
theorem leftSupport_polarPartialIsometry (x q : H →L[ℂ] H) (hqx : q * x = x) :
    q * polarPartialIsometry x = polarPartialIsometry x := by
  have he : ∀ ξ : operatorRangeClosure (polarModulus x),
      q (polarRangeIsometry x ξ) = polarRangeIsometry x ξ := by
    intro ξ
    refine (rangeIntoClosure_dense (polarModulus x)).induction ?_ ?_ ξ
    · rintro _ ⟨η, rfl⟩
      rw [polarRangeIsometry_apply]
      exact congrArg (fun T : H →L[ℂ] H => T η) hqx
    · exact isClosed_eq (q.continuous.comp (polarRangeIsometry x).continuous)
        (polarRangeIsometry x).continuous
  ext ξ
  exact he _

/-- Commutation on the two dense range maps extends to the polar isometry. -/
theorem polarPartialIsometry_commutes (x T : H →L[ℂ] H)
    (hx : Commute x T) (hS : Commute (polarModulus x) T)
    (hSstar : Commute (polarModulus x) (star T)) :
    Commute (polarPartialIsometry x) T := by
  let M := operatorRangeClosure (polarModulus x)
  let J := polarRangeIsometry x
  let Q := M.orthogonalProjectionOnto
  let R : M →L[ℂ] M := T.restrict (fun ξ hξ => operatorRangeClosure_invariant _ T hS hξ)
  have hJ : ∀ ξ : M, J (R ξ) = T (J ξ) := by
    intro ξ
    refine (rangeIntoClosure_dense (polarModulus x)).induction ?_ ?_ ξ
    · rintro _ ⟨η, rfl⟩
      have hR : R (rangeIntoClosure (polarModulus x) η) =
          rangeIntoClosure (polarModulus x) (T η) := by
        apply Subtype.ext
        exact (congrArg (fun S : H →L[ℂ] H => S η) hS.eq).symm
      rw [hR, polarRangeIsometry_apply, polarRangeIsometry_apply]
      exact congrArg (fun S : H →L[ℂ] H => S η) hx.eq
    · exact isClosed_eq (J.continuous.comp R.continuous) (T.continuous.comp J.continuous)
  have hQ (ξ : H) : Q (T ξ) = R (Q ξ) := by
    apply Subtype.ext
    exact congrArg (fun S : H →L[ℂ] H => S ξ) (rangeSupport_commutes _ T hS hSstar).eq
  change polarPartialIsometry x * T = T * polarPartialIsometry x
  ext ξ
  change J (Q (T ξ)) = T (J (Q ξ))
  rw [hQ, hJ]

theorem polarModulus_mem (P : VonNeumannAlgebra H) (x : H →L[ℂ] H) (hx : x ∈ P) :
    polarModulus x ∈ P := by
  let : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
    change IsClosed P.carrier
    rw [← P.centralizer_centralizer']
    exact Set.isClosed_centralizer _
  rw [polarModulus, CFC.sqrt_eq_real_sqrt (star x * x) (star_mul_self_nonneg x)]
  have hxstar : star x ∈ P.toStarSubalgebra := star_mem hx
  have hxx : star x * x ∈ P.toStarSubalgebra := P.toStarSubalgebra.mul_mem hxstar hx
  exact cfcₙ_mem (𝕜' := ℂ) (s := P.toStarSubalgebra) Real.sqrt hxx

theorem polarPartialIsometry_mem (P : VonNeumannAlgebra H) (x : H →L[ℂ] H) (hx : x ∈ P) :
    polarPartialIsometry x ∈ P := by
  suffices polarPartialIsometry x ∈ P.commutant.commutant by simpa using this
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  have hS := polarModulus_mem P x hx
  exact (polarPartialIsometry_commutes x T
    (VonNeumannAlgebra.mem_commutant_iff.mp hT x hx)
    (VonNeumannAlgebra.mem_commutant_iff.mp hT _ hS)
    (VonNeumannAlgebra.mem_commutant_iff.mp (star_mem hT) _ hS)).eq.symm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralRoundingDischarge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

theorem isStarProjection_subtype_of_coe {R S : Type*} [Mul R] [Star R]
    [SetLike S R] [MulMemClass S R] [StarMemClass S R] {s : S}
    (x : s) (hp : IsStarProjection (x : R)) : IsStarProjection x := by
  constructor
  · exact Subtype.ext hp.isIdempotentElem.eq
  · exact Subtype.ext hp.isSelfAdjoint.star_eq

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialRightSupportDischarge
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Right support trace bounds from the constructed polar partial isometry -/
noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Trace comparison needs only traciality and positivity once the polar
partial isometry has been constructed. -/
theorem trace_initial_le_leftSupport {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (τ : A →ₚ[ℂ] ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (v q : A) (hq : IsStarProjection q) (hv : IsStarProjection (v * star v))
    (hqv : q * v = v) : (τ (star v * v)).re ≤ (τ q).re := by
  have hqs : q * (v * star v) = v * star v := by rw [← mul_assoc, hqv]
  have hpos := τ.map_nonneg (hv.sub_of_mul_eq_right hq hqs).nonneg
  change 0 ≤ τ (q - v * star v) at hpos
  have ht : τ (v * star v) = τ (star v * v) := htr _ _
  rw [map_sub, ht] at hpos
  exact sub_nonneg.mp (show 0 ≤ (τ q).re - (τ (star v * v)).re from hpos.1)

section Tracial
variable (P : VonNeumannAlgebra H)
attribute [local instance] OAI.KadisonSimilarity.supportClosed
attribute [local instance] OAI.KadisonSimilarity.supportCStar
attribute [local instance] OAI.KadisonSimilarity.supportOrder
local instance supportStarOrder : StarOrderedRing P.toStarSubalgebra := inferInstance

/-- The constructed right support has trace no larger than any containing
left support. No normality of the tracial positive functional is used. -/
theorem exists_rightSupport_trace_le
    (τ : P.toStarSubalgebra →ₚ[ℂ] ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (q x : P.toStarSubalgebra) (hq : IsStarProjection q) (hqx : q * x = x) :
    ∃ r : P.toStarSubalgebra, IsStarProjection r ∧ (τ r).re ≤ (τ q).re ∧ x * r = x := by
  let v : P.toStarSubalgebra :=
    ⟨polarPartialIsometry (x : H →L[ℂ] H), polarPartialIsometry_mem P x x.property⟩
  let r : P.toStarSubalgebra := ⟨rangeSupport (polarModulus (x : H →L[ℂ] H)),
    rangeSupport_mem P _ (polarModulus_mem P x x.property)⟩
  have hr : IsStarProjection r := by
    apply isStarProjection_subtype_of_coe
    change IsStarProjection (rangeSupport (polarModulus (x : H →L[ℂ] H)))
    exact rangeSupport_isStarProjection (H := H) (polarModulus (x : H →L[ℂ] H))
  have hv : IsStarProjection (v * star v) := by
    apply isStarProjection_subtype_of_coe
    change IsStarProjection (polarPartialIsometry (x : H →L[ℂ] H) *
      star (polarPartialIsometry (x : H →L[ℂ] H)))
    exact polarPartialIsometry_final (H := H) (x : H →L[ℂ] H)
  have hvr : star v * v = r := by
    apply Subtype.ext
    change star (polarPartialIsometry (x : H →L[ℂ] H)) * polarPartialIsometry (x : H →L[ℂ] H) =
      rangeSupport (polarModulus (x : H →L[ℂ] H))
    exact polarPartialIsometry_initial (H := H) (x : H →L[ℂ] H)
  have hqv : q * v = v := by
    apply Subtype.ext
    change (q : H →L[ℂ] H) * polarPartialIsometry (x : H →L[ℂ] H) =
      polarPartialIsometry (x : H →L[ℂ] H)
    exact leftSupport_polarPartialIsometry (H := H) (x : H →L[ℂ] H)
      (q : H →L[ℂ] H) (congrArg Subtype.val hqx)
  refine ⟨r, hr, ?_, ?_⟩
  · rw [← hvr]
    exact trace_initial_le_leftSupport τ htr v q hq hv hqv
  · apply Subtype.ext
    let X : H →L[ℂ] H := x
    change X * rangeSupport (polarModulus X) = X
    calc
      _ = (polarPartialIsometry X * polarModulus X) * rangeSupport (polarModulus X) := by
        rw [polarPartialIsometry_mul_modulus]
      _ = polarPartialIsometry X * (polarModulus X * rangeSupport (polarModulus X)) :=
        mul_assoc _ _ _
      _ = X := by rw [mul_rangeSupport _ (polarModulus_selfAdjoint X),
        polarPartialIsometry_mul_modulus]

/-- Discharge of the exact support input used in propagation. -/
theorem tracialRightSupportInput
    (τ : P.toStarSubalgebra →ₚ[ℂ] ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (q : P.toStarSubalgebra) (hq : IsStarProjection q)
    (A : StarSubalgebra ℂ P.toStarSubalgebra) :
    TracialRightSupportInput (fun a => (τ a).re) q A := by
  intro a
  apply exists_rightSupport_trace_le P τ htr q (q * (a : P.toStarSubalgebra)) hq
  rw [← mul_assoc, hq.isIdempotentElem.eq]

end Tracial

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

theorem transportedPositiveTrace_tracial (τ : A →ₚ[ℂ] ℂ) (e : A ≃⋆ₐ[ℂ] B)
    (htr : ∀ a b, τ (a * b) = τ (b * a)) :
    ∀ b c, transportedPositiveTrace τ e (b * c) = transportedPositiveTrace τ e (c * b) := by
  intro b c
  simp only [transportedPositiveTrace_apply, map_mul]
  exact htr _ _

/-- Right supports transfer through the same actual algebraic equivalence. -/
theorem tracialRightSupportInput_of_equiv
    (τA : A → ℝ) (τB : B → ℝ) (e : A ≃⋆ₐ[ℂ] B) (hτ : ∀ a, τB (e a) = τA a)
    (q : A) (S : StarSubalgebra ℂ A)
    (support : TracialRightSupportInput τB (e q) (S.map e.toStarAlgHom)) :
    TracialRightSupportInput τA q S := by
  intro a
  let b : S.map e.toStarAlgHom := ⟨e (a : A), ⟨(a : A), a.property, rfl⟩⟩
  obtain ⟨r, hr, htrace, hright⟩ := support b
  change (e q * e (a : A)) * r = e q * e (a : A) at hright
  refine ⟨e.symm r, hr.map e.symm, ?_, ?_⟩
  · have he : τA (e.symm r) = τB r := by
      simpa only [e.apply_symm_apply] using (hτ (e.symm r)).symm
    rw [he, ← hτ q]
    exact htrace
  · have h := congrArg e.symm hright
    simpa only [map_mul, e.symm_apply_apply] using h

end Equivalence

section Concrete
variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : VonNeumannAlgebra H)

local instance transportModel_closed : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed P.carrier
  rw [← P.centralizer_centralizer']
  exact Set.isClosed_centralizer _

/-- The concrete polar construction discharges right supports in the
abstract algebra through that same faithful normal realization. -/
theorem tracialRightSupportInput_of_concrete_equiv
    (τ : A →ₚ[ℂ] ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (e : A ≃⋆ₐ[ℂ] P.toStarSubalgebra) (q : A) (hq : IsStarProjection q)
    (S : StarSubalgebra ℂ A) : TracialRightSupportInput (fun a => (τ a).re) q S := by
  apply tracialRightSupportInput_of_equiv (fun a => (τ a).re)
    (fun b => (transportedPositiveTrace τ e b).re) e
    (fun a => congrArg Complex.re (transportedPositiveTrace_map τ e a)) q S
  exact tracialRightSupportInput P (transportedPositiveTrace τ e)
    (transportedPositiveTrace_tracial τ e htr) (e q) (hq.map e.toStarAlgHom) (S.map e.toStarAlgHom)

/-- The same actual representation supplies the propagation right
supports for every projection and every subalgebra. -/
theorem tracialRightSupportInput_of_concrete_range
    (τ : A →ₚ[ℂ] ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hinj : Function.Injective ρ)
    (hrange : ρ.range = P.toStarSubalgebra)
    (q : A) (hq : IsStarProjection q) (S : StarSubalgebra ℂ A) :
    TracialRightSupportInput (fun a => (τ a).re) q S :=
  tracialRightSupportInput_of_concrete_equiv P τ htr
    (equivalenceOfConcreteRange P ρ hinj hrange) q hq S

end Concrete
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeMatrixExtension
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The matrix-factor automorphism extends to the actual normal tracial
algebra by conjugating its left representation with the free-word unitary. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry
open scoped CStarAlgebra

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)
  (h1 : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
  (hgen : G.FactorsTraciallyGenerate A D)

local notation "U" => G.freeMatrixExtensionUnitary A D ι u h1 hf hgen

variable (hfaithful : Function.Injective G.vector) (M : VonNeumannAlgebra H)
  (hrange : G.left.range = M.toStarSubalgebra)

theorem freeMatrixExtensionHom_left (x : P) :
    G.left (G.freeMatrixExtensionHom A D ι u h1 hf hgen hfaithful M hrange x) =
      G.freeMatrixExtensionRepresentation A D ι u h1 hf hgen x := by
  let e := equivalenceOfConcreteRange M G.left (G.left_injective hfaithful)
    hrange
  let r := (G.freeMatrixExtensionRepresentation A D ι u h1 hf hgen).codRestrict
    M.toStarSubalgebra (G.freeMatrixExtensionRepresentation_mem A D ι u h1 hf hgen
      hfaithful M hrange)
  exact congrArg (fun t : M.toStarSubalgebra => (t : H →L[ℂ] H)) (e.apply_symm_apply (r x))

theorem freeMatrixExtensionHom_base (a : A) :
    G.freeMatrixExtensionHom A D ι u h1 hf hgen hfaithful M hrange (a : P) = (a : P) := by
  apply G.left_injective hfaithful
  rw [G.freeMatrixExtensionHom_left, G.freeMatrixExtensionRepresentation_apply,
    G.freeMatrixExtensionUnitary_base]

theorem freeMatrixExtensionHom_other (d : D) :
    G.freeMatrixExtensionHom A D ι u h1 hf hgen hfaithful M hrange (d : P) =
      (matrixConjugateLetter D ι u d : P) := by
  apply G.left_injective hfaithful
  rw [G.freeMatrixExtensionHom_left, G.freeMatrixExtensionRepresentation_apply,
    G.freeMatrixExtensionUnitary_other]

private theorem vectorTrace_conjugate (V : H ≃ₗᵢ[ℂ] H) (Ω : H) (hΩ : V Ω = Ω)
    (T : H →L[ℂ] H) : vectorTrace Ω (V.conjStarAlgEquiv T) = vectorTrace Ω T := by
  have hs : V.symm Ω = Ω := by
    apply V.injective
    rw [V.apply_symm_apply, hΩ]
  rw [vectorTrace_apply, vectorTrace_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, hs]
  calc
    inner ℂ Ω (V (T Ω)) = inner ℂ (V Ω) (V (T Ω)) := by rw [hΩ]
    _ = inner ℂ Ω (T Ω) := V.inner_map_map Ω (T Ω)

theorem freeMatrixExtensionHom_trace (x : P) :
    G.trace (G.freeMatrixExtensionHom A D ι u h1 hf hgen hfaithful M hrange x) =
      G.trace x := by
  rw [← G.trace_eq_vectorTrace, G.freeMatrixExtensionHom_left,
    G.freeMatrixExtensionRepresentation_apply, ← G.trace_eq_vectorTrace x]
  exact vectorTrace_conjugate (U) (G.vector 1)
    (G.freeMatrixExtensionUnitary_one A D ι u h1 hf hgen) (G.left x)

include h1 hf hgen hfaithful M hrange in
/-- Blanchard--Dykema's two-factor extension specialization, constructed
for the given faithful normal tracial free product. -/
theorem matrixConjugationExtensionInput_of_normal_range :
    G.MatrixConjugationExtensionInput D ι A := by
  intro v
  exact ⟨G.freeMatrixExtensionHom A D ι v h1 hf hgen hfaithful M hrange,
    G.freeMatrixExtensionHom_trace A D ι v h1 hf hgen hfaithful M hrange,
    G.freeMatrixExtensionHom_base A D ι v h1 hf hgen hfaithful M hrange,
    G.freeMatrixExtensionHom_other A D ι v h1 hf hgen hfaithful M hrange⟩

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_OppositeTracialGeometry
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Right multiplication is the left representation of the opposite algebra.
This transfers the proved bounded-ball normality criterion to its actual range. -/

noncomputable section
namespace KadisonSimilarity.TracialCornerGeometry
open scoped CStarAlgebra

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

/-- The right range is a von Neumann algebra when the original left range is normal. -/
theorem rightRepresentation_normal_range (h1 : G.trace 1 = 1)
    (hf : Function.Injective G.vector) (M : VonNeumannAlgebra H)
    (hrange : G.left.range = M.toStarSubalgebra) :
    G.rightRepresentation.range =
      (representationVonNeumannAlgebra G.rightRepresentation).toStarSubalgebra := by
  apply G.oppositeGeometry.normal_range_of_closed_trace_balls
  intro C
  have h := G.trace_balls_closed_of_normal_range h1 hf M hrange C
  have heq : G.oppositeGeometry.vector '' Metric.closedBall (0 : Pᵐᵒᵖ) C =
      G.vector '' Metric.closedBall (0 : P) C := by
    ext ξ
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨MulOpposite.unop a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨MulOpposite.op a, ha, rfl⟩
  rwa [heq]

end KadisonSimilarity.TracialCornerGeometry

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCommutationDischarge
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite tracial commutation theorem for the given faithful normal
representation, using the constructed trace-preserving expectation. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)
  (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
  (M : VonNeumannAlgebra H) (hrange : G.left.range = M.toStarSubalgebra)

include h1 M hrange in
theorem tracialCommutationInput_of_normal_range :
    TracialCommutationInput G.left (G.faithfulRightAction hf) := by
  let N := representationVonNeumannAlgebra G.rightRepresentation
  have hright : G.rightRepresentation.range = N.toStarSubalgebra :=
    G.rightRepresentation_normal_range h1 hf M hrange
  have hNM : N ≤ G.leftCommutant := by
    intro T hT
    change T ∈ N.toStarSubalgebra at hT
    rw [← hright] at hT
    obtain ⟨a, rfl⟩ := hT
    exact (G.mem_leftCommutant_iff _).mpr (fun b => G.right_left b (MulOpposite.unop a))
  let τ := G.commutantTracialRepresentation h1
  have hsub : Set.range G.vector ⊆ subalgebraTraceVectors τ N := by
    rintro _ ⟨a, rfl⟩
    have haN : G.right a ∈ N :=
      mem_representationVonNeumannAlgebra G.rightRepresentation (MulOpposite.op a)
    refine ⟨⟨G.right a, hNM haN⟩, haN, ?_⟩
    change G.right a (G.vector 1) = G.vector a
    rw [G.right_vector, one_mul]
  intro Z hZ
  have hZM : Z ∈ G.leftCommutant := (G.mem_leftCommutant_iff Z).mpr hZ
  have hZN : Z ∈ N := mem_of_traceVector_mem_closure τ hNM ⟨Z, hZM⟩
    (closure_mono hsub (G.dense_vector (Generator.Tracial.baseVector τ ⟨Z, hZM⟩)))
  change Z ∈ N.toStarSubalgebra at hZN
  rw [← hright] at hZN
  obtain ⟨a, ha⟩ := hZN
  exact ⟨MulOpposite.unop a, ha⟩

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialGeometrySupport
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal tracial geometry supplies the propagation support input.
Positivity of its trace follows directly from the Hilbert inner product. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

theorem rightSupportInput_of_normal_range
    (hf : Function.Injective G.vector) (M : VonNeumannAlgebra H)
    (hrange : G.left.range = M.toStarSubalgebra)
    (q : A) (hq : IsStarProjection q) (S : StarSubalgebra ℂ A) :
    TracialRightSupportInput (fun a => (G.trace a).re) q S := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  exact tracialRightSupportInput_of_concrete_range M G.positiveTrace G.tracial
    G.left (G.left_injective hf) hrange q hq S

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_LocalFreeCornerInputs
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact remaining published premises for one local free-product
application. Every field concerns the underlying tracial algebras or their
standard Hilbert models; none is an estimate for the operator being tested.
The generated algebras, frame, reflection and ordinary word density
provide the geometric data. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

universe u v

variable {P : Type u} [CStarAlgebra P]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  {b : ℝ} (Q : SmallFreeCornerData (G.baseGeometry D).trace b)
  (s : A) (hssq : s * s = 1)
  (hτ : G.trace 1 = 1) (hfaithful : Function.Injective G.vector)

include M hτ hssq hfaithful in
/-- The local conclusion is derived from the published premises and the
actual small frame, for every commuting operator with its concrete corner
bound. No operator-estimate field occurs in the published bundle. -/
theorem free_corner_from_local_published_inputs_oai
    (published : G.LocalFreeCornerPublishedInputs)
    (baseExpectation : Nonempty (TracialExpectation G.trace A))
    (hnormal : ∃ N : VonNeumannAlgebra H, G.left.range = N.toStarSubalgebra)
    (hgen : G.FactorsTraciallyGenerate A D)
    (S : RealTracialSequence (G.baseGeometry D).trace)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    (hf : ScalarFree G.trace D A)
    (hsstar : star s = s) (hs0 : G.trace (s : P) = 0)
    (T : H →L[ℂ] H)
    (hTD : ∀ x : D, T.comp (G.left (x : P)) = (G.left (x : P)).comp T)
    {ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D T Q.trace ε) :
    ‖G.baseOperator A (commutator T (G.left (s : P)))‖ ≤
      6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε := by
  obtain ⟨E⟩ := baseExpectation
  obtain ⟨N, hN⟩ := hnormal
  obtain ⟨EC⟩ := G.l2Generated_tracialExpectation hτ hfaithful N hN
    (StarAlgebra.adjoin ℂ ({(Q.half.reflection : P), (s : P)} : Set P))
  have spectral := G.generated_dihedral_spectralInput hτ hfaithful N hN D A hf
    (symmetryUnit (Q.half.reflection : P)
      (congrArg (fun x : D => (x : P)) Q.half.reflection_square))
    (symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq))
    Q.half.reflection.property s.property (Q.half.reflection_trace hτ) hs0
    (symmetryUnit_inv _ _) (symmetryUnit_inv _ _)
    (symmetryUnit_star _ _ (congrArg (fun x : D => (x : P)) Q.half.reflection_star))
    (symmetryUnit_star _ _ (congrArg (fun x : A => (x : P)) hsstar))
  have support := G.rightSupportInput_of_normal_range hfaithful N hN
    (Q.frame.corner : P) (Q.frame.corner_projection.map D.subtype) A
  have matrixExtension := fun j => G.matrixConjugationExtensionInput_of_normal_range
    A D (M.embedding j) hτ hf hgen hfaithful N hN
  have commutation := G.tracialCommutationInput_of_normal_range hτ hfaithful N hN
  have hcompression := G.smallFrameCompressionInput_proved A D Q s hτ
  exact G.free_corner_from_smallFrame A D M Q s hsstar hssq hgen hfaithful
    matrixExtension S hsize hτ hf (ricardXuWordDecompositionInput G A D)
    (ricardXuCreationInput G A D) support published.comparison publishedDerivationInputs
    commutation hcompression E EC spectral hs0 T hTD hε hcorner

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_from_local_published_inputs_oai.{u, v, u_1} := @OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_from_local_published_inputs_oai.{u, v, u_1}
