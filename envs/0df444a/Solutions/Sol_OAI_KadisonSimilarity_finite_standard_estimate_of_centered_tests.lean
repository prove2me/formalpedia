-- Prove2me | solution 1 for OAI.KadisonSimilarity.finite_standard_estimate_of_centered_tests
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T14:56:00.659899+00:00
-- url     : https://prove2.me/submissions/99eeb2c3-c2be-49f9-9925-0d4beb669ae2

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A025
import Definitions.Def_OAIQ075A028
import Definitions.Def_OAIQ075A030

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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [Group Γ]

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
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialSymmetryDilation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.HochschildMatrixDilation.diag_pow _root_.OAI.KadisonSimilarity.grothendieckMatrixMap_apply _root_.OAI.KadisonSimilarity.grothendieckOffDiagonal_mul_star _root_.OAI.KadisonSimilarity.grothendieckOffDiagonal_star_mul _root_.OAI.KadisonSimilarity.grothendieckState00_apply _root_.OAI.KadisonSimilarity.grothendieckState11_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.representedDoubleMatrix_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered symmetry tests for contractions. The selfadjoint two-by-two
dilation has opposite diagonal entries, so its normalized trace vanishes
for every linear functional. Applying it to the selfadjoint off-diagonal
matrix of an arbitrary contraction yields a four-by-four symmetry with
the original contraction as one entry. This avoids any extra spectral
trace-equality hypothesis. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder Matrix
open HochschildMatrixDilation

variable {A : Type*} [CStarAlgebra A]

variable [PartialOrder A] [StarOrderedRing A]

attribute [local instance] OAI.KadisonSimilarity.instNonUnitalContinuousFunctionalCalculusRealIsSelfAdjoint_solutions
attribute [local instance] OAI.KadisonSimilarity.instNonnegSpectrumClassReal_solutions
/-- Opposite diagonal entries make the dilation centered without any
centering condition on its input. -/
theorem linearMatrixTrace_selfAdjointSymmetryDilation (τ : A →ₗ[ℂ] ℂ) (a : A) :
    linearMatrixTrace τ (selfAdjointSymmetryDilation a) = 0 := by
  simp [linearMatrixTrace, selfAdjointSymmetryDilation, diag, offdiag]

theorem contractionSymmetryUnitary_star (a : A) (ha : ‖a‖ ≤ 1) :
    star (contractionSymmetryUnitary a ha : Mat (Mat A)) = contractionSymmetryUnitary a ha :=
  selfAdjointSymmetryDilation_star _ (offdiag_selfAdjoint a)

theorem contractionSymmetryUnitary_sq (a : A) (ha : ‖a‖ ≤ 1) :
    (contractionSymmetryUnitary a ha : Mat (Mat A)) * contractionSymmetryUnitary a ha = 1 :=
  selfAdjointSymmetryDilation_sq _ (offdiag_selfAdjoint a) (offdiag_norm_le_one a ha)

theorem linearMatrixTrace_contractionSymmetryUnitary (τ : A →ₗ[ℂ] ℂ)
    (a : A) (ha : ‖a‖ ≤ 1) :
    linearMatrixTrace (linearMatrixTrace τ)
      (contractionSymmetryUnitary a ha : Mat (Mat A)) = 0 :=
  linearMatrixTrace_selfAdjointSymmetryDilation _ _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FullColumns
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialSymmetryExtraction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered symmetry dilation is tested on actual finite Hilbert
arrays. Its original entry is recovered by coordinate insertion and
projection, both contractive. Thus no matrix-size factor enters the
commutator estimate. -/

noncomputable section
namespace KadisonSimilarity

open HochschildMatrixDilation

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Coordinate compression is contractive, independently of the array sizes. -/
theorem norm_matrixEntryCompression_le {n m : ℕ} (i : Fin m) (j : Fin n)
    (T : HilbertCopies H n →L[ℂ] HilbertCopies K m) :
    ‖matrixEntryCompression i j T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  calc
    ‖matrixEntryCompression i j T x‖ = ‖T (PiLp.single 2 j x) i‖ := rfl
    _ ≤ ‖T (PiLp.single 2 j x)‖ := PiLp.norm_apply_le (T (PiLp.single 2 j x)) i
    _ ≤ ‖T‖ * ‖(PiLp.single 2 j x : HilbertCopies H n)‖ :=
      T.le_opNorm (PiLp.single 2 j x)
    _ = ‖T‖ * ‖x‖ := by rw [PiLp.norm_single]

theorem matrixEntryCompression_commutator {n : ℕ}
    (Y : H →L[ℂ] H) (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) (i j : Fin n) :
    matrixEntryCompression i j (commutator (amplify Y n) (matrixOperator X)) =
      commutator Y (X i j) := by
  rw [commutator_amplify_matrixOperator]
  exact matrixEntryCompression_matrixOperator (fun p q => commutator Y (X p q)) i j

variable [CompleteSpace H]
variable {A : Type*} [CStarAlgebra A]

/-- Two successive coordinate corners recover each original algebra entry. -/
theorem double_matrix_commutator_corner (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Y : H →L[ℂ] H) (S : Mat (Mat A)) (i j k l : Fin 2) :
    matrixEntryCompression k l (matrixEntryCompression i j
      (commutator (amplify (amplify Y 2) 2) (representedDoubleMatrix σ S))) =
      commutator Y (σ (S i j k l)) := by
  have hout := matrixEntryCompression_commutator (amplify Y 2)
    (fun p q => representedMatrix σ (S p q)) i j
  have hin := matrixEntryCompression_commutator Y (fun p q => σ (S i j p q)) k l
  change matrixEntryCompression k l
    (matrixEntryCompression i j
      (commutator (amplify (amplify Y 2) 2)
        (matrixOperator (fun p q => representedMatrix σ (S p q))))) = _
  rw [hout]
  exact hin

/-- The double compression has norm at most one. -/
theorem norm_double_entry_commutator_le (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Y : H →L[ℂ] H) (S : Mat (Mat A)) (i j k l : Fin 2) :
    ‖commutator Y (σ (S i j k l))‖ ≤
      ‖commutator (amplify (amplify Y 2) 2) (representedDoubleMatrix σ S)‖ := by
  rw [← double_matrix_commutator_corner σ Y S i j k l]
  exact (norm_matrixEntryCompression_le k l _).trans
    (norm_matrixEntryCompression_le i j _)

variable [PartialOrder A] [StarOrderedRing A]

/-- Testing the actual four-by-four centered symmetry controls the original
contraction, with constant one. -/
theorem norm_commutator_le_centered_symmetry (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Y : H →L[ℂ] H) (a : A) (ha : ‖a‖ ≤ 1) :
    ‖commutator Y (σ a)‖ ≤
      ‖commutator (amplify (amplify Y 2) 2)
        (representedDoubleMatrix σ (contractionSymmetryUnitary a ha))‖ := by
  simpa only [contractionSymmetryUnitary_entry] using
    norm_double_entry_commutator_le σ Y (contractionSymmetryUnitary a ha) 0 1 0 1

/-- In particular, a matrix commutator in the original amplification is
recovered from the centered symmetry over that matrix algebra. -/
theorem norm_amplified_commutator_le_centered_symmetry
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Y : H →L[ℂ] H) {n : ℕ} [NeZero n]
    (X : CStarMatrix (Fin n) (Fin n) A) (hX : ‖X‖ ≤ 1) :
    ‖commutator (amplify Y n) (representedMatrix σ X)‖ ≤
      ‖commutator (amplify (amplify (amplify Y n) 2) 2)
        (representedDoubleMatrix (representedMatrixHom σ n)
          (contractionSymmetryUnitary X hX))‖ :=
  norm_commutator_le_centered_symmetry (representedMatrixHom σ n) (amplify Y n) X hX

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SquareArrayPadding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.hilbertArrayFlatten_apply _root_.OAI.KadisonSimilarity.hilbertFourfoldFlatten_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.hilbertTripleFlatten_apply _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_matrixOperator _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.matrixLeftArray_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.representedDoubleMatrix_apply _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.KadisonSimilarity.vonNeumannInnerDerivation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
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

section Coordinates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {r m : ℕ}

theorem norm_copyEmbeddingMap_le (e : Fin r ↪ Fin m) :
    ‖copyEmbeddingMap (H := H) e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [norm_copyEmbeddingMap, one_mul] using (le_refl ‖x‖)

theorem norm_copyRestriction_le (e : Fin r ↪ Fin m) :
    ‖copyRestriction (H := H) e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp only [copyRestriction_apply]
  calc
    ∑ i : Fin r, ‖x (e i)‖ ^ 2 = ∑ j ∈ Finset.univ.map e, ‖x j‖ ^ 2 := by
      rw [Finset.sum_map]
    _ ≤ ∑ j : Fin m, ‖x j‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro j _ _
      exact sq_nonneg _

theorem copyEmbeddingMap_amplify (e : Fin r ↪ Fin m) (T : H →L[ℂ] H) :
    (copyEmbeddingMap e).comp (amplify T r) =
      (amplify T m).comp (copyEmbeddingMap e) := by
  ext x j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    simp
  · simp [copyEmbeddingMap_apply_of_not_mem e _ j hj]

theorem copyRestriction_amplify (e : Fin r ↪ Fin m) (T : H →L[ℂ] H) :
    (copyRestriction e).comp (amplify T m) =
      (amplify T r).comp (copyRestriction e) := by
  ext x i
  simp

end Coordinates

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

section Padding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {r m : ℕ}

@[simp] theorem norm_padArrayOperator (e : Fin r ↪ Fin m)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r) :
    ‖padArrayOperator e Y‖ = ‖Y‖ := by
  unfold padArrayOperator
  exact norm_split_extension
    (E := HilbertCopies H r) (F := HilbertCopies H m)
    (copyEmbeddingMap e) (copyRestriction e)
    (norm_copyEmbeddingMap_le e) (norm_copyRestriction_le e)
    (copyRestriction_copyEmbedding e) Y

/-- Common left multiplication commutes with extending the multiplicity space. -/
theorem commutator_padArrayOperator (e : Fin r ↪ Fin m)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r) (T : H →L[ℂ] H) :
    commutator (padArrayOperator e Y) (amplify T m) =
      padArrayOperator e (commutator Y (amplify T r)) :=
  commutator_split_extension _ _ _ _ _ (copyEmbeddingMap_amplify e T)
    (copyRestriction_amplify e T)

/-- Every scalar commutator norm is unchanged by multiplicity padding. -/
theorem norm_commutator_padArrayOperator (e : Fin r ↪ Fin m)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r) (T : H →L[ℂ] H) :
    ‖commutator (padArrayOperator e Y) (amplify T m)‖ =
      ‖commutator Y (amplify T r)‖ := by
  rw [commutator_padArrayOperator, norm_padArrayOperator]

/-- In particular, each prescribed homogeneous scalar bound transfers with
the same constant, in both directions. -/
theorem scalar_bound_padArrayOperator_iff {A : Type*} [Norm A]
    (σ : A → (H →L[ℂ] H)) (e : Fin r ↪ Fin m)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r) (ε : ℝ) :
    (∀ a, ‖commutator (padArrayOperator e Y) (amplify (σ a) m)‖ ≤ ε * ‖a‖) ↔
      (∀ a, ‖commutator Y (amplify (σ a) r)‖ ≤ ε * ‖a‖) := by
  simp only [norm_commutator_padArrayOperator]

end Padding

section MatrixMultiplicities

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {r m : ℕ}

theorem amplify_padArrayOperator (e : Fin r ↪ Fin m)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r) (n : ℕ) :
    amplify (padArrayOperator e Y) n =
      (mapCopies (copyEmbeddingMap e) n).comp
        ((amplify Y n).comp (mapCopies (copyRestriction e) n)) := by
  ext x i
  simp [padArrayOperator]

/-- Multiplicity padding preserves the norm of every matrix commutator. -/
theorem norm_matrix_commutator_padArrayOperator (e : Fin r ↪ Fin m)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    ‖commutator (amplify (padArrayOperator e Y) n)
      (matrixOperator (fun i j => amplify (X i j) m))‖ =
    ‖commutator (amplify Y n)
      (matrixOperator (fun i j => amplify (X i j) r))‖ := by
  let J := mapCopies (copyEmbeddingMap (H := H) e) n
  let R := mapCopies (copyRestriction (H := H) e) n
  have hJ : ‖J‖ ≤ 1 :=
    (norm_mapCopies_le _ _).trans (norm_copyEmbeddingMap_le e)
  have hR : ‖R‖ ≤ 1 :=
    (norm_mapCopies_le _ _).trans (norm_copyRestriction_le e)
  have hRJ : R.comp J = ContinuousLinearMap.id ℂ (HilbertCopies (HilbertCopies H r) n) := by
    dsimp [R, J]
    rw [← mapCopies_comp_eq, copyRestriction_copyEmbedding, mapCopies_id_eq]
  have hJA : J.comp (matrixOperator (fun i j => amplify (X i j) r)) =
      (matrixOperator (fun i j => amplify (X i j) m)).comp J :=
    mapCopies_intertwines_matrix _ _ _ (fun i j => copyEmbeddingMap_amplify e (X i j))
  have hRB : R.comp (matrixOperator (fun i j => amplify (X i j) m)) =
      (matrixOperator (fun i j => amplify (X i j) r)).comp R :=
    mapCopies_intertwines_matrix _ _ _ (fun i j => copyRestriction_amplify e (X i j))
  rw [amplify_padArrayOperator]
  change ‖commutator (J.comp ((amplify Y n).comp R)) _‖ = _
  rw [commutator_split_extension J R _ _ _ hJA hRB,
    norm_split_extension J R hJ hR hRJ]

end MatrixMultiplicities

section MatrixIndices

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {r m : ℕ}

theorem padOperatorMatrix_apply_of_not_mem_left (e : Fin r ↪ Fin m)
    (X : Matrix (Fin r) (Fin r) (H →L[ℂ] H)) (i j : Fin m)
    (hi : i ∉ Set.range e) : padOperatorMatrix e X i j = 0 := by
  have h (p : Fin r) : i ≠ e p := fun hp => hi ⟨p, hp.symm⟩
  simp [padOperatorMatrix, h]

theorem padOperatorMatrix_apply_of_not_mem_right (e : Fin r ↪ Fin m)
    (X : Matrix (Fin r) (Fin r) (H →L[ℂ] H)) (i j : Fin m)
    (hj : j ∉ Set.range e) : padOperatorMatrix e X i j = 0 := by
  have h (q : Fin r) : j ≠ e q := fun hq => hj ⟨q, hq.symm⟩
  simp [padOperatorMatrix, h]

private theorem sum_eq_sum_embedding {M : Type*} [AddCommMonoid M]
    (e : Fin r ↪ Fin m) (f : Fin m → M)
    (hf : ∀ j, j ∉ Set.range e → f j = 0) :
    ∑ j : Fin m, f j = ∑ i : Fin r, f (e i) := by
  calc
    _ = ∑ j ∈ Finset.univ.map e, f j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      apply hf
      rintro ⟨i, rfl⟩
      exact hj (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    _ = _ := by rw [Finset.sum_map]

/-- Entrywise matrix padding realizes precisely extension by zero. -/
theorem matrixOperator_padOperatorMatrix (e : Fin r ↪ Fin m)
    (X : Matrix (Fin r) (Fin r) (H →L[ℂ] H)) :
    matrixOperator (padOperatorMatrix e X) = padArrayOperator e (matrixOperator X) := by
  ext x j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    simp only [matrixOperator_apply, padArrayOperator, ContinuousLinearMap.comp_apply,
      copyEmbeddingMap_apply_image]
    rw [sum_eq_sum_embedding e _ (by
      intro j hj
      rw [padOperatorMatrix_apply_of_not_mem_right e X (e i) j hj, zero_apply])]
    simp only [padOperatorMatrix_apply_image, copyRestriction_apply]
  · simp only [matrixOperator_apply, padArrayOperator, ContinuousLinearMap.comp_apply]
    rw [copyEmbeddingMap_apply_of_not_mem e _ j hj]
    apply Finset.sum_eq_zero
    intro i _
    rw [padOperatorMatrix_apply_of_not_mem_left e X j i hj, zero_apply]

/-- Enlarging the matrix size introduces no loss in a commutator norm. -/
theorem norm_commutator_padOperatorMatrix (e : Fin r ↪ Fin m)
    (Y : H →L[ℂ] H) (X : Matrix (Fin r) (Fin r) (H →L[ℂ] H)) :
    ‖commutator (amplify Y m) (matrixOperator (padOperatorMatrix e X))‖ =
      ‖commutator (amplify Y r) (matrixOperator X)‖ := by
  calc
    _ = ‖commutator (padArrayOperator e (matrixOperator X)) (amplify Y m)‖ := by
      rw [matrixOperator_padOperatorMatrix]
      exact norm_sub_rev
        ((amplify Y m) * (padArrayOperator e (matrixOperator X)))
        ((padArrayOperator e (matrixOperator X)) * (amplify Y m))
    _ = ‖commutator (matrixOperator X) (amplify Y r)‖ :=
      norm_commutator_padArrayOperator e (matrixOperator X) Y
    _ = _ := norm_sub_rev ((matrixOperator X) * (amplify Y r))
      ((amplify Y r) * (matrixOperator X))

/-- Padding the multiplicity and the testing matrix can be performed
independently, preserving the complete commutator test exactly. -/
theorem norm_commutator_pad_both {s t : ℕ}
    (e : Fin r ↪ Fin m) (f : Fin s ↪ Fin t)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r)
    (X : Matrix (Fin s) (Fin s) (H →L[ℂ] H)) :
    ‖commutator (amplify (padArrayOperator e Y) t)
      (matrixOperator (padOperatorMatrix f (fun i j => amplify (X i j) m)))‖ =
    ‖commutator (amplify Y s)
      (matrixOperator (fun i j => amplify (X i j) r))‖ := by
  exact (norm_commutator_padOperatorMatrix (H := HilbertCopies H m) f
    (padArrayOperator e Y) (fun i j => amplify (X i j) m)).trans
      (norm_matrix_commutator_padArrayOperator e Y X)

end MatrixIndices

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_CStarMatrixPadding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Isometric zero padding of C-star matrices

Padding along an injection is a nonunital star algebra monomorphism. Its
isometry follows from the C-star norm theorem, and its represented action is
the concrete zero extension on finite Hilbert sums.
-/

noncomputable section
namespace KadisonSimilarity

section RepresentedPadding

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {r m : ℕ}

theorem representedPadding_entries (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (e : Fin r ↪ Fin m) (X : CStarMatrix (Fin r) (Fin r) A) :
    (fun i j => σ (cstarMatrixPadding e X i j)) =
      padOperatorMatrix e (fun i j => σ (X i j)) := by
  apply Matrix.ext
  intro i j
  simp only [cstarMatrixPadding_apply, matrixZeroPadding, padOperatorMatrix,
    map_sum, CStarMatrix.ofMatrix_symm_apply]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> simp

end RepresentedPadding

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixArrayFlattening
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.normalizedMatrixTrace_diagonal _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Flattening nested matrix and Hilbert-array coordinates -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

private theorem sum_fin_prod {M : Type*} [AddCommMonoid M] (p q : ℕ)
    (f : Fin (p * q) → M) :
    ∑ k : Fin (p * q), f k = ∑ i : Fin p, ∑ j : Fin q, f (finProdFinEquiv (i, j)) := by
  simpa only [Fintype.sum_prod_type] using
    (Fintype.sum_equiv (finProdFinEquiv : Fin p × Fin q ≃ Fin (p * q))
      (fun ij => f (finProdFinEquiv ij)) f (fun _ => rfl)).symm


section TripleMatrices

variable {A : Type*} [CStarAlgebra A]

private theorem sum_fourfold {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : Fin (4 * n) → M) :
    ∑ a : Fin (4 * n), f a =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin n, f (fourfoldIndexEquiv n (i, (j, k))) := by
  simpa only [Fintype.sum_prod_type] using
    (Fintype.sum_equiv (fourfoldIndexEquiv n)
      (fun ijk => f (fourfoldIndexEquiv n ijk)) f (fun _ => rfl)).symm

end TripleMatrices

section MatrixTrace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Normalized diagonal traces agree under block flattening. -/
theorem normalizedMatrixTrace_blockMatrixFlatten (p q : ℕ) [NeZero p] [NeZero q]
    (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin p) (Fin p) (CStarMatrix (Fin q) (Fin q) A)) :
    normalizedMatrixTrace (normalizedMatrixTrace τ q) p X =
      normalizedMatrixTrace τ (p * q) (blockMatrixFlatten p q X) := by
  simp only [normalizedMatrixTrace_apply, Nat.cast_mul]
  rw [sum_fin_prod]
  simp only [blockMatrixFlatten_apply]
  let a : Fin p → ℂ := fun i => ∑ j : Fin q, τ (X i i j j)
  change (∑ i : Fin p, a i / (q : ℂ)) / (p : ℂ) =
    (∑ i : Fin p, a i) / ((p : ℂ) * (q : ℂ))
  rw [← Finset.sum_div, div_div, mul_comm (q : ℂ) (p : ℂ)]

theorem normalizedMatrixTrace_tripleMatrixFlatten (p q t : ℕ)
    [NeZero p] [NeZero q] [NeZero t] (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin p) (Fin p)
      (CStarMatrix (Fin q) (Fin q) (CStarMatrix (Fin t) (Fin t) A))) :
    normalizedMatrixTrace (normalizedMatrixTrace (normalizedMatrixTrace τ t) q) p X =
      normalizedMatrixTrace τ (p * (q * t)) (tripleMatrixFlatten p q t X) := by
  calc
    _ = normalizedMatrixTrace (normalizedMatrixTrace τ (q * t)) p
        (entrywiseCStarMatrixEquiv p (blockMatrixFlatten q t) X) := by
      simp only [normalizedMatrixTrace_apply, entrywiseCStarMatrixEquiv_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact normalizedMatrixTrace_blockMatrixFlatten q t τ (X i i)
    _ = _ := normalizedMatrixTrace_blockMatrixFlatten p (q * t) τ _

theorem normalizedMatrixTrace_reindex {r m : ℕ} [NeZero r] [NeZero m]
    (τ : A →ₚ[ℂ] ℂ) (e : Fin r ≃ Fin m)
    (X : CStarMatrix (Fin r) (Fin r) A) :
    normalizedMatrixTrace τ m (CStarMatrix.reindexₐ ℂ A e X) =
      normalizedMatrixTrace τ r X := by
  have hcard : r = m := by simpa using Fintype.card_congr e
  simp only [normalizedMatrixTrace_apply]
  congr 1
  · exact (Fintype.sum_equiv e (fun i => τ (X i i))
      (fun j => τ ((CStarMatrix.reindexₐ ℂ A e X) j j)) (by
        intro i
        change τ (X i i) = τ (X (e.symm (e i)) (e.symm (e i)))
        rw [Equiv.symm_apply_apply])).symm
  · exact_mod_cast hcard.symm

/-- The normalized trace is unchanged by the complete fourfold flattening. -/
theorem normalizedMatrixTrace_fourfoldMatrixFlatten (n : ℕ) [NeZero n]
    (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin 2) (Fin 2)
      (CStarMatrix (Fin 2) (Fin 2) (CStarMatrix (Fin n) (Fin n) A))) :
    normalizedMatrixTrace τ (4 * n) (fourfoldMatrixFlatten n X) =
      normalizedMatrixTrace (normalizedMatrixTrace (normalizedMatrixTrace τ n) 2) 2 X := by
  rw [fourfoldMatrixFlatten, StarAlgEquiv.trans_apply, normalizedMatrixTrace_reindex]
  exact (normalizedMatrixTrace_tripleMatrixFlatten 2 2 n τ X).symm

theorem normalizedMatrixTrace_two_eq_linearMatrixTrace (τ : A →ₚ[ℂ] ℂ)
    (X : HochschildMatrixDilation.Mat A) :
    normalizedMatrixTrace τ 2 X = linearMatrixTrace τ.toLinearMap X := by
  simp only [normalizedMatrixTrace_apply, linearMatrixTrace_apply, Fin.sum_univ_two,
    Nat.cast_ofNat]
  rfl

/-- The actual flattened four-by-four contraction symmetry is centered for
the normalized trace on the ordinary matrix algebra. -/
theorem normalizedMatrixTrace_flattened_contractionSymmetry (n : ℕ) [NeZero n]
    (τ : A →ₚ[ℂ] ℂ) (X : CStarMatrix (Fin n) (Fin n) A) (hX : ‖X‖ ≤ 1) :
    normalizedMatrixTrace τ (4 * n)
      (fourfoldMatrixFlatten n (contractionSymmetryUnitary X hX)) = 0 := by
  rw [normalizedMatrixTrace_fourfoldMatrixFlatten, normalizedMatrixTrace_two_eq_linearMatrixTrace]
  have htwo : (normalizedMatrixTrace (normalizedMatrixTrace τ n) 2).toLinearMap =
      linearMatrixTrace (normalizedMatrixTrace τ n).toLinearMap := by
    ext Y
    exact normalizedMatrixTrace_two_eq_linearMatrixTrace _ Y
  rw [htwo]
  exact linearMatrixTrace_contractionSymmetryUnitary _ X hX

end MatrixTrace

section HilbertFlattening

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem hilbertFourfoldFlatten_amplify (n : ℕ) (Y : H →L[ℂ] H)
    (x : HilbertCopies (HilbertCopies (HilbertCopies H n) 2) 2) :
    hilbertFourfoldFlatten n (amplify (amplify (amplify Y n) 2) 2 x) =
      amplify Y (4 * n) (hilbertFourfoldFlatten n x) := by
  ext k
  obtain ⟨⟨i, j, a⟩, rfl⟩ := (fourfoldIndexEquiv n).surjective k
  simp

end HilbertFlattening

section RepresentedFlattening

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [PartialOrder A] [StarOrderedRing A]

private theorem representedDoubleMatrix_nested_apply (n : ℕ)
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (X : HochschildMatrixDilation.Mat
      (HochschildMatrixDilation.Mat (CStarMatrix (Fin n) (Fin n) A)))
    (x : HilbertCopies (HilbertCopies (HilbertCopies H n) 2) 2)
    (i k : Fin 2) (a : Fin n) :
    representedDoubleMatrix (representedMatrixHom σ n) X x i k a =
      ∑ j : Fin 2, ∑ l : Fin 2, ∑ b : Fin n, σ (X i j k l a b) (x j l b) := by
  rw [representedDoubleMatrix_apply (representedMatrixHom σ n) X x i k]
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  exact matrixOperator_apply (fun c d => σ (X i j k l c d)) (x j l) a

/-- The nested action used by the dilation is precisely the ordinary
flattened matrix action under the explicit Hilbert-array isometry. -/
theorem hilbertFourfoldFlatten_representedDoubleMatrix (n : ℕ)
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (X : HochschildMatrixDilation.Mat
      (HochschildMatrixDilation.Mat (CStarMatrix (Fin n) (Fin n) A)))
    (x : HilbertCopies (HilbertCopies (HilbertCopies H n) 2) 2) :
    hilbertFourfoldFlatten n (representedDoubleMatrix (representedMatrixHom σ n) X x) =
      representedMatrix σ (fourfoldMatrixFlatten n X) (hilbertFourfoldFlatten n x) := by
  ext a
  obtain ⟨⟨i, k, b⟩, rfl⟩ := (fourfoldIndexEquiv n).surjective a
  rw [hilbertFourfoldFlatten_apply, representedDoubleMatrix_nested_apply]
  let W : Matrix (Fin (4 * n)) (Fin (4 * n)) (H →L[ℂ] H) :=
    fun c d => σ (fourfoldMatrixFlatten n X c d)
  change _ = matrixOperator W (hilbertFourfoldFlatten n x) (fourfoldIndexEquiv n (i, (k, b)))
  rw [matrixOperator_apply W (hilbertFourfoldFlatten n x) (fourfoldIndexEquiv n (i, (k, b))),
    sum_fourfold n]
  have hW (j l : Fin 2) (c : Fin n) :
      W (fourfoldIndexEquiv n (i, (k, b))) (fourfoldIndexEquiv n (j, (l, c))) =
        σ (X i j k l b c) := by
    dsimp only [W]
    rw [fourfoldMatrixFlatten_apply]
  simp only [hW, hilbertFourfoldFlatten_apply]

theorem hilbertFourfoldFlatten_commutator (n : ℕ)
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Y : H →L[ℂ] H)
    (X : HochschildMatrixDilation.Mat
      (HochschildMatrixDilation.Mat (CStarMatrix (Fin n) (Fin n) A)))
    (x : HilbertCopies (HilbertCopies (HilbertCopies H n) 2) 2) :
    hilbertFourfoldFlatten n
      (commutator (amplify (amplify (amplify Y n) 2) 2)
        (representedDoubleMatrix (representedMatrixHom σ n) X) x) =
      commutator (amplify Y (4 * n)) (representedMatrix σ (fourfoldMatrixFlatten n X))
        (hilbertFourfoldFlatten n x) := by
  simp only [commutator, sub_apply, mul_apply_eq_comp, map_sub,
    hilbertFourfoldFlatten_amplify, hilbertFourfoldFlatten_representedDoubleMatrix]

/-- The commutator norm is exactly preserved by the change of array coordinates. -/
theorem norm_fourfold_commutator (n : ℕ)
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Y : H →L[ℂ] H)
    (X : HochschildMatrixDilation.Mat
      (HochschildMatrixDilation.Mat (CStarMatrix (Fin n) (Fin n) A))) :
    ‖commutator (amplify Y (4 * n)) (representedMatrix σ (fourfoldMatrixFlatten n X))‖ =
      ‖commutator (amplify (amplify (amplify Y n) 2) 2)
        (representedDoubleMatrix (representedMatrixHom σ n) X)‖ := by
  let U := hilbertFourfoldFlatten (H := H) n
  let T := commutator (amplify (amplify (amplify Y n) 2) 2)
    (representedDoubleMatrix (representedMatrixHom σ n) X)
  have he : U.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (T.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap) =
      commutator (amplify Y (4 * n)) (representedMatrix σ (fourfoldMatrixFlatten n X)) := by
    apply ContinuousLinearMap.ext
    intro x
    change U (T (U.symm x)) = _
    rw [hilbertFourfoldFlatten_commutator, LinearIsometryEquiv.apply_symm_apply]
  calc
    _ = ‖U.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (T.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap)‖ :=
      congrArg norm he.symm
    _ = ‖T.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap‖ :=
      norm_isometricCoordinates_comp _ U
    _ = ‖T‖ := norm_comp_isometricCoordinates T U.symm

/-- The original matrix test is a norm-decreasing corner of the ordinary
`4 * n` centered symmetry test. -/
theorem norm_amplified_commutator_le_flattened_symmetry {n : ℕ} [NeZero n]
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Y : H →L[ℂ] H)
    (X : CStarMatrix (Fin n) (Fin n) A) (hX : ‖X‖ ≤ 1) :
    ‖commutator (amplify Y n) (representedMatrix σ X)‖ ≤
      ‖commutator (amplify Y (4 * n))
        (representedMatrix σ (fourfoldMatrixFlatten n (contractionSymmetryUnitary X hX)))‖ := by
  calc
    _ ≤ ‖commutator (amplify (amplify (amplify Y n) 2) 2)
        (representedDoubleMatrix (representedMatrixHom σ n)
          (contractionSymmetryUnitary X hX))‖ :=
      norm_amplified_commutator_le_centered_symmetry σ Y X hX
    _ = _ := (norm_fourfold_commutator n σ Y (contractionSymmetryUnitary X hX)).symm

end RepresentedFlattening

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FiniteAmplificationReduction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.HochschildMatrixDilation.diag_pow _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.grothendieckMatrixMap_apply _root_.OAI.KadisonSimilarity.grothendieckOffDiagonal_mul_star _root_.OAI.KadisonSimilarity.grothendieckOffDiagonal_star_mul _root_.OAI.KadisonSimilarity.grothendieckState00_apply _root_.OAI.KadisonSimilarity.grothendieckState11_apply _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.normalizedMatrixTrace_diagonal _root_.OAI.KadisonSimilarity.vonNeumannInnerDerivation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-- Matrix padding and multiplicity padding preserve the actual represented
commutator, with independent injections on the two indices. -/
theorem norm_represented_commutator_pad_both {r m s t : ℕ}
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (e : Fin r ↪ Fin m) (f : Fin s ↪ Fin t)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r)
    (X : CStarMatrix (Fin s) (Fin s) A) :
    ‖commutator (amplify (padArrayOperator e Y) t)
      (representedMatrix (amplifiedScalarRepresentation σ m) (cstarMatrixPadding f X))‖ =
    ‖commutator (amplify Y s) (representedMatrix (amplifiedScalarRepresentation σ r) X)‖ := by
  change ‖commutator (amplify (padArrayOperator e Y) t)
    (matrixOperator (fun i j => amplifiedScalarRepresentation σ m (cstarMatrixPadding f X i j)))‖ = _
  rw [representedPadding_entries]
  exact norm_commutator_pad_both e f Y (fun i j => σ (X i j))

variable [PartialOrder A] [StarOrderedRing A]

/-- The represented flattened symmetry is contractive even for a degenerate
representation, since it is the image of an actual unitary. -/
theorem norm_represented_flattened_symmetry_le {n : ℕ} [NeZero n]
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (X : CStarMatrix (Fin n) (Fin n) A) (hX : ‖X‖ ≤ 1) :
    ‖representedMatrix σ (fourfoldMatrixFlatten n (contractionSymmetryUnitary X hX))‖ ≤ 1 := by
  let φ := (representedMatrixHom σ (4 * n)).comp
    (fourfoldMatrixFlatten (A := A) n).toStarAlgHom
  let u := Unitary.map (StarMonoidHom.ofClass φ) (contractionSymmetryUnitary X hX)
  change ‖(u : HilbertCopies H (4 * n) →L[ℂ] HilbertCopies H (4 * n))‖ ≤ 1
  exact (Unitary.linearIsometryEquiv u).toLinearIsometry.norm_toContinuousLinearMap_le

/-- Restoring the original operator after a norm-small replacement loses at
most twice that distance on the flattened unitary test. -/
theorem flattened_symmetry_bound_of_approximation {n : ℕ} [NeZero n]
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Y : H →L[ℂ] H)
    (X : CStarMatrix (Fin n) (Fin n) A) (hX : ‖X‖ ≤ 1)
    (Y₀ : HilbertCopies H (4 * n) →L[ℂ] HilbertCopies H (4 * n))
    {η B : ℝ} (hclose : ‖Y₀ - amplify Y (4 * n)‖ ≤ η)
    (hbound : ‖commutator Y₀
      (representedMatrix σ (fourfoldMatrixFlatten n (contractionSymmetryUnitary X hX)))‖ ≤ B) :
    ‖commutator (amplify Y n) (representedMatrix σ X)‖ ≤ B + 2 * η := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hclose
  have hnorm := norm_represented_flattened_symmetry_le σ X hX
  have hc : ‖amplify Y (4 * n) - Y₀‖ ≤ η := by
    rwa [norm_sub_rev]
  calc
    _ ≤ ‖commutator (amplify Y (4 * n))
      (representedMatrix σ (fourfoldMatrixFlatten n (contractionSymmetryUnitary X hX)))‖ :=
        norm_amplified_commutator_le_flattened_symmetry σ Y X hX
    _ ≤ B + 2 * η *
      ‖representedMatrix σ (fourfoldMatrixFlatten n (contractionSymmetryUnitary X hX))‖ :=
        norm_commutator_le_of_approx _ _ _ hbound hc
    _ ≤ B + 2 * η := by nlinarith

/-- A test of arbitrary matrix size and multiplicity is controlled by one
centered symmetry test in a square array. The symmetry bound is an explicit
hypothesis, rather than an assumed conclusion about all matrix tests. -/
theorem finite_amplification_bound_of_one_symmetry {r h n : ℕ} [NeZero n]
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (e : Fin r ↪ Fin (4 * n)) (f : Fin h ↪ Fin n)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r)
    (X : CStarMatrix (Fin h) (Fin h) A) (hX : ‖X‖ ≤ 1)
    (Y₀ : HilbertCopies (HilbertCopies H (4 * n)) (4 * n) →L[ℂ]
      HilbertCopies (HilbertCopies H (4 * n)) (4 * n))
    {η B : ℝ}
    (hclose : ‖Y₀ - amplify (padArrayOperator e Y) (4 * n)‖ ≤ η)
    (hbound : ‖commutator Y₀
      (representedMatrix (amplifiedScalarRepresentation σ (4 * n))
        (fourfoldMatrixFlatten n (contractionSymmetryUnitary (cstarMatrixPadding f X)
          (by simpa only [norm_cstarMatrixPadding] using hX))))‖ ≤ B) :
    ‖commutator (amplify Y h) (representedMatrix (amplifiedScalarRepresentation σ r) X)‖ ≤
      B + 2 * η := by
  rw [← norm_represented_commutator_pad_both σ e f Y X]
  exact flattened_symmetry_bound_of_approximation
    (amplifiedScalarRepresentation σ (4 * n)) (padArrayOperator e Y)
    (cstarMatrixPadding f X) (by simpa only [norm_cstarMatrixPadding] using hX)
    Y₀ hclose hbound

omit [CompleteSpace H] in
/-- Amplifying the replacement does not enlarge its norm distance. -/
theorem norm_amplify_sub_le (S T : H →L[ℂ] H) (n : ℕ) :
    ‖amplify S n - amplify T n‖ ≤ ‖S - T‖ := by
  have h : amplify S n - amplify T n = amplify (S - T) n := by
    ext x i
    simp only [sub_apply, PiLp.sub_apply, amplify_apply]
  rw [h]
  exact norm_amplify_le (S - T) n

/-- The symmetry appearing in the preceding reduction is selfadjoint,
squares to one, and is centered for the actual normalized matrix trace. -/
theorem padded_flattened_symmetry_properties {h n : ℕ} [NeZero n]
    (τ : A →ₚ[ℂ] ℂ) (f : Fin h ↪ Fin n)
    (X : CStarMatrix (Fin h) (Fin h) A) (hX : ‖X‖ ≤ 1) :
    let S := fourfoldMatrixFlatten n (contractionSymmetryUnitary (cstarMatrixPadding f X)
      (by simpa only [norm_cstarMatrixPadding] using hX))
    star S = S ∧ S * S = 1 ∧ normalizedMatrixTrace τ (4 * n) S = 0 := by
  dsimp only
  refine ⟨?_, ?_, normalizedMatrixTrace_flattened_contractionSymmetry n τ _ _⟩
  · rw [← map_star, contractionSymmetryUnitary_star]
  · rw [← map_mul, contractionSymmetryUnitary_sq, map_one]

/-- Uniform centered-square symmetry bounds, together with the actual norm
approximation, control every finite matrix amplification. This theorem is a
reduction: its symmetry bound must be proved separately in the application. -/
theorem finite_amplification_bound_of_centered_tests {r : ℕ}
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (τ : A →ₚ[ℂ] ℂ)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r) {η B : ℝ}
    (hconstant : 0 ≤ B + 2 * η)
    (hreplace : ∀ (n : ℕ) [NeZero n], ∀ e : Fin r ↪ Fin (4 * n),
      ∃ Y₀ : HilbertCopies (HilbertCopies H (4 * n)) (4 * n) →L[ℂ]
          HilbertCopies (HilbertCopies H (4 * n)) (4 * n),
        ‖Y₀ - amplify (padArrayOperator e Y) (4 * n)‖ ≤ η ∧
        ∀ S : CStarMatrix (Fin (4 * n)) (Fin (4 * n)) A,
          star S = S → S * S = 1 → normalizedMatrixTrace τ (4 * n) S = 0 →
          ‖commutator Y₀ (representedMatrix (amplifiedScalarRepresentation σ (4 * n)) S)‖ ≤ B)
    (h : ℕ) (X : CStarMatrix (Fin h) (Fin h) A) :
    ‖commutator (amplify Y h) (representedMatrix (amplifiedScalarRepresentation σ r) X)‖ ≤
      (B + 2 * η) * ‖X‖ := by
  by_cases hh : h = 0
  · subst h
    have hz : commutator (amplify Y 0)
        (representedMatrix (amplifiedScalarRepresentation σ r) X) = 0 :=
      Subsingleton.elim _ _
    rw [hz, norm_zero]
    exact mul_nonneg hconstant (norm_nonneg X)
  have : NeZero h := ⟨hh⟩
  have hunit (Z : CStarMatrix (Fin h) (Fin h) A) (hZ : ‖Z‖ ≤ 1) :
      ‖commutator (amplify Y h) (representedMatrix (amplifiedScalarRepresentation σ r) Z)‖ ≤
        B + 2 * η := by
    let n := max r h + 1
    have hn : 0 < n := by dsimp [n]; omega
    have : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let e : Fin r ↪ Fin (4 * n) := Fin.castLEEmb (by dsimp [n]; omega)
    let f : Fin h ↪ Fin n := Fin.castLEEmb (by dsimp [n]; omega)
    obtain ⟨Y₀, hclose, htest⟩ := hreplace n e
    apply finite_amplification_bound_of_one_symmetry σ e f Y Z hZ Y₀ hclose
    let hnorm : ‖cstarMatrixPadding f Z‖ ≤ 1 := by
      simpa only [norm_cstarMatrixPadding] using hZ
    obtain ⟨hstar, hsquare, htrace⟩ := padded_flattened_symmetry_properties τ f Z hZ
    exact htest (fourfoldMatrixFlatten n (contractionSymmetryUnitary _ hnorm))
      hstar hsquare htrace
  let ρ := representedMatrixHom (amplifiedScalarRepresentation σ r) h
  let δ := cornerCommutator ρ ρ (amplify Y h)
  have hδ : ‖δ‖ ≤ B + 2 * η := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hconstant
    intro Z hZ
    exact hunit Z hZ.le
  exact (δ.le_opNorm X).trans (mul_le_mul_of_nonneg_right hδ (norm_nonneg X))

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

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_RepresentedFiniteSymmetrization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite matrix averaging in a fixed represented algebra

The scalar bound is supplied on the source C-star algebra. Actual normalized
Haar measures on the finite matrix-unitary groups produce a single operator
commuting with every stage. No von Neumann closure or independently chosen
invariant operator is needed in this step.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A norm perturbation by `δ` changes a source-algebra scalar commutator
bound `δ` into at most `3δ`. -/
theorem represented_scalar_bound_of_close
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Y₀ Y : H →L[ℂ] H)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : ∀ a, ‖commutator Y (σ a)‖ ≤ δ * ‖a‖)
    (hclose : ‖Y₀ - Y‖ ≤ δ) :
    ∀ a, ‖commutator Y₀ (σ a)‖ ≤ (3 * δ) * ‖a‖ := by
  intro a
  calc
    ‖commutator Y₀ (σ a)‖ ≤ δ * ‖a‖ + 2 * δ * ‖σ a‖ :=
      norm_commutator_le_of_approx Y₀ Y (σ a) (hscalar a) hclose
    _ ≤ δ * ‖a‖ + 2 * δ * ‖a‖ := by
      gcongr
      exact NonUnitalStarAlgHom.norm_apply_le σ a
    _ = (3 * δ) * ‖a‖ := by ring

private theorem norm_matrixUnitary_image_le_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (ι : Matrix α α ℂ →⋆ₐ[ℂ] A) (u : Matrix.unitaryGroup α ℂ) :
    ‖ι (u : Matrix α α ℂ)‖ ≤ 1 := by
  let v := Unitary.map (StarMonoidHom.ofClass ι) u
  have h : ‖(v : A)‖ = ‖(1 : A)‖ := by
    simpa only [mul_one] using CStarRing.norm_coe_unitary_mul v (1 : A)
  change ‖(v : A)‖ ≤ 1
  rw [h]
  exact IsStarProjection.norm_le 1 (.one A)

variable {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]

attribute [local instance] finiteMatrixUnitaryCompactSpace
  finiteMatrixUnitaryMeasurableSpace finiteMatrixUnitaryBorelSpace

/-- Actual Haar averages and a weak-operator cluster point give the finite
factor's initial perturbation. The scalar norm is measured on the original
source algebra; the bound and the distance do not depend on matrix sizes. -/
theorem exists_represented_finite_matrix_symmetrization
    [∀ n, Nonempty (I n)]
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ι : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
    (transition : ∀ n m, n ≤ m →
      Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (hcompat : ∀ n m h a, ι m (transition n m h a) = ι n a)
    (Y : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : ∀ a, ‖commutator Y (σ a)‖ ≤ δ * ‖a‖) :
    ∃ Y₀ : H →L[ℂ] H, ‖Y₀‖ ≤ ‖Y‖ ∧ ‖Y₀ - Y‖ ≤ δ ∧
      (∀ a, ‖commutator Y₀ (σ a)‖ ≤ (3 * δ) * ‖a‖) ∧
      ∀ n a, commutator Y₀ (σ (ι n a)) = 0 := by
  let R := fun n => σ.comp (ι n)
  let U := fun n => matrixUnitaryAction (R n)
  let emb := fun n m h => Unitary.map (StarMonoidHom.ofClass (transition n m h))
  have hc n m h u : U m (emb n m h u) = U n u :=
    congrArg σ (hcompat n m h (u : Matrix (I n) (I n) ℂ))
  have hI n : WeaklyIntegrable (finiteMatrixHaarProbability (I := I) n)
      (unitaryConjugate (U n) Y) :=
    weaklyIntegrable_unitaryConjugate _ _ (matrixUnitaryAction_adjoint (R n))
      (matrixUnitaryAction_continuous (R n)) Y
  have hcomm n u : ‖commutator Y (U n u)‖ ≤ δ :=
    (hscalar (ι n (u : Matrix (I n) (I n) ℂ))).trans
      (mul_le_of_le_one_right hδ (norm_matrixUnitary_image_le_one (ι n) u))
  obtain ⟨Y₀, hnorm, hclose, hinv⟩ := exists_simultaneously_symmetrized_close
    (finiteMatrixHaarProbability (I := I)) U
    (fun n => matrixUnitaryAction_norm_le (R n)) (fun n m h u => emb n m h u) hc Y hI hδ hcomm
  refine ⟨Y₀, hnorm, hclose, represented_scalar_bound_of_close σ Y₀ Y hδ hscalar hclose, ?_⟩
  intro n a
  exact commutes_matrix_of_unitaries (R n) Y₀ (hinv n) a

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixSmallCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {n : ℕ} [NeZero n]

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

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixGNSRecovery
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact recovery of finite matrix commutators from the normalized matrix
GNS space. The surjective linear isometry transports the represented
operators and preserves their commutator norms. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {n : ℕ} [NeZero n]

/-- The normalized matrix GNS identification preserves the full commutator
norm, rather than only one inequality. -/
theorem norm_matrixGNSLiftOperator_commutator (τ : A →ₚ[ℂ] ℂ)
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖commutator (matrixGNSLiftOperator τ Y)
      ((normalizedMatrixTrace τ n).gnsStarAlgHom X)‖ =
      ‖commutator (amplify Y n) (matrixLeftArray τ X)‖ := by
  let U := matrixGNSUnitary τ n
  let T := commutator (matrixGNSLiftOperator τ Y)
    ((normalizedMatrixTrace τ n).gnsStarAlgHom X)
  have he : U.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (T.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap) =
      commutator (amplify Y n) (matrixLeftArray τ X) := by
    apply ContinuousLinearMap.ext
    intro ξ
    change U (T (U.symm ξ)) = _
    rw [matrixGNSLiftOperator_commutator, LinearIsometryEquiv.apply_symm_apply]
  calc
    _ = ‖T.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap‖ :=
      (norm_comp_isometricCoordinates T U.symm).symm
    _ = ‖U.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (T.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap)‖ :=
      (norm_isometricCoordinates_comp _ U).symm
    _ = _ := congrArg norm he

/-- The same equality in the notation used by finite amplification. -/
theorem norm_matrixGNSLiftOperator_commutator_represented (τ : A →ₚ[ℂ] ℂ)
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖commutator (matrixGNSLiftOperator τ Y)
      ((normalizedMatrixTrace τ n).gnsStarAlgHom X)‖ =
      ‖commutator (amplify Y n)
        (representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom n) X)‖ :=
  norm_matrixGNSLiftOperator_commutator τ Y X

omit [NeZero n] in
/-- Uniform replacements on square matrix GNS spaces control every finite
standard multiplicity and every matrix size. Normalization of arbitrary
tests, dimension padding, and the two approximation errors are all handled
by the proved dilation reduction. -/
theorem finite_standard_bound_of_matrixGNS_replacements {r : ℕ}
    (τ : A →ₚ[ℂ] ℂ)
    (Y : HilbertCopies τ.GNS r →L[ℂ] HilbertCopies τ.GNS r) {η B : ℝ}
    (hconstant : 0 ≤ B + 2 * η)
    (hreplace : ∀ (m : ℕ) [NeZero m], ∀ e : Fin r ↪ Fin (4 * m),
      ∃ Y₀ : HilbertCopies τ.GNS (4 * m) →L[ℂ] HilbertCopies τ.GNS (4 * m),
        ‖Y₀ - padArrayOperator e Y‖ ≤ η ∧
        ∀ S : CStarMatrix (Fin (4 * m)) (Fin (4 * m)) A,
          star S = S → S * S = 1 → normalizedMatrixTrace τ (4 * m) S = 0 →
          ‖commutator (matrixGNSLiftOperator τ Y₀)
            ((normalizedMatrixTrace τ (4 * m)).gnsStarAlgHom S)‖ ≤ B)
    (h : ℕ) (X : CStarMatrix (Fin h) (Fin h) A) :
    ‖commutator (amplify Y h)
      (representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom r) X)‖ ≤
      (B + 2 * η) * ‖X‖ := by
  apply finite_amplification_bound_of_centered_tests τ.gnsStarAlgHom τ Y hconstant
  intro m _ e
  obtain ⟨Y₀, hclose, hbound⟩ := hreplace m e
  refine ⟨amplify Y₀ (4 * m),
    (norm_amplify_sub_le Y₀ (padArrayOperator e Y) (4 * m)).trans hclose, ?_⟩
  intro S hstar hsquare htrace
  rw [← norm_matrixGNSLiftOperator_commutator_represented]
  exact hbound S hstar hsquare htrace

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FiniteStandardEstimate
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite standard multiplicities from the centered free-corner test

This is a reduction theorem. Its centered-symmetry premise is an explicit
local conclusion to be supplied by the free-corner argument, and is not a
published-input predicate. Haar averaging, multiplicity padding, matrix
GNS transport, symmetry dilation, and restoring the original operator are
all performed by proved lemmas.
-/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]

/-- The centered-symmetry bound `c * (3δ)` for operators commuting with the
finite matrix tower gives the complete finite-standard bound
`(3c+2) * δ`. The only unproved premise in this reduction is the displayed
centered test itself; the initial perturbation is constructed by Haar
averaging rather than assumed. -/
theorem finite_standard_estimate_of_centered_tests_oai
    (τ : A →ₚ[ℂ] ℂ)
    (F : ∀ j, Matrix (I j) (I j) ℂ →⋆ₐ[ℂ] A)
    (transition : ∀ j k, j ≤ k →
      Matrix (I j) (I j) ℂ →⋆ₐ[ℂ] Matrix (I k) (I k) ℂ)
    (hcompat : ∀ j k h a, F k (transition j k h a) = F j a)
    {c : ℝ} (hc : 0 ≤ c)
    (hcentered : ∀ (m : ℕ) [NeZero m]
      (Y₀ : HilbertCopies τ.GNS (4 * m) →L[ℂ] HilbertCopies τ.GNS (4 * m))
      (δ : ℝ), 0 ≤ δ →
      (∀ a, ‖commutator Y₀ (amplify (τ.gnsStarAlgHom a) (4 * m))‖ ≤
        (3 * δ) * ‖a‖) →
      (∀ j a, commutator Y₀ (amplify (τ.gnsStarAlgHom (F j a)) (4 * m)) = 0) →
      ∀ S : CStarMatrix (Fin (4 * m)) (Fin (4 * m)) A,
        star S = S → S * S = 1 → normalizedMatrixTrace τ (4 * m) S = 0 →
        ‖commutator (matrixGNSLiftOperator τ Y₀)
          ((normalizedMatrixTrace τ (4 * m)).gnsStarAlgHom S)‖ ≤ c * (3 * δ))
    {r : ℕ} (Y : HilbertCopies τ.GNS r →L[ℂ] HilbertCopies τ.GNS r)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : ∀ a, ‖commutator Y (amplify (τ.gnsStarAlgHom a) r)‖ ≤ δ * ‖a‖)
    (h : ℕ) (X : CStarMatrix (Fin h) (Fin h) A) :
    ‖commutator (amplify Y h)
      (representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom r) X)‖ ≤
      (3 * c + 2) * δ * ‖X‖ := by
  have hreplace : ∀ (m : ℕ) [NeZero m], ∀ e : Fin r ↪ Fin (4 * m),
      ∃ Y₀ : HilbertCopies τ.GNS (4 * m) →L[ℂ] HilbertCopies τ.GNS (4 * m),
        ‖Y₀ - padArrayOperator e Y‖ ≤ δ ∧
        ∀ S : CStarMatrix (Fin (4 * m)) (Fin (4 * m)) A,
          star S = S → S * S = 1 → normalizedMatrixTrace τ (4 * m) S = 0 →
          ‖commutator (matrixGNSLiftOperator τ Y₀)
            ((normalizedMatrixTrace τ (4 * m)).gnsStarAlgHom S)‖ ≤ c * (3 * δ) := by
    intro m _ e
    have hpad : ∀ a, ‖commutator (padArrayOperator e Y)
        (amplifiedScalarRepresentation τ.gnsStarAlgHom (4 * m) a)‖ ≤ δ * ‖a‖ :=
      (scalar_bound_padArrayOperator_iff τ.gnsStarAlgHom e Y δ).mpr hscalar
    obtain ⟨Y₀, _, hclose, hnew, hstage⟩ :=
      exists_represented_finite_matrix_symmetrization
        (amplifiedScalarRepresentation τ.gnsStarAlgHom (4 * m))
        F transition hcompat (padArrayOperator e Y) hδ hpad
    exact ⟨Y₀, hclose, hcentered m Y₀ δ hδ hnew hstage⟩
  calc
    ‖commutator (amplify Y h)
        (representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom r) X)‖ ≤
        (c * (3 * δ) + 2 * δ) * ‖X‖ :=
      finite_standard_bound_of_matrixGNS_replacements τ Y
        (η := δ) (B := c * (3 * δ)) (by positivity) hreplace h X
    _ = (3 * c + 2) * δ * ‖X‖ := by ring

end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonSimilarity.finite_standard_estimate_of_centered_tests_oai.{u_1, u_2} := @OAI.KadisonSimilarity.finite_standard_estimate_of_centered_tests_oai.{u_1, u_2}
