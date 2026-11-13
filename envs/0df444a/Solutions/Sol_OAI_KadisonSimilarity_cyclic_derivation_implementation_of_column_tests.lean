-- Prove2me | solution 1 for OAI.KadisonSimilarity.cyclic_derivation_implementation_of_column_tests
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:45:41.459214+00:00
-- url     : https://prove2.me/submissions/3886e632-e8d7-4624-bea7-0c0d5def2941

import Mathlib
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A017
import Definitions.Def_OAIQ075A018
import Theorems.Thm_OAI_KadisonSimilarity_dicksonTwoBound_proved

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_Derivations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_matrixOperator _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_apply _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_zero _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.NaimarkZFC.gns_apply_coe
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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.pairRepresentation_fst _root_.OAI.KadisonSimilarity.pairRepresentation_snd _root_.OAI.KadisonSimilarity.rectangularDiagonalStarHom_apply _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.sharpHom_apply _root_.OAI.KadisonSimilarity.sharpVectorMap_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.NaimarkZFC.gns_apply_coe
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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.pairRepresentation_fst _root_.OAI.KadisonSimilarity.pairRepresentation_snd _root_.OAI.KadisonSimilarity.rectangularDiagonalStarHom_apply _root_.OAI.KadisonSimilarity.sharpHom_apply _root_.OAI.KadisonSimilarity.sharpVectorMap_apply _root_.OAI.NaimarkZFC.gns_apply_coe
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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_matrixOperator _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.pairRepresentation_fst _root_.OAI.KadisonSimilarity.pairRepresentation_snd _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.sharpHom_apply _root_.OAI.KadisonSimilarity.sharpVectorMap_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.NaimarkZFC.gns_apply_coe
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
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicColumnTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.pairRepresentation_fst _root_.OAI.KadisonSimilarity.pairRepresentation_snd _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.NaimarkZFC.gns_apply_coe
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
theorem cyclic_derivation_implementation_of_column_tests_oai
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

end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonSimilarity.cyclic_derivation_implementation_of_column_tests_oai.{u_1, u_2, u_3} := @OAI.KadisonSimilarity.cyclic_derivation_implementation_of_column_tests_oai.{u_1, u_2, u_3}
