-- Prove2me | solution 1 for OAI.KadisonSimilarity.free_corner_from_multiplicity_propagation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:25:32.78088+00:00
-- url     : https://prove2.me/submissions/d2b28e14-f43f-40f2-823d-06b769519160

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A006
import Definitions.Def_OAIQ075A010
import Definitions.Def_OAIQ075A016
import Theorems.Thm_OAI_KadisonSimilarity_arcWidth_pos

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_HankelBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite Hankel test in the similarity manuscript

The coefficients here are the actual Fourier coefficients of the narrow-arc
function in Section `hankel`: `sin (l θ) / (π l)`, with `θ = 1/(2N)`.
The lower bound uses the constant vector in the first `N` coordinates.
No assertion about the free-product construction is assumed here.
-/

noncomputable section

namespace KadisonSimilarity

open Finset

theorem arcCoefficient_lower {N l : ℕ} (hN : 0 < N) (hl : 0 < l)
    (hlN : l < 2 * N) :
    2 * arcWidth N / Real.pi ^ 2 ≤ arcCoefficient N l := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hlNr : (l : ℝ) < 2 * N := by exact_mod_cast hlN
  have hx : 0 ≤ (l : ℝ) * arcWidth N := by
    exact mul_nonneg hlr.le (arcWidth_pos hN).le
  have hx1 : (l : ℝ) * arcWidth N < 1 := by
    unfold arcWidth
    rw [mul_one_div, div_lt_one (by positivity)]
    exact hlNr
  have hxpi : (l : ℝ) * arcWidth N ≤ Real.pi / 2 := by
    linarith [Real.pi_gt_three]
  have hs := Real.mul_le_sin hx hxpi
  unfold arcCoefficient
  apply (le_div_iff₀ (mul_pos Real.pi_pos hlr)).2
  calc
    (2 * arcWidth N / Real.pi ^ 2) * (Real.pi * l) =
        2 / Real.pi * (l * arcWidth N) := by
          field_simp
    _ ≤ Real.sin (l * arcWidth N) := hs

theorem arcHankelMatrix_entry_lower {N : ℕ} (hN : 0 < N) (j k : Fin N) :
    2 * arcWidth N / Real.pi ^ 2 ≤ arcHankelMatrix N j k := by
  apply arcCoefficient_lower hN
  · omega
  · have := j.isLt
    have := k.isLt
    omega

/-- Cancellation of the nonzero corner trace in the final Hankel estimate. -/
theorem cancel_corner_trace {u x c₀ ε : ℝ} (hu : 0 < u)
    (h : u / (2 * Real.pi ^ 2) * x ≤ 3 * u * (1 + 4 * c₀) * ε) :
    x ≤ 6 * Real.pi ^ 2 * (1 + 4 * c₀) * ε := by
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have h' := (div_le_iff₀ (by positivity : 0 < 2 * Real.pi ^ 2)).1
    (show (u * x) / (2 * Real.pi ^ 2) ≤ 3 * u * (1 + 4 * c₀) * ε by
      simpa [div_mul_eq_mul_div] using h)
  apply (mul_le_mul_iff_right₀ hu).1
  nlinarith [h']

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_OperatorAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

section Compression

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

open ContinuousLinearMap

/-- Exact compression identity, including both full-codomain errors. -/
theorem compression_commutator_identity (G T : H →L[ℂ] H)
    (J : K →L[ℂ] K) (ι : K →L[ℂ] H) :
    commutator J (ι.adjoint.comp (T.comp ι)) =
      ι.adjoint.comp ((commutator G T).comp ι) -
        (G.adjoint.comp ι - ι.comp J.adjoint).adjoint.comp (T.comp ι) +
        ι.adjoint.comp (T.comp (G.comp ι - ι.comp J)) := by
  simp only [map_sub, adjoint_comp, adjoint_adjoint, sub_comp, comp_sub,
    comp_assoc, commutator, mul_def]
  abel

/-- Lemma `lem:compressed-commutator`: a contractive inclusion transfers a
commutator estimate, with one contribution from each intertwining error. -/
theorem norm_compressed_commutator_le (G T : H →L[ℂ] H)
    (J : K →L[ℂ] K) (ι : K →L[ℂ] H) {ε η : ℝ}
    (hι : ‖ι‖ ≤ 1)
    (hG : ‖commutator G T‖ ≤ ε * ‖T‖)
    (hR : ‖G.comp ι - ι.comp J‖ ≤ η)
    (hR' : ‖G.adjoint.comp ι - ι.comp J.adjoint‖ ≤ η) :
    ‖commutator J (ι.adjoint.comp (T.comp ι))‖ ≤ (ε + 2 * η) * ‖T‖ := by
  have hε : 0 ≤ ε * ‖T‖ := (norm_nonneg _).trans hG
  have hη : 0 ≤ η := (norm_nonneg _).trans hR
  have hfirst : ‖ι.adjoint.comp ((commutator G T).comp ι)‖ ≤ ε * ‖T‖ := by
    calc
      _ ≤ ‖ι.adjoint‖ * (‖commutator G T‖ * ‖ι‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (opNorm_comp_le _ _) (norm_nonneg _))
      _ = ‖ι‖ * (‖commutator G T‖ * ‖ι‖) := by rw [adjoint.norm_map]
      _ ≤ 1 * (ε * ‖T‖ * 1) := by gcongr
      _ = ε * ‖T‖ := by ring
  have hsecond :
      ‖(G.adjoint.comp ι - ι.comp J.adjoint).adjoint.comp (T.comp ι)‖ ≤
        η * ‖T‖ := by
    calc
      _ ≤ ‖(G.adjoint.comp ι - ι.comp J.adjoint).adjoint‖ * (‖T‖ * ‖ι‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (opNorm_comp_le _ _) (norm_nonneg _))
      _ = ‖G.adjoint.comp ι - ι.comp J.adjoint‖ * (‖T‖ * ‖ι‖) := by
        rw [adjoint.norm_map]
      _ ≤ η * (‖T‖ * 1) := by gcongr
      _ = η * ‖T‖ := by ring
  have hthird : ‖ι.adjoint.comp (T.comp (G.comp ι - ι.comp J))‖ ≤ η * ‖T‖ := by
    calc
      _ ≤ ‖ι.adjoint‖ * (‖T‖ * ‖G.comp ι - ι.comp J‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (opNorm_comp_le _ _) (norm_nonneg _))
      _ = ‖ι‖ * (‖T‖ * ‖G.comp ι - ι.comp J‖) := by rw [adjoint.norm_map]
      _ ≤ 1 * (‖T‖ * η) := by gcongr
      _ = η * ‖T‖ := by ring
  rw [compression_commutator_identity]
  calc
    _ ≤ (‖ι.adjoint.comp ((commutator G T).comp ι)‖ +
        ‖(G.adjoint.comp ι - ι.comp J.adjoint).adjoint.comp (T.comp ι)‖) +
        ‖ι.adjoint.comp (T.comp (G.comp ι - ι.comp J))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (ε * ‖T‖ + η * ‖T‖) + η * ‖T‖ :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ = (ε + 2 * η) * ‖T‖ := by ring

/-- The manuscript's constant after the two propagation errors are substituted. -/
theorem norm_compressed_commutator_le_paper (G T : H →L[ℂ] H)
    (J : K →L[ℂ] K) (ι : K →L[ℂ] H) {ε c₀ : ℝ}
    (hι : ‖ι‖ ≤ 1)
    (hG : ‖commutator G T‖ ≤ ε * ‖T‖)
    (hR : ‖G.comp ι - ι.comp J‖ ≤ 2 * c₀ * ε)
    (hR' : ‖G.adjoint.comp ι - ι.comp J.adjoint‖ ≤ 2 * c₀ * ε) :
    ‖commutator J (ι.adjoint.comp (T.comp ι))‖ ≤ (1 + 4 * c₀) * ε * ‖T‖ := by
  convert norm_compressed_commutator_le G T J ι hι hG hR hR' using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Compression

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_Amplification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.mapCopies_apply _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_matrixOperator _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_apply _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_zero _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.KadisonSimilarity.vonNeumannInnerDerivation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
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
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_HankelCommutator
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.mapCopies_apply _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_matrixOperator _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_apply _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_zero _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A finite Hankel matrix detects the base commutator

The constant-coordinate compression gives the tensor-product norm lower bound
needed by the paper without introducing any infinite matrix norm assumption.
-/

noncomputable section
namespace KadisonSimilarity

open Finset ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem norm_constantCopies_le (N : ℕ) :
    ‖constantCopies (H := H) N‖ ≤ Real.sqrt N := by
  apply opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  simp

/-- Compressing a scalar operator matrix to constant coordinates sums all
its coefficients. -/
theorem constantCopies_compression (N : ℕ) (M : Matrix (Fin N) (Fin N) ℝ)
    (T : H →L[ℂ] H) :
    (constantCopies N).adjoint.comp
      ((matrixOperator (fun i j => (M i j : ℂ) • T)).comp (constantCopies N)) =
      ((∑ i : Fin N, ∑ j : Fin N, M i j : ℝ) : ℂ) • T := by
  ext x
  simp only [comp_apply, constantCopies_adjoint_apply]
  simp [matrixOperator, constantCopies, ← Finset.sum_smul, -Complex.ofReal_sum]

theorem norm_constantCopies_compression_le (N : ℕ)
    (T : HilbertCopies H N →L[ℂ] HilbertCopies H N) :
    ‖(constantCopies N).adjoint.comp (T.comp (constantCopies N))‖ ≤ N * ‖T‖ := by
  let V : H →L[ℂ] HilbertCopies H N := constantCopies N
  change ‖V.adjoint.comp (T.comp V)‖ ≤ (N : ℝ) * ‖T‖
  have hinner : ‖T.comp V‖ ≤ ‖T‖ * ‖V‖ := opNorm_comp_le T V
  have houter : ‖V.adjoint.comp (T.comp V)‖ ≤ ‖V.adjoint‖ * ‖T.comp V‖ :=
    opNorm_comp_le V.adjoint (T.comp V)
  have hV : ‖V‖ ≤ Real.sqrt N := norm_constantCopies_le N
  have hVs : ‖V.adjoint‖ ≤ Real.sqrt N := by rwa [adjoint.norm_map]
  calc
    _ ≤ ‖V.adjoint‖ * (‖T‖ * ‖V‖) :=
      houter.trans (mul_le_mul_of_nonneg_left hinner (norm_nonneg _))
    _ ≤ Real.sqrt N * (‖T‖ * Real.sqrt N) := by gcongr
    _ = (Real.sqrt N) ^ 2 * ‖T‖ := by ring
    _ = N * ‖T‖ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]

/-- A matrix with coefficients bounded below by `c ≥ 0` detects a factor
`N * c` of the norm of its common operator entry. -/
theorem norm_scalar_operator_matrix_lower {N : ℕ} (hN : 0 < N)
    (M : Matrix (Fin N) (Fin N) ℝ) (T : H →L[ℂ] H) {c : ℝ}
    (hc : 0 ≤ c) (hM : ∀ i j, c ≤ M i j) :
    N * c * ‖T‖ ≤ ‖matrixOperator (fun i j => (M i j : ℂ) • T)‖ := by
  let s : ℝ := ∑ i : Fin N, ∑ j : Fin N, M i j
  have hsum : (N : ℝ) * (N * c) ≤ s := by
    calc
      _ = ∑ _i : Fin N, ∑ _j : Fin N, c := by simp
      _ ≤ s := sum_le_sum fun i _ => sum_le_sum fun j _ => hM i j
  have hs : 0 ≤ s := (by positivity : 0 ≤ (N : ℝ) * (N * c)).trans hsum
  have hcomp := norm_constantCopies_compression_le N
    (matrixOperator (fun i j => (M i j : ℂ) • T))
  rw [constantCopies_compression, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hs] at hcomp
  have hmul := mul_le_mul_of_nonneg_right hsum (norm_nonneg T)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply (mul_le_mul_iff_right₀ hNr).mp
  nlinarith

/-- The actual narrow-arc matrix detects a uniform fraction of the base norm. -/
theorem norm_arc_operator_matrix_lower {N : ℕ} (hN : 0 < N) (T : H →L[ℂ] H) :
    (1 / Real.pi ^ 2) * ‖T‖ ≤
      ‖matrixOperator (fun i j => (arcHankelMatrix N i j : ℂ) • T)‖ := by
  have h := norm_scalar_operator_matrix_lower hN (arcHankelMatrix N) T
    (by unfold arcWidth; positivity) (arcHankelMatrix_entry_lower hN)
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold arcWidth
  field_simp

omit [CompleteSpace H] in
/-- Scalar diagonal terms vanish from the commutator. -/
theorem commutator_scalar_id_add (B S : H →L[ℂ] H) (a b : ℂ) :
    commutator B (a • ContinuousLinearMap.id ℂ H + b • S) = b • commutator B S := by
  change commutator B (a • (1 : H →L[ℂ] H) + b • S) = _
  simp only [commutator, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    mul_one, one_mul, smul_sub]
  abel

/-- The Toeplitz part of the finite Fourier compression contributes no
commutator; the Hankel part detects the base operator. -/
theorem norm_commutator_fourier_matrix_lower {N : ℕ} (hN : 0 < N)
    (B S : H →L[ℂ] H) (toeplitz : Matrix (Fin N) (Fin N) ℝ) :
    (1 / Real.pi ^ 2) * ‖commutator B S‖ ≤
      ‖commutator (amplify B N)
        (matrixOperator (fun i j => (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ H +
          (arcHankelMatrix N i j : ℂ) • S))‖ := by
  let X : Matrix (Fin N) (Fin N) (H →L[ℂ] H) := fun i j =>
    (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ H + (arcHankelMatrix N i j : ℂ) • S
  have hX := commutator_amplify_matrixOperator B X
  change _ ≤ ‖commutator (amplify B N) (matrixOperator X)‖
  rw [hX]
  simpa only [X, commutator_scalar_id_add] using norm_arc_operator_matrix_lower hN (commutator B S)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_OrthogonalColumns
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.mapCopies_apply _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_apply _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_zero _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite orthogonal word levels and their full-codomain errors. -/

noncomputable section
namespace KadisonSimilarity

open Finset ContinuousLinearMap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Orthogonal output levels allow the same bound at every matrix size. -/
theorem norm_sumColumns_le {N : ℕ} (U : Fin N → H →L[ℂ] K) {c : ℝ}
    (hc : 0 ≤ c) (hU : ∀ i, ‖U i‖ ≤ c)
    (horth : ∀ i j, i ≠ j → ∀ x y, inner ℂ (U i x) (U j y) = 0) :
    ‖sumColumns U‖ ≤ c := by
  apply opNorm_le_bound _ hc
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp
  rw [sumColumns_apply, norm_sum_sq_of_pairwise_orthogonal _ (fun i j hij => horth i j hij _ _)]
  calc
    _ ≤ ∑ i : Fin N, (c * ‖x i‖) ^ 2 := by
      apply sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) ((U i).le_opNorm (x i) |>.trans
        (mul_le_mul_of_nonneg_right (hU i) (norm_nonneg _))) 2
    _ = (c * ‖x‖) ^ 2 := by
      simp_rw [mul_pow]
      rw [← mul_sum, ← PiLp.norm_sq_eq_of_L2, ← mul_pow]

variable [CompleteSpace H] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- The full error of an assembled inclusion is the assembly of its level
errors. -/
theorem sumColumns_intertwining_error {N : ℕ} (U : Fin N → H →L[ℂ] K)
    (G : K →L[ℂ] K) (B : H →L[ℂ] H) :
    G.comp (sumColumns U) - (sumColumns U).comp (amplify B N) =
      sumColumns (fun i => G.comp (U i) - (U i).comp B) := by
  ext x
  simp [sumColumns_apply, map_sum, Finset.sum_sub_distrib]

omit [CompleteSpace H] [CompleteSpace K] in
/-- The propagation estimate on individual orthogonal word levels gives a
full-codomain norm bound on their assembled inclusion. -/
theorem norm_word_inclusion_error_le {N : ℕ}
    (U : Fin N → H →L[ℂ] K) (L : Fin N → Submodule ℂ K)
    (hU : ∀ i x, U i x ∈ L i)
    (horth : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, inner ℂ x y = 0)
    (G : K →L[ℂ] K) (B : H →L[ℂ] H)
    (hG : ∀ i x, x ∈ L i → G x ∈ L i)
    {η : ℝ} (hη : 0 ≤ η)
    (herr : ∀ i, ‖G.comp (U i) - (U i).comp B‖ ≤ η) :
    ‖G.comp (sumColumns U) - (sumColumns U).comp (amplify B N)‖ ≤ η := by
  rw [sumColumns_intertwining_error]
  apply norm_sumColumns_le _ hη herr
  intro i j hij x y
  apply horth i j hij
  · exact (L i).sub_mem (hG i _ (hU i x)) (hU i (B x))
  · exact (L j).sub_mem (hG j _ (hU j y)) (hU j (B y))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeCornerEndgame
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.mapCopies_apply _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_matrixOperator _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_apply _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_zero _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.vonNeumannInnerDerivation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite Fourier test completing the free-corner estimate

Given the actual finite word-level inclusion and its Fourier compression,
the two propagation errors, narrow-arc norm bound, and Hankel test imply the
paper's corner-independent constant. The free-product construction of those
data is not assumed to be a published theorem.
-/

noncomputable section
namespace KadisonSimilarity

open ContinuousLinearMap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] in
/-- Scaling the test operator scales its commutator. -/
theorem commutator_smul_right (B S : H →L[ℂ] H) (c : ℂ) :
    commutator B (c • S) = c • commutator B S := by
  simp only [commutator, mul_smul_comm, smul_mul_assoc, smul_sub]

omit [CompleteSpace H] in
/-- Scalar multiplication of a bounded operator has the expected norm. -/
theorem norm_complex_smul_endomorphism (T : H →L[ℂ] H) (c : ℂ) :
    ‖c • T‖ = ‖c‖ * ‖T‖ := norm_smul c T

/-- A finite Fourier compression suffices to finish the corner estimate.
All assumptions describe constructed operators and their checked identities;
none assumes the free-corner conclusion. -/
theorem free_corner_bound_of_fourier_compression
    {N : ℕ} (hN : 0 < N) (G T : H →L[ℂ] H) (B S : K →L[ℂ] K)
    (ι : HilbertCopies K N →L[ℂ] H)
    (toeplitz : Matrix (Fin N) (Fin N) ℝ)
    {u ε c₀ : ℝ} (hu : 0 < u) (hε : 0 ≤ ε) (hc₀ : 0 ≤ c₀)
    (hι : ‖ι‖ ≤ 1) (hT : ‖T‖ ≤ 3 * u)
    (hG : ‖commutator G T‖ ≤ ε * ‖T‖)
    (hR : ‖G.comp ι - ι.comp (amplify B N)‖ ≤ 2 * c₀ * ε)
    (hR' : ‖G.adjoint.comp ι - ι.comp (amplify B N).adjoint‖ ≤ 2 * c₀ * ε)
    (hfourier : ι.adjoint.comp (T.comp ι) =
      (u : ℂ) • matrixOperator (fun i j =>
        (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ K +
          (arcHankelMatrix N i j : ℂ) • S)) :
    ‖commutator B S‖ ≤ 6 * Real.pi ^ 2 * (1 + 4 * c₀) * ε := by
  let X : Matrix (Fin N) (Fin N) (K →L[ℂ] K) := fun i j =>
    (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ K +
      (arcHankelMatrix N i j : ℂ) • S
  have hlower := norm_commutator_fourier_matrix_lower hN B S toeplitz
  change (1 / Real.pi ^ 2) * ‖commutator B S‖ ≤
    ‖commutator (amplify B N) (matrixOperator X)‖ at hlower
  have hupper := norm_compressed_commutator_le_paper G T (amplify B N) ι hι hG hR hR'
  have hscaled : ‖commutator (amplify B N) (ι.adjoint.comp (T.comp ι))‖ =
      u * ‖commutator (amplify B N) (matrixOperator X)‖ := by
    have hf : ι.adjoint.comp (T.comp ι) = (u : ℂ) • matrixOperator X := hfourier
    rw [hf, commutator_smul_right]
    have hs : ‖(u : ℂ) • commutator (amplify B N) (matrixOperator X)‖ =
        ‖(u : ℂ)‖ * ‖commutator (amplify B N) (matrixOperator X)‖ :=
      norm_complex_smul_endomorphism _ (u : ℂ)
    rw [hs, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  rw [hscaled] at hupper
  apply cancel_corner_trace hu
  have hhalf : 1 / (2 * Real.pi ^ 2) ≤ 1 / Real.pi ^ 2 := by
    apply one_div_le_one_div_of_le (sq_pos_of_pos Real.pi_pos)
    nlinarith [sq_nonneg Real.pi]
  calc
    u / (2 * Real.pi ^ 2) * ‖commutator B S‖ =
        u * ((1 / (2 * Real.pi ^ 2)) * ‖commutator B S‖) := by ring
    _ ≤ u * ((1 / Real.pi ^ 2) * ‖commutator B S‖) := by gcongr
    _ ≤ u * ‖commutator (amplify B N) (matrixOperator X)‖ :=
      mul_le_mul_of_nonneg_left hlower hu.le
    _ ≤ (1 + 4 * c₀) * ε * ‖T‖ := hupper
    _ ≤ (1 + 4 * c₀) * ε * (3 * u) := by gcongr
    _ = 3 * u * (1 + 4 * c₀) * ε := by ring

/-- The word-level hypotheses of propagation imply the complete finite Fourier
endgame, including both full-codomain errors. -/
theorem free_corner_bound_of_word_levels
    {N : ℕ} (hN : 0 < N) (G T : H →L[ℂ] H) (B S : K →L[ℂ] K)
    (U : Fin N → K →L[ℂ] H) (L : Fin N → Submodule ℂ H)
    (hUnorm : ∀ i, ‖U i‖ ≤ 1) (hUlevel : ∀ i x, U i x ∈ L i)
    (horth : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, inner ℂ x y = 0)
    (hGlevel : ∀ i x, x ∈ L i → G x ∈ L i)
    (hGstarlevel : ∀ i x, x ∈ L i → G.adjoint x ∈ L i)
    (toeplitz : Matrix (Fin N) (Fin N) ℝ)
    {u ε c₀ : ℝ} (hu : 0 < u) (hε : 0 ≤ ε) (hc₀ : 0 ≤ c₀)
    (hT : ‖T‖ ≤ 3 * u) (hG : ‖commutator G T‖ ≤ ε * ‖T‖)
    (herr : ∀ i, ‖G.comp (U i) - (U i).comp B‖ ≤ 2 * c₀ * ε)
    (herr' : ∀ i, ‖G.adjoint.comp (U i) - (U i).comp B.adjoint‖ ≤ 2 * c₀ * ε)
    (hfourier : (sumColumns U).adjoint.comp (T.comp (sumColumns U)) =
      (u : ℂ) • matrixOperator (fun i j =>
        (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ K +
          (arcHankelMatrix N i j : ℂ) • S)) :
    ‖commutator B S‖ ≤ 6 * Real.pi ^ 2 * (1 + 4 * c₀) * ε := by
  have hι : ‖sumColumns U‖ ≤ 1 := norm_sumColumns_le U (by norm_num) hUnorm
    (fun i j hij x y => horth i j hij _ (hUlevel i x) _ (hUlevel j y))
  have hη : 0 ≤ 2 * c₀ * ε := by positivity
  have hR := norm_word_inclusion_error_le U L hUlevel horth G B hGlevel hη herr
  have hR' := norm_word_inclusion_error_le U L hUlevel horth G.adjoint B.adjoint
    hGstarlevel hη herr'
  rw [← adjoint_amplify] at hR'
  exact free_corner_bound_of_fourier_compression hN G T B S (sumColumns U)
    toeplitz hu hε hc₀ hι hT hG hR hR' hfourier

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_WordPropagationTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the multiplicity propagation estimate to the actual orthogonal
word columns used by the finite Fourier test. -/

noncomputable section
namespace KadisonSimilarity

universe u
variable {E F : Type u} {K H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {J : ℕ → Type*} [∀ n, NormedAddCommGroup (J n)]
  [∀ n, InnerProductSpace ℂ (J n)] [∀ n, CompleteSpace (J n)]

variable (U : OrthogonalWordLevels (MultiplicityWordSpace J E F) H)

omit [CompleteSpace H] [CompleteSpace K] [∀ n, CompleteSpace (J n)] in
/-- A multiplicity error has exactly the same norm in a normalized word
column. This supplies the full-output error needed in the Hankel test. -/
theorem norm_repeatedWordInclusion_error_le (n : ℕ) (R : K →ₗᵢ[ℂ] J n)
    (d : E) (r : F) (hd : ‖d‖ = 1) (hr : ‖r‖ = 1)
    (Y : H →L[ℂ] H) (B : K →L[ℂ] K) (Bn : J n →L[ℂ] J n)
    (hY : ∀ v, Y (U.inclusion n (hilbertTensorInsert v
        (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert (Bn v)
        (endpointWord d (fun _ : Fin n => r))))
    {η : ℝ} (hη : 0 ≤ η)
    (hprop : ∀ x, ‖Bn (R x) - R (B x)‖ ≤ η * ‖x‖) :
    ‖Y.comp (repeatedWordInclusion U n R d r hd hr).toContinuousLinearMap -
      (repeatedWordInclusion U n R d r hd hr).toContinuousLinearMap.comp B‖ ≤ η := by
  apply ContinuousLinearMap.opNorm_le_bound _ hη
  intro x
  change ‖Y (U.inclusion n (hilbertTensorInsert (R x)
      (endpointWord d (fun _ : Fin n => r)))) -
    U.inclusion n (hilbertTensorInsert (R (B x))
      (endpointWord d (fun _ : Fin n => r)))‖ ≤ _
  rw [hY, ← map_sub, LinearIsometry.norm_map]
  change ‖hilbertTensorRightInsert (endpointWord d (fun _ : Fin n => r)) (Bn (R x)) -
    hilbertTensorRightInsert (endpointWord d (fun _ : Fin n => r)) (R (B x))‖ ≤ _
  rw [← map_sub, hilbertTensorRightInsert_apply, norm_hilbertTensorInsert,
    norm_endpointWord_constant d r hd hr, mul_one]
  exact hprop x

/-- The finite Fourier test consumes the derived multiplicity propagation
bounds, with the orthogonality and full-column errors constructed here. -/
theorem free_corner_from_multiplicity_propagation_oai
    {N : ℕ} (hN : 0 < N) (R : ∀ n, K →ₗᵢ[ℂ] J n)
    (d : E) (r : F) (hd : ‖d‖ = 1) (hr : ‖r‖ = 1)
    (Y T : H →L[ℂ] H) (B S : K →L[ℂ] K) (Bn : ∀ n, J n →L[ℂ] J n)
    (hY : ∀ n v, Y (U.inclusion n (hilbertTensorInsert v
        (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert (Bn n v)
        (endpointWord d (fun _ : Fin n => r))))
    (hYstar : ∀ n v, Y.adjoint (U.inclusion n (hilbertTensorInsert v
        (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert ((Bn n).adjoint v)
        (endpointWord d (fun _ : Fin n => r))))
    (hlevel : ∀ n x, Y (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range)
    (hlevelstar : ∀ n x, Y.adjoint (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range)
    (toeplitz : Matrix (Fin N) (Fin N) ℝ)
    {u ε c₀ : ℝ} (hu : 0 < u) (hε : 0 ≤ ε) (hc₀ : 0 ≤ c₀)
    (hT : ‖T‖ ≤ 3 * u) (hcomm : ‖commutator Y T‖ ≤ ε * ‖T‖)
    (hprop : ∀ n x, ‖Bn n (R n x) - R n (B x)‖ ≤ 2 * c₀ * ε * ‖x‖)
    (hpropstar : ∀ n x, ‖(Bn n).adjoint (R n x) - R n (B.adjoint x)‖ ≤
      2 * c₀ * ε * ‖x‖)
    (hfourier :
      let V : Fin N → K →L[ℂ] H := fun i =>
        (repeatedWordInclusion U i.val (R i.val) d r hd hr).toContinuousLinearMap
      (sumColumns V).adjoint.comp (T.comp (sumColumns V)) =
        (u : ℂ) • matrixOperator (fun i j =>
          (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ K +
            (arcHankelMatrix N i j : ℂ) • S)) :
    ‖commutator B S‖ ≤ 6 * Real.pi ^ 2 * (1 + 4 * c₀) * ε := by
  let V : Fin N → K →L[ℂ] H := fun i =>
    (repeatedWordInclusion U i.val (R i.val) d r hd hr).toContinuousLinearMap
  let L : Fin N → Submodule ℂ H := fun i => (U.inclusion i.val).toLinearMap.range
  have hnorm (i : Fin N) : ‖V i‖ ≤ 1 :=
    (repeatedWordInclusion U i.val (R i.val) d r hd hr).norm_toContinuousLinearMap_le
  have hmem (i : Fin N) (x : K) : V i x ∈ L i := ⟨_, rfl⟩
  have horth (i j : Fin N) (hij : i ≠ j) (x : H) (hx : x ∈ L i)
      (y : H) (hy : y ∈ L j) : inner ℂ x y = 0 := by
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact U.orthogonal i.val j.val (fun h => hij (Fin.ext h)) a b
  apply free_corner_bound_of_word_levels hN Y T B S V L hnorm hmem horth
    (fun i x hx => by obtain ⟨a, rfl⟩ := hx; exact hlevel i.val a)
    (fun i x hx => by obtain ⟨a, rfl⟩ := hx; exact hlevelstar i.val a)
    toeplitz hu hε hc₀ hT hcomm
  · intro i
    exact norm_repeatedWordInclusion_error_le U i.val (R i.val) d r hd hr Y B
      (Bn i.val) (hY i.val) (by positivity) (hprop i.val)
  · intro i
    exact norm_repeatedWordInclusion_error_le U i.val (R i.val) d r hd hr Y.adjoint B.adjoint
      (Bn i.val).adjoint (hYstar i.val) (by positivity) (hpropstar i.val)
  · exact hfourier

end KadisonSimilarity

end

end OAI
end

theorem solution.{u, u_1, u_2, u_3} : type_of% @OAI.KadisonSimilarity.free_corner_from_multiplicity_propagation_oai.{u, u_1, u_2, u_3} := @OAI.KadisonSimilarity.free_corner_from_multiplicity_propagation_oai.{u, u_1, u_2, u_3}
