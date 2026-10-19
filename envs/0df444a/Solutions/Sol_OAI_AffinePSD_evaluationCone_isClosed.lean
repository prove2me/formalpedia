-- Prove2me | solution 1 for OAI.AffinePSD.evaluationCone_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:35:31.226181+00:00
-- url     : https://prove2.me/submissions/b6e515ed-c753-4183-a026-beaa96f53c47

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/OrthogonalCone.lean:L39-L59
-- (upload_full_project.md Phase 4): solution for node OAI.AffinePSD.evaluationCone_isClosed. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Model
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests__MatchingAffineLift
import Theorems.Thm_OAI_AffinePSD_evaluationCone_isClosed_of_diagonal

-- ---- from OAI.Combinatorics.MatchingPSD.OrthogonalCone ----
namespace OAI

namespace AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

lemma trace_orthogonal_congruence (U A D : Matrix R R ℝ)
    (hU : U * Uᵀ = 1) :
    ((Uᵀ * A * U) * (Uᵀ * D * U)).trace = (A * D).trace := by
  have he : (Uᵀ * A * U) * (Uᵀ * D * U) = Uᵀ * (A * D) * U := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᵀ, hU, Matrix.one_mul]
  rw [he, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

omit [Fintype I] in
lemma evaluationCone_orthogonal (B : I → Matrix R R ℝ)
    (U : Matrix R R ℝ) (hU' : U * Uᵀ = 1) :
    evaluationCone (fun i => Uᵀ * B i * U) = evaluationCone B := by
  ext y
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨U * A * Uᵀ, ?_, ?_⟩
    · simpa using hA.mul_mul_conjTranspose_same U
    · ext i
      change (U * A * Uᵀ * B i).trace = (A * (Uᵀ * B i * U)).trace
      rw [Matrix.mul_assoc U A Uᵀ, Matrix.mul_assoc U (A * Uᵀ) (B i),
        Matrix.trace_mul_comm U]
      simp only [Matrix.mul_assoc]
  · rintro ⟨A, hA, rfl⟩
    refine ⟨Uᵀ * A * U, ?_, ?_⟩
    · simpa using hA.conjTranspose_mul_mul_same U
    · ext i
      exact trace_orthogonal_congruence U A (B i) hU'

lemma evaluationCone_isClosed (B : I → Matrix R R ℝ)
    (hB : ∀ i, (B i).PosSemidef) : IsClosed (evaluationCone B) := by
  classical
  have hS : (∑ i, B i).PosSemidef := Matrix.posSemidef_sum _ (fun i _ => hB i)
  let U : Matrix R R ℝ := hS.isHermitian.eigenvectorUnitary
  let d : R → ℝ := hS.isHermitian.eigenvalues
  have hU : Uᵀ * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hS.isHermitian.eigenvectorUnitary.property.1
  have hU' : U * Uᵀ = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hS.isHermitian.eigenvectorUnitary.property.2
  have hspec : ∑ i, B i = U * diagonal d * Uᵀ := by
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, U, d] using hS.isHermitian.spectral_theorem
  rw [← evaluationCone_orthogonal B U hU']
  refine evaluationCone_isClosed_of_diagonal _ (fun i => ?_) d ?_
  · simpa using (hB i).conjTranspose_mul_mul_same U
  · rw [← Matrix.sum_mul, ← Matrix.mul_sum, hspec]
    simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
    rw [Matrix.mul_assoc, hU, Matrix.mul_one]

end AffinePSD

end OAI

-- ---- platform node ----
open OAI OAI.AffinePSD
open Matrix Finset
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.AffinePSD.evaluationCone_isClosed := @_root_.OAI.AffinePSD.evaluationCone_isClosed
