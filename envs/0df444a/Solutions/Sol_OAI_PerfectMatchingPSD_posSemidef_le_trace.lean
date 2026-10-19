-- Prove2me | solution 1 for OAI.PerfectMatchingPSD.posSemidef_le_trace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:53:04.57423+00:00
-- url     : https://prove2.me/submissions/058972fb-3053-4c68-9e2c-0b181f4d31c5

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/SquareRootDisturbance.lean:L73-L92
-- (upload_full_project.md Phase 4): solution for node OAI.PerfectMatchingPSD.posSemidef_le_trace. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages

-- ---- from OAI.Combinatorics.MatchingPSD.SquareRootDisturbance ----
namespace OAI

universe u_1

namespace PerfectMatchingPSD
open Matrix
open scoped MatrixOrder Matrix.Norms.Frobenius
variable {R : Type u_1} [Fintype R] [DecidableEq R]

lemma posSemidef_le_trace {A : Matrix R R ℝ} (hA : A.PosSemidef) :
    A ≤ A.trace • (1 : Matrix R R ℝ) := by
  classical
  have he (i : R) : hA.isHermitian.eigenvalues i ≤ A.trace := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hd : (A.trace • (1 : Matrix R R ℝ) -
      Matrix.diagonal hA.isHermitian.eigenvalues).PosSemidef := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub]
    exact Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (he i))
  let U : Matrix R R ℝ := hA.isHermitian.eigenvectorUnitary
  have hu : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hs : A = U * Matrix.diagonal hA.isHermitian.eigenvalues * Uᴴ := by
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, U] using hA.isHermitian.spectral_theorem
  have hc := hd.conjTranspose_mul_mul_same Uᴴ
  have hc' : (A.trace • (1 : Matrix R R ℝ) -
      U * Matrix.diagonal hA.isHermitian.eigenvalues * Uᴴ).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose, mul_sub, sub_mul,
      mul_smul_comm, smul_mul_assoc, mul_one, hu] using hc
  rwa [← hs] at hc'

end PerfectMatchingPSD

end OAI

-- ---- platform node ----
open OAI OAI.PerfectMatchingPSD
open Matrix
open scoped MatrixOrder Matrix.Norms.Frobenius


theorem solution : type_of% @_root_.OAI.PerfectMatchingPSD.posSemidef_le_trace := @_root_.OAI.PerfectMatchingPSD.posSemidef_le_trace
