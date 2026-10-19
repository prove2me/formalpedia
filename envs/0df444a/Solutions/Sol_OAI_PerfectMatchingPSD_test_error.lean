-- Prove2me | solution 1 for OAI.PerfectMatchingPSD.test_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:51:08.238788+00:00
-- url     : https://prove2.me/submissions/ddadb409-7615-431f-97ae-9b391c34cc80

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/SquareRootDisturbance.lean:L51-L71
-- (upload_full_project.md Phase 4): solution for node OAI.PerfectMatchingPSD.test_error. The node keeps its source
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

-- ---- from OAI.Combinatorics.MatchingPSD.DeterminantNormalization ----
namespace OAI

universe u_1 u_2 u_3

namespace PerfectMatchingPSD
open Matrix Set
variable {R : Type u_1} {I : Type u_2} {J : Type u_3} [Fintype R] [DecidableEq R]

open scoped MatrixOrder

lemma trace_mul_nonneg {A B : Matrix R R ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  let G := CFC.sqrt B
  have hG : G.PosSemidef := (CFC.sqrt_nonneg B).posSemidef
  have hGG : G * G = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have h := (hA.conjTranspose_mul_mul_same G).trace_nonneg
  rw [hG.isHermitian.eq, Matrix.trace_mul_cycle, hGG] at h
  simpa only [Matrix.trace_mul_comm B A] using h

lemma trace_mul_le_of_le {A B D : Matrix R R ℝ} (hA : A.PosSemidef) (hBD : B ≤ D) :
    (A * B).trace ≤ (A * D).trace := by
  have h := trace_mul_nonneg hA hBD
  rwa [mul_sub, Matrix.trace_sub, sub_nonneg] at h

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.SquareRootDisturbance ----
namespace OAI

universe u_1

namespace PerfectMatchingPSD
open Matrix
open scoped MatrixOrder Matrix.Norms.Frobenius
variable {R : Type u_1} [Fintype R] [DecidableEq R]

lemma frobenius_sq (A : Matrix R R ℝ) :
    ‖A‖^2 = ∑ i, ∑ j, (A i j)^2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
  · simp
  · positivity

lemma frobenius_sq_trace (A : Matrix R R ℝ) : ‖A‖^2 = (Aᵀ * A).trace := by
  rw [frobenius_sq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, ← pow_two]
  exact Finset.sum_comm

lemma square_le_self {A : Matrix R R ℝ} (hA : 0 ≤ A) (hA₁ : A ≤ 1) : A^2 ≤ A := by
  have hc : Commute A (1-A) := (Commute.one_right A).sub_right (Commute.refl A)
  have hh := Commute.mul_nonneg hA (sub_nonneg.mpr hA₁) hc
  simpa only [mul_sub, mul_one, ← pow_two, sub_nonneg] using hh

lemma one_sub_square_le {A : Matrix R R ℝ} (hA : 0 ≤ A) (hA₁ : A ≤ 1) :
    (1-A)^2 ≤ 1-A := square_le_self (sub_nonneg.mpr hA₁) (by simpa using hA)

lemma test_error {ρ F : Matrix R R ℝ} (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1)
    (hF : 0 ≤ F) (hF₁ : F ≤ 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hs : 1-ε ≤ (ρ*F).trace) :
    ‖(F-1)*CFC.sqrt ρ‖ ≤ Real.sqrt ε := by
  let G := CFC.sqrt ρ
  have hG : G.PosSemidef := (CFC.sqrt_nonneg ρ).posSemidef
  have hGG : G*G = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have he : ((F-1)*G)ᵀ * ((F-1)*G) = G*(1-F)^2*G := by
    have hFt : Fᵀ = F := hF.posSemidef.isHermitian.eq
    have hGt : Gᵀ = G := hG.isHermitian.eq
    rw [Matrix.transpose_mul, Matrix.transpose_sub, hFt, Matrix.transpose_one, hGt]
    noncomm_ring
  have hb := trace_mul_le_of_le hρ (one_sub_square_le hF hF₁)
  have hnorm : ‖(F-1)*G‖^2 ≤ ε := by
    rw [frobenius_sq_trace, he, Matrix.trace_mul_cycle, hGG]
    have hc : (ρ*(1-F)).trace = 1-(ρ*F).trace := by
      rw [mul_sub, mul_one, Matrix.trace_sub, htρ]
    rw [hc] at hb
    linarith
  change ‖(F-1)*G‖ ≤ Real.sqrt ε
  nlinarith [Real.sq_sqrt hε, Real.sqrt_nonneg ε, norm_nonneg ((F-1)*G)]

end PerfectMatchingPSD

end OAI

-- ---- platform node ----
open OAI OAI.PerfectMatchingPSD
open Matrix
open scoped MatrixOrder Matrix.Norms.Frobenius


theorem solution : type_of% @_root_.OAI.PerfectMatchingPSD.test_error := @_root_.OAI.PerfectMatchingPSD.test_error
