-- Prove2me | solution 1 for OAI.PerfectMatchingPSD.cut_degree_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:18:36.240073+00:00
-- url     : https://prove2.me/submissions/72e550d1-ab34-4f53-b0bd-b526058648b7

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/FiniteFactorization.lean:L38-L51
-- (upload_full_project.md Phase 4): solution for node OAI.PerfectMatchingPSD.cut_degree_identity. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixInterpolation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GoodCells
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellDecoder

-- ---- from OAI.Combinatorics.MatchingPSD.FiniteFactorization ----
namespace OAI

universe u_1 u_2

namespace PerfectMatchingPSD

lemma endpoint_count {n : ℕ} (U : Finset (Fin n)) (M : PerfectMatching n) :
    (∑ e ∈ M.1, ((if e.1.1 ∈ U then 1 else 0) +
      (if e.1.2 ∈ U then 1 else 0) : ℕ)) = U.card := by
  classical
  have pair_count (e : Edge n) :
      (∑ v ∈ U, (if e.1.1 = v ∨ e.1.2 = v then 1 else 0 : ℕ)) =
        (if e.1.1 ∈ U then 1 else 0) + (if e.1.2 ∈ U then 1 else 0) := by
    have pointwise (v : Fin n) :
        (if e.1.1 = v ∨ e.1.2 = v then 1 else 0 : ℕ) =
          (if e.1.1 = v then 1 else 0) + (if e.1.2 = v then 1 else 0) := by
      have hne : e.1.1 ≠ e.1.2 := ne_of_lt e.2
      by_cases h₁ : e.1.1 = v <;> by_cases h₂ : e.1.2 = v <;> simp_all
    simp_rw [pointwise]
    simp [Finset.sum_add_distrib]
  calc
    _ = ∑ e ∈ M.1, ∑ v ∈ U,
        (if e.1.1 = v ∨ e.1.2 = v then 1 else 0 : ℕ) := by
      apply Finset.sum_congr rfl
      intro e _
      exact (pair_count e).symm
    _ = ∑ v ∈ U, ∑ e ∈ M.1,
        (if e.1.1 = v ∨ e.1.2 = v then 1 else 0 : ℕ) := Finset.sum_comm
    _ = ∑ v ∈ U, (M.1.filter fun e => e.1.1 = v ∨ e.1.2 = v).card := by
      simp only [Finset.sum_boole, Nat.cast_id]
    _ = U.card := by
      have hm : ∀ v : Fin n,
          (M.1.filter fun e => e.1.1 = v ∨ e.1.2 = v).card = 1 := M.2
      simp [hm]

lemma cut_degree_identity {n : ℕ} (U : Finset (Fin n)) (M : PerfectMatching n) :
    U.card = 2 * (M.1.filter fun e => e.1.1 ∈ U ∧ e.1.2 ∈ U).card +
      crossingCount U M := by
  classical
  rw [← endpoint_count U M]
  have term (e : Edge n) :
      ((if e.1.1 ∈ U then 1 else 0) + (if e.1.2 ∈ U then 1 else 0) : ℕ) =
        2 * (if e.1.1 ∈ U ∧ e.1.2 ∈ U then 1 else 0) +
          (if Crosses U e then 1 else 0) := by
    by_cases h₁ : e.1.1 ∈ U <;> by_cases h₂ : e.1.2 ∈ U <;>
      simp [h₁, h₂, Crosses]
  simp_rw [term]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_boole, Nat.cast_id, crossingCount]

end PerfectMatchingPSD

end OAI

-- ---- platform node ----
open OAI OAI.PerfectMatchingPSD


theorem solution : type_of% @_root_.OAI.PerfectMatchingPSD.cut_degree_identity := @_root_.OAI.PerfectMatchingPSD.cut_degree_identity
