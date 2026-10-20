-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Pruning.exists_pruning_rank_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:17:50.897992+00:00
-- url     : https://prove2.me/submissions/91ca8822-7eb1-4a05-98f5-8d25e1bfd462

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/GenericRankSelection.lean:L35-L75
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Pruning.exists_pruning_rank_coefficients. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_PruningDefinitions
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Matching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_AugmentedGraph
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatchingAugmented
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankMatching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRank
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMaps
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelRestriction
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MaxSupportKernel
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelConflict
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankCoefficients
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMapsPolynomial
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankGlobalMinors
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Bipartite_exists_vertexCover_card_eq_of_isMaximumMatching
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_det_matrixLMatchingMinor_ne_zero
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_det_matrixNTransposeMatchingMinor_ne_zero
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_exists_coefficients_localMaximalRanks
import Theorems.Thm_OAI_SeymourSecondNeighborhood_rank_le_vertexCover_card

-- ---- from OAI.Combinatorics.SecondNeighborhood.GenericRankFamily ----
namespace OAI

namespace SeymourSecondNeighborhood

open Bipartite

theorem rank_le_card_of_maximum_matching
    {I J K : Type*} [Fintype I] [Fintype J] [Field K]
    {support : I → J → Prop} {matching : Finset (I × J)}
    (hmatching : IsMaximumMatching support matching) (D : Matrix I J K)
    (hD : ∀ i j, ¬ support i j → D i j = 0) : D.rank ≤ matching.card := by
  classical
  obtain ⟨rows, cols, hcover, hcard, _, _⟩ :=
    exists_vertexCover_card_eq_of_isMaximumMatching hmatching
  rw [← hcard]
  apply rank_le_vertexCover_card
  intro i j hij
  apply hcover i j
  by_contra hs
  exact hij (hD i j hs)

theorem rank_eq_card_of_maximum_matching_minor
    {I J K : Type*} [Fintype I] [Fintype J] [Field K]
    {support : I → J → Prop} {matching : Finset (I × J)}
    [DecidableEq ↥matching]
    (hmatching : IsMaximumMatching support matching) (D : Matrix I J K)
    (hD : ∀ i j, ¬ support i j → D i j = 0)
    (hdet : (D.submatrix (fun e : ↥matching => e.1.1)
      (fun e : ↥matching => e.1.2)).det ≠ 0) : D.rank = matching.card := by
  apply le_antisymm (rank_le_card_of_maximum_matching hmatching D hD)
  calc
    matching.card = (D.submatrix (fun e : ↥matching => e.1.1)
        (fun e : ↥matching => e.1.2)).rank := by
      simpa only [Fintype.card_coe] using (Matrix.rank_of_det_ne_zero hdet).symm
    _ ≤ D.rank := Matrix.rank_submatrix_le _ _ _

variable {σ κ τ K : Type*} [Field K] [Infinite K] [Fintype κ] [Fintype τ]
variable {I J : κ → Type*} [∀ k, Fintype (I k)] [∀ k, Fintype (J k)]

end SeymourSecondNeighborhood

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.GenericRankSelection ----
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Bipartite
open scoped Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem matrixL_supported_on_matchingSupport (r : X → X → Prop)
    (R C : Finset (X × X)) (v : CoefficientVariables X → ℝ) :
    ∀ z left, ¬ matrixLSupport r R C z left →
      matrixL r R C (selectedA r v) z left = 0 := by
  classical
  intro z left hs
  by_cases hc : z.1.2 = left.1.2
  · have hr : ¬ r left.1.1 z.1.1 := fun hr => hs ⟨hc, hr⟩
    simp [matrixL, selectedA, hc, hr]
  · simp [matrixL, hc]

theorem matrixNTranspose_supported_on_matchingSupport (r : X → X → Prop)
    (R C : Finset (X × X)) (v : CoefficientVariables X → ℝ) :
    ∀ z right, ¬ matrixNTransposeSupport r R C z right →
      (matrixN r R C (selectedB r v))ᵀ z right = 0 := by
  classical
  intro z right hs
  by_cases hc : right.1.1 = z.1.1
  · have hr : ¬ r right.1.2 z.1.2 := fun hr => hs ⟨hc, hr⟩
    simp [Matrix.transpose_apply, matrixN, selectedB, hc, hr]
  · simp [Matrix.transpose_apply, matrixN, hc]

theorem exists_pruning_rank_coefficients
    (r : X → X → Prop) (R C : Finset (X × X))
    (α : Finset (↥(Z r R C) × ↥R)) (β : Finset (↥(Z r R C) × ↥C))
    (hα : IsMaximumMatching (matrixLSupport r R C) α)
    (hβ : IsMaximumMatching (matrixNTransposeSupport r R C) β) :
    ∃ v : CoefficientVariables X → ℝ,
      SupportedCoefficients r (selectedA r v) ∧
      SupportedCoefficients r (selectedB r v) ∧
      LocalMaximalRanks r R C (selectedB r v) ∧
      ((matrixL r R C (selectedA r v)).submatrix
        (fun e : ↥α => e.1.1) (fun e : ↥α => e.1.2)).det ≠ 0 ∧
      (((matrixN r R C (selectedB r v))ᵀ).submatrix
        (fun e : ↥β => e.1.1) (fun e : ↥β => e.1.2)).det ≠ 0 ∧
      (matrixL r R C (selectedA r v)).rank = α.card ∧
      ((matrixN r R C (selectedB r v))ᵀ).rank = β.card := by
  classical
  let extra : Bool → MvPolynomial (CoefficientVariables X) ℝ := fun t =>
    if t then (matrixLMatchingMinor r R C α).det
    else (matrixNTransposeMatchingMinor r R C β).det
  have hextra : ∀ t, extra t ≠ 0 := by
    intro t
    cases t with
    | false => exact det_matrixNTransposeMatchingMinor_ne_zero r R C β hβ.1
    | true => exact det_matrixLMatchingMinor_ne_zero r R C α hα.1
  obtain ⟨v, hv, ha, hb, hlocal⟩ :=
    exists_coefficients_localMaximalRanks r R C extra hextra
  have hdetL : ((matrixL r R C (selectedA r v)).submatrix
      (fun e : ↥α => e.1.1) (fun e : ↥α => e.1.2)).det ≠ 0 := by
    have h := hv true
    change MvPolynomial.eval v (matrixLMatchingMinor r R C α).det ≠ 0 at h
    simpa only [← det_evalPolynomialMatrix, eval_matrixLMatchingMinor] using h
  have hdetN : (((matrixN r R C (selectedB r v))ᵀ).submatrix
      (fun e : ↥β => e.1.1) (fun e : ↥β => e.1.2)).det ≠ 0 := by
    have h := hv false
    change MvPolynomial.eval v (matrixNTransposeMatchingMinor r R C β).det ≠ 0 at h
    simpa only [← det_evalPolynomialMatrix, eval_matrixNTransposeMatchingMinor] using h
  refine ⟨v, ha, hb, hlocal, hdetL, hdetN, ?_, ?_⟩
  · exact rank_eq_card_of_maximum_matching_minor hα _
      (matrixL_supported_on_matchingSupport r R C v) hdetL
  · exact rank_eq_card_of_maximum_matching_minor hβ _
      (matrixNTranspose_supported_on_matchingSupport r R C v) hdetN

end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
open Bipartite
open scoped Matrix


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Pruning.exists_pruning_rank_coefficients := @_root_.OAI.SeymourSecondNeighborhood.Pruning.exists_pruning_rank_coefficients
