-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Pruning.card_add_rank_matrixL_add_rank_matrixN_le_card_Z_add_card_H_of_lifts
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:20:07.574105+00:00
-- url     : https://prove2.me/submissions/b4d1bdd8-7ef7-4944-b95e-fc09612e9816

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/CompositeRankBound.lean:L60-L88
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Pruning.card_add_rank_matrixL_add_rank_matrixN_le_card_Z_add_card_H_of_lifts. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelBasisLifts
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_card_add_rank_matrixN_mul_matrixL_le_card_H_of_lifts

-- ---- from OAI.Combinatorics.SecondNeighborhood.CompositeRankBound ----
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Matrix
open scoped Classical

noncomputable section

theorem matrix_rank_add_rank_le_rank_mul_add_card
    {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (L : Matrix J I ℝ) (N : Matrix K J ℝ) :
    L.rank + N.rank ≤ (N * L).rank + Fintype.card J := by
  let S : Submodule ℝ (J → ℝ) := LinearMap.range L.mulVecLin
  let restricted : S →ₗ[ℝ] (K → ℝ) := N.mulVecLin.domRestrict S
  have hrange : LinearMap.range restricted = LinearMap.range (N * L).mulVecLin := by
    dsimp only [restricted]
    rw [LinearMap.range_domRestrict, Matrix.mulVecLin_mul, LinearMap.range_comp]
  have hkernel : Module.finrank ℝ (LinearMap.ker restricted) ≤
      Module.finrank ℝ (LinearMap.ker N.mulVecLin) := by
    rw [← Submodule.finrank_map_subtype_eq S (LinearMap.ker restricted)]
    change Module.finrank ℝ
      ((LinearMap.ker (N.mulVecLin.domRestrict S)).map S.subtype) ≤ _
    rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]
    exact Submodule.finrank_mono inf_le_right
  have hrestricted : (N * L).rank +
      Module.finrank ℝ (LinearMap.ker restricted) = L.rank := by
    change Module.finrank ℝ (LinearMap.range (N * L).mulVecLin) +
      Module.finrank ℝ (LinearMap.ker restricted) = Module.finrank ℝ S
    rw [← hrange]
    exact LinearMap.finrank_range_add_finrank_ker restricted
  have hfull : N.rank + Module.finrank ℝ (LinearMap.ker N.mulVecLin) =
      Fintype.card J := by
    simpa only [Matrix.rank, Module.finrank_pi] using
      LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  calc
    L.rank + N.rank =
        ((N * L).rank + Module.finrank ℝ (LinearMap.ker restricted)) + N.rank := by
      rw [hrestricted]
    _ ≤ ((N * L).rank + Module.finrank ℝ (LinearMap.ker N.mulVecLin)) + N.rank :=
      Nat.add_le_add_right (Nat.add_le_add_left hkernel _) _
    _ = (N * L).rank +
        (Module.finrank ℝ (LinearMap.ker N.mulVecLin) + N.rank) := Nat.add_assoc _ _ _
    _ = (N * L).rank + Fintype.card J := by
      rw [Nat.add_comm (Module.finrank ℝ (LinearMap.ker N.mulVecLin)) N.rank, hfull]

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem matrixL_rank_add_matrixN_rank_le_rank_composite_add_card_Z
    (r : X → X → Prop) (R C : Finset (X × X)) (a b : X → X → ℝ) :
    (matrixL r R C a).rank + (matrixN r R C b).rank ≤
      (matrixN r R C b * matrixL r R C a).rank + (Z r R C).card := by
  simpa only [Fintype.card_coe] using
    matrix_rank_add_rank_le_rank_mul_add_card (matrixL r R C a) (matrixN r R C b)

theorem card_add_rank_matrixL_add_rank_matrixN_le_card_Z_add_card_H_of_lifts
    {E : Type*} [Fintype E]
    (r : X → X → Prop) (R C : Finset (X × X)) (a b : X → X → ℝ)
    (ha : SupportedCoefficients r a) (hb : SupportedCoefficients r b)
    (hmax : LocalMaximalRanks r R C b)
    (left : E → ↥R) (right : E → ↥C)
    (U : E → (↥R → ℝ)) (W : E → (↥C → ℝ))
    (hU : ∀ e, matrixL r R C a *ᵥ U e = 0)
    (hW : ∀ e, (matrixN r R C b)ᵀ *ᵥ W e = 0)
    (hWcoordinate : ∀ e, W e (right e) = 1)
    (hUcoordinate : ∀ e f, U e (left f) = if e = f then 1 else 0)
    (hconflict : ∀ e, Conflict r (left e).val (right e).val) :
    Fintype.card E + (matrixL r R C a).rank + (matrixN r R C b).rank ≤
      (Z r R C).card + (H r R C).card := by
  have hcomposite := matrixL_rank_add_matrixN_rank_le_rank_composite_add_card_Z
    r R C a b
  have hkernel := card_add_rank_matrixN_mul_matrixL_le_card_H_of_lifts
    r R C a b ha hb hmax left right U W hU hW hWcoordinate hUcoordinate hconflict
  calc
    Fintype.card E + (matrixL r R C a).rank + (matrixN r R C b).rank =
        Fintype.card E + ((matrixL r R C a).rank + (matrixN r R C b).rank) :=
      Nat.add_assoc _ _ _
    _ ≤ Fintype.card E +
        ((matrixN r R C b * matrixL r R C a).rank + (Z r R C).card) :=
      Nat.add_le_add_left hcomposite _
    _ = (Fintype.card E + (matrixN r R C b * matrixL r R C a).rank) +
        (Z r R C).card := (Nat.add_assoc _ _ _).symm
    _ ≤ (H r R C).card + (Z r R C).card := Nat.add_le_add_right hkernel _
    _ = (Z r R C).card + (H r R C).card := Nat.add_comm _ _

end
end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
open Matrix
open scoped Classical


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Pruning.card_add_rank_matrixL_add_rank_matrixN_le_card_Z_add_card_H_of_lifts := @_root_.OAI.SeymourSecondNeighborhood.Pruning.card_add_rank_matrixL_add_rank_matrixN_le_card_Z_add_card_H_of_lifts
