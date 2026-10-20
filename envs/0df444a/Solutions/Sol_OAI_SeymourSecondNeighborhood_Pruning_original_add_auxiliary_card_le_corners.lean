-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Pruning.original_add_auxiliary_card_le_corners
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:21:02.693188+00:00
-- url     : https://prove2.me/submissions/47655f53-b8eb-4d35-9826-3e14a6263e6a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/RankBoundFromMinors.lean:L13-L42
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Pruning.original_add_auxiliary_card_le_corners. The node keeps its source
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
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_card_add_rank_matrixL_add_rank_matrixN_le_card_Z_add_card_H_of_lifts
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_exists_pruning_rank_coefficients

-- ---- from OAI.Combinatorics.SecondNeighborhood.GenericRankColumns ----
namespace OAI

namespace SeymourSecondNeighborhood

open scoped Matrix

variable {I J K κ : Type*} [Fintype I] [Fintype J] [Field K]
variable [Fintype κ] [DecidableEq κ]

omit [Fintype I] [Fintype J] in
theorem selectedColumns_linearIndependent_of_det_ne_zero
    (M : Matrix I J K) (r : κ → I) (c : κ → J)
    (hdet : (M.submatrix r c).det ≠ 0) :
    LinearIndependent K (M.submatrix id c).col := by
  apply LinearIndependent.of_comp (LinearMap.funLeft K K r)
  change LinearIndependent K (M.submatrix r c).col
  exact Matrix.linearIndependent_cols_of_det_ne_zero hdet

theorem selectedColumns_span_eq_of_det_ne_zero
    (M : Matrix I J K) (r : κ → I) (c : κ → J)
    (hdet : (M.submatrix r c).det ≠ 0) (hrank : M.rank ≤ Fintype.card κ) :
    Submodule.span K (Set.range (M.submatrix id c).col) =
      Submodule.span K (Set.range M.col) := by
  apply Submodule.eq_of_le_of_finrank_le
  · apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨c j, rfl⟩
  · calc
      Module.finrank K (Submodule.span K (Set.range M.col)) = M.rank :=
        (Matrix.rank_eq_finrank_span_cols M).symm
      _ ≤ Fintype.card κ := hrank
      _ = Module.finrank K (Submodule.span K (Set.range (M.submatrix id c).col)) :=
        (finrank_span_eq_card
          (selectedColumns_linearIndependent_of_det_ne_zero M r c hdet)).symm

theorem selectedColumns_range_eq_of_det_ne_zero
    (M : Matrix I J K) (r : κ → I) (c : κ → J)
    (hdet : (M.submatrix r c).det ≠ 0) (hrank : M.rank ≤ Fintype.card κ) :
    LinearMap.range (M.submatrix id c).mulVecLin = LinearMap.range M.mulVecLin := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  exact selectedColumns_span_eq_of_det_ne_zero M r c hdet hrank

theorem exists_selectedColumns_mulVec
    (M : Matrix I J K) (r : κ → I) (c : κ → J)
    (hdet : (M.submatrix r c).det ≠ 0) (hrank : M.rank ≤ Fintype.card κ)
    (x : J → K) :
    ∃ y : κ → K, M *ᵥ x = (M.submatrix id c) *ᵥ y := by
  have hx : M *ᵥ x ∈ LinearMap.range M.mulVecLin := ⟨x, rfl⟩
  rw [← selectedColumns_range_eq_of_det_ne_zero M r c hdet hrank] at hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy.symm⟩

end SeymourSecondNeighborhood

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.KernelBasisLifts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open scoped BigOperators Matrix

variable {I J F κ E : Type*}
variable [Fintype J] [Fintype κ] [DecidableEq J] [Field F]

omit [Fintype J] in
theorem extendSelected_apply_of_ne (col : κ → J) (y : κ → F) (j : J)
    (hj : ∀ k, j ≠ col k) : extendSelected col y j = 0 := by
  simp only [extendSelected, Finset.sum_apply]
  exact Finset.sum_eq_zero fun k _ =>
    Pi.single_eq_of_ne (M := fun _ : J => F) (hj k) (y k)

theorem mulVec_extendSelected (M : Matrix I J F) (col : κ → J) (y : κ → F) :
    M *ᵥ extendSelected col y = (M.submatrix id col) *ᵥ y := by
  funext i
  change (M i) ⬝ᵥ (∑ k, Pi.single (col k) (y k)) =
    ∑ k, M i (col k) * y k
  simp only [dotProduct_sum, dotProduct_single]

theorem liftCoefficients_spec (M : Matrix I J F) (col : κ → J)
    (cover : ∀ x : J → F, ∃ y : κ → F,
      M *ᵥ x = (M.submatrix id col) *ᵥ y) (j : J) :
    M *ᵥ Pi.single j 1 = (M.submatrix id col) *ᵥ liftCoefficients M col cover j :=
  Classical.choose_spec (cover (Pi.single j 1))

theorem mulVec_kernelLift (M : Matrix I J F) (col : κ → J)
    (cover : ∀ x : J → F, ∃ y : κ → F,
      M *ᵥ x = (M.submatrix id col) *ᵥ y) (j : J) :
    M *ᵥ kernelLift M col cover j = 0 := by
  rw [kernelLift, Matrix.mulVec_sub, mulVec_extendSelected,
    liftCoefficients_spec M col cover j, sub_self]

theorem kernelLift_apply_of_ne (M : Matrix I J F) (col : κ → J)
    (cover : ∀ x : J → F, ∃ y : κ → F,
      M *ᵥ x = (M.submatrix id col) *ᵥ y) (j j' : J)
    (hj' : ∀ k, j' ≠ col k) :
    kernelLift M col cover j j' = (Pi.single j 1 : J → F) j' := by
  change (Pi.single j 1 : J → F) j' -
    extendSelected col (liftCoefficients M col cover j) j' = _
  rw [extendSelected_apply_of_ne col _ j' hj', sub_zero]

theorem kernelLift_normalized [DecidableEq E]
    (M : Matrix I J F) (col : κ → J)
    (cover : ∀ x : J → F, ∃ y : κ → F,
      M *ᵥ x = (M.submatrix id col) *ᵥ y)
    (left : E → J) (hleft : Function.Injective left)
    (hdisjoint : ∀ e k, left e ≠ col k) (e f : E) :
    kernelLift M col cover (left e) (left f) = if e = f then 1 else 0 := by
  rw [kernelLift_apply_of_ne M col cover (left e) (left f) (hdisjoint f)]
  by_cases h : e = f
  · subst f
    simp
  · have hcoord : left f ≠ left e := fun hcoord => h (hleft hcoord).symm
    rw [Pi.single_eq_of_ne hcoord, ite_eq_right h]

theorem exists_normalized_kernelLifts [DecidableEq E]
    (M : Matrix I J F) (col : κ → J)
    (cover : ∀ x : J → F, ∃ y : κ → F,
      M *ᵥ x = (M.submatrix id col) *ᵥ y)
    (left : E → J) (hleft : Function.Injective left)
    (hdisjoint : ∀ e k, left e ≠ col k) :
    ∃ U : E → J → F, (∀ e, M *ᵥ U e = 0) ∧
      (∀ e f, U e (left f) = if e = f then 1 else 0) := by
  refine ⟨fun e => kernelLift M col cover (left e), ?_, ?_⟩
  · intro e
    exact mulVec_kernelLift M col cover (left e)
  · intro e f
    exact kernelLift_normalized M col cover left hleft hdisjoint e f

theorem exists_normalized_kernelLifts_of_det_ne_zero
    [Fintype I] [DecidableEq κ] [DecidableEq E]
    (M : Matrix I J F) (row : κ → I) (col : κ → J)
    (hdet : (M.submatrix row col).det ≠ 0) (hrank : M.rank ≤ Fintype.card κ)
    (left : E → J) (hleft : Function.Injective left)
    (hdisjoint : ∀ e k, left e ≠ col k) :
    ∃ U : E → J → F, (∀ e, M *ᵥ U e = 0) ∧
      (∀ e f, U e (left f) = if e = f then 1 else 0) := by
  exact exists_normalized_kernelLifts M col
    (fun x => exists_selectedColumns_mulVec M row col hdet hrank x)
    left hleft hdisjoint

end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.RankBoundFromMinors ----
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open scoped Matrix

variable {X E : Type*} [Fintype X] [DecidableEq X] [Fintype E]

theorem original_add_auxiliary_card_le_corners
    (r : X → X → Prop) (R C : Finset (X × X))
    (α : Finset (↥(Z r R C) × ↥R)) (β : Finset (↥(Z r R C) × ↥C))
    (hα : Bipartite.IsMaximumMatching (matrixLSupport r R C) α)
    (hβ : Bipartite.IsMaximumMatching (matrixNTransposeSupport r R C) β)
    (left : E → ↥R) (right : E → ↥C)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hleft_disjoint : ∀ e (f : ↥α), left e ≠ f.1.2)
    (hright_disjoint : ∀ e (f : ↥β), right e ≠ f.1.2)
    (hconflict : ∀ e, Conflict r (left e).1 (right e).1) :
    Fintype.card E + α.card + β.card ≤ (Z r R C).card + (H r R C).card := by
  classical
  obtain ⟨v, ha, hb, hmax, hdetL, hdetN, hrankL, hrankN⟩ :=
    exists_pruning_rank_coefficients r R C α β hα hβ
  have hupperL : (matrixL r R C (selectedA r v)).rank ≤ Fintype.card ↥α := by
    simpa only [Fintype.card_coe] using hrankL.le
  have hupperN : ((matrixN r R C (selectedB r v))ᵀ).rank ≤ Fintype.card ↥β := by
    simpa only [Fintype.card_coe] using hrankN.le
  obtain ⟨U, hU, hUcoordinate⟩ := exists_normalized_kernelLifts_of_det_ne_zero
    (matrixL r R C (selectedA r v)) (fun f : ↥α => f.1.1)
    (fun f : ↥α => f.1.2) hdetL hupperL left hleft hleft_disjoint
  obtain ⟨W, hW, hWcoordinate⟩ := exists_normalized_kernelLifts_of_det_ne_zero
    (matrixN r R C (selectedB r v))ᵀ (fun f : ↥β => f.1.1)
    (fun f : ↥β => f.1.2) hdetN hupperN right hright hright_disjoint
  have hbound := card_add_rank_matrixL_add_rank_matrixN_le_card_Z_add_card_H_of_lifts
    r R C (selectedA r v) (selectedB r v) ha hb hmax left right U W
    hU hW (fun e => by simpa using hWcoordinate e e) hUcoordinate hconflict
  have hrankN' : (matrixN r R C (selectedB r v)).rank = β.card := by
    simpa only [Matrix.rank_transpose] using hrankN
  simpa only [hrankL, hrankN'] using hbound

end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
open scoped Matrix


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Pruning.original_add_auxiliary_card_le_corners := @_root_.OAI.SeymourSecondNeighborhood.Pruning.original_add_auxiliary_card_le_corners
