-- Prove2me | solution 1 for OAI.Saxl.dominates_stripRemove_last
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:04:38.281497+00:00
-- url     : https://prove2.me/submissions/d74ccaa4-cad1-40fb-80b8-bebfc224c74a

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/HorizontalRemoval.lean:L179-L211
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.dominates_stripRemove_last. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension
import Definitions.Def_OAI_RepresentationTheory_Saxl_SizedStrips
import Definitions.Def_OAI_RepresentationTheory_Saxl_HorizontalRemoval

-- ---- from OAI.RepresentationTheory.Saxl.HorizontalRemoval ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
lemma rowLen_zero_of_height_le (μ : YoungDiagram) {i : ℕ} (hi : μ.colLen 0 ≤ i) :
    μ.rowLen i = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro h
  have hm := YoungDiagram.mem_iff_lt_rowLen.mpr h
  have hh := YoungDiagram.mem_iff_lt_colLen.mp hm
  omega

lemma rowPrefix_eq_card (μ : YoungDiagram) {k : ℕ} (hk : μ.colLen 0 ≤ k) :
    rowPrefix μ k = μ.card := by
  have he : μ.card = ∑ i : Fin (μ.colLen 0), μ.rowLen i := by
    have hh := Fintype.card_congr (rowCellEquiv μ)
    simpa using hh
  rw [he, Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono hk)
  intro i hik hin
  exact rowLen_zero_of_height_le μ (by simpa using hin)

/- Tallest-column bottom deletion, expressed by interlacing rows. -/
lemma stripRemove_le (μ : YoungDiagram) (t : ℕ) : stripRemove μ t ≤ μ := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

lemma stripRemove_prefix (μ : YoungDiagram) (t k : ℕ) :
    rowPrefix (stripRemove μ t) k + min t (μ.rowLen 0) =
      rowPrefix μ k + min t (μ.rowLen k) := by
  induction k with
  | zero => simp [rowPrefix]
  | succ k ih =>
    have hr : (stripRemove μ t).rowLen k + min t (μ.rowLen k) =
        μ.rowLen k + min t (μ.rowLen (k+1)) := by
      rw [stripRemove_rowLen]
      dsimp [stripRow]
      omega
    simp only [rowPrefix, Finset.sum_range_succ] at ih ⊢
    omega

lemma stripRemove_card (μ : YoungDiagram) (t : ℕ) :
    (stripRemove μ t).card + min t (μ.rowLen 0) = μ.card := by
  have hh := stripRemove_prefix μ t (μ.colLen 0)
  rw [rowPrefix_eq_card μ le_rfl, rowLen_zero_of_height_le μ le_rfl, min_zero, add_zero] at hh
  have ht : (stripRemove μ t).colLen 0 ≤ μ.colLen 0 := by
    by_contra h
    have hm : (μ.colLen 0, 0) ∈ stripRemove μ t := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have hh := YoungDiagram.mem_iff_lt_colLen.mp (stripRemove_le μ t hm)
    omega
  rwa [rowPrefix_eq_card _ ht] at hh

lemma rowPrefix_succ (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ (k+1) = rowPrefix μ k + μ.rowLen k := by
  simp [rowPrefix, Finset.sum_range_succ]

lemma rowPrefix_le_card (μ : YoungDiagram) (k : ℕ) : rowPrefix μ k ≤ μ.card := by
  rw [← rowPrefix_eq_card μ (Nat.le_max_left _ k)]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_max_right _ _))

lemma rowPrefix_mono (μ : YoungDiagram) {k l : ℕ} (h : k ≤ l) :
    rowPrefix μ k ≤ rowPrefix μ l :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

lemma rowTruncate_rowLen (μ : YoungDiagram) (k i : ℕ) :
    (rowTruncate μ k).rowLen i = if i < k then μ.rowLen i else 0 := by
  have hh : ∀ j, j < (rowTruncate μ k).rowLen i ↔ j < if i < k then μ.rowLen i else 0 := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_rowTruncate, YoungDiagram.mem_iff_lt_rowLen]
    split_ifs <;> simp_all
  have h₁ := hh ((rowTruncate μ k).rowLen i)
  have h₂ := hh (if i < k then μ.rowLen i else 0)
  omega

lemma rowTruncate_height (μ : YoungDiagram) (k : ℕ) : (rowTruncate μ k).colLen 0 ≤ k := by
  by_contra h
  have hm : (k,0) ∈ rowTruncate μ k := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  exact Nat.lt_irrefl k (mem_rowTruncate.mp hm).2

lemma rowTruncate_prefix (μ : YoungDiagram) (k q : ℕ) (hq : q ≤ k) :
    rowPrefix (rowTruncate μ k) q = rowPrefix μ q := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [rowTruncate_rowLen, ite_eq_left (lt_of_lt_of_le (Finset.mem_range.mp hi) hq)]

lemma rowTruncate_card (μ : YoungDiagram) (k : ℕ) :
    (rowTruncate μ k).card = rowPrefix μ k := by
  rw [← rowPrefix_eq_card _ (rowTruncate_height μ k), rowTruncate_prefix _ _ _ le_rfl]

lemma dominates_stripRemove_last (θ τ : YoungDiagram) (k : ℕ)
    (hh : θ.colLen 0 ≤ k+1) (hc : τ.card = θ.card) (hd : Dominates τ θ) :
    (stripRemove τ (θ.rowLen k)).card = (rowTruncate θ k).card ∧
      Dominates (stripRemove τ (θ.rowLen k)) (rowTruncate θ k) := by
  have hw : θ.rowLen k ≤ τ.rowLen 0 := by
    have hh := hd 1
    simp only [rowPrefix, Finset.sum_range_one] at hh
    exact (θ.rowLen_anti 0 k (Nat.zero_le _)).trans hh
  have hθ : (rowTruncate θ k).card + θ.rowLen k = θ.card := by
    rw [rowTruncate_card, ← rowPrefix_succ, rowPrefix_eq_card θ hh]
  have hτ : (stripRemove τ (θ.rowLen k)).card + θ.rowLen k = τ.card := by
    simpa only [min_eq_left hw] using stripRemove_card τ (θ.rowLen k)
  have hcard : (stripRemove τ (θ.rowLen k)).card = (rowTruncate θ k).card := by omega
  refine ⟨hcard, ?_⟩
  have hsmall (q : ℕ) (hq : q ≤ k) : rowPrefix θ q ≤ rowPrefix (stripRemove τ (θ.rowLen k)) q := by
    have he := stripRemove_prefix τ (θ.rowLen k) q
    rw [min_eq_left hw] at he
    by_cases hr : θ.rowLen k ≤ τ.rowLen q
    · rw [min_eq_left hr] at he
      have hh := hd q
      omega
    · rw [min_eq_right (by omega : τ.rowLen q ≤ θ.rowLen k)] at he
      have hsq := hd (q+1)
      rw [rowPrefix_succ, rowPrefix_succ] at hsq
      have ht := θ.rowLen_anti q k hq
      omega
  intro q
  by_cases hq : q ≤ k
  · rw [rowTruncate_prefix _ _ _ hq]
    exact hsmall q hq
  · have hle := rowPrefix_le_card (rowTruncate θ k) q
    rw [rowTruncate_card] at hle
    exact hle.trans ((hsmall k le_rfl).trans (rowPrefix_mono _ (by omega)))

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.dominates_stripRemove_last := @_root_.OAI.Saxl.dominates_stripRemove_last
