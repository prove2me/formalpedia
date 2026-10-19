-- Prove2me | solution 1 for OAI.Saxl.strip_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:32:45.236387+00:00
-- url     : https://prove2.me/submissions/7dcc69e5-a866-4a40-9209-4d25e9f92aad

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/StripReduction.lean:L139-L161
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.strip_reduction. The node keeps its source
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
import Definitions.Def_OAI_RepresentationTheory_Saxl_YoungRule
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_RepeatedProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseSign
import Definitions.Def_OAI_RepresentationTheory_Saxl_DominatedQuotient
import Definitions.Def_OAI_RepresentationTheory_Saxl_DominatedSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripReduction
import Theorems.Thm_OAI_Saxl_stripRemove_horizontal

-- ---- from OAI.RepresentationTheory.Saxl.Basic ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV uW

namespace Saxl

/- The genuine finite-dimensional Hom criterion; no simplicity hypothesis. -/
/- Column permutations cannot also fix the row word unless they are identity. -/
/- The coefficient of the canonical row word in its polytabloid is one. -/
theorem staircase_cells_succ (m : ℕ) :
    (staircase (m + 1)).cells = (staircase m).cells ∪ Finset.HasAntidiagonal.antidiagonal m := by
  ext x
  rcases x with ⟨i, j⟩
  simp only [YoungDiagram.mem_cells, mem_staircase, Finset.mem_union,
    Finset.HasAntidiagonal.mem_antidiagonal]
  omega

theorem staircase_card_succ (m : ℕ) :
    (staircase (m + 1)).card = (staircase m).card + (m + 1) := by
  change (staircase (m + 1)).cells.card = _
  rw [staircase_cells_succ, Finset.card_union_of_disjoint]
  · rw [Finset.Nat.card_antidiagonal]
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases x with ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, mem_staircase] at hx
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hy
    omega

theorem staircase_card_double (m : ℕ) :
    (staircase m).card * 2 = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [staircase_card_succ]
    nlinarith

/- The staircase has triangular cardinality. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.HorizontalRemoval ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.StripReduction ----
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
lemma stripRemove_full_prefix (μ : YoungDiagram) (q : ℕ) :
    rowPrefix (stripRemove μ (μ.rowLen 0)) q + μ.rowLen 0 = rowPrefix μ (q+1) := by
  have hh := stripRemove_prefix μ (μ.rowLen 0) q
  rw [min_self, min_eq_right (μ.rowLen_anti 0 q (Nat.zero_le _))] at hh
  exact hh.trans (rowPrefix_succ μ q).symm

/- Sweeps remove any prescribed number within the first q-row capacity. -/
theorem stripChain_of_capacity (q t : ℕ) (μ : YoungDiagram)
    (ht : t ≤ rowPrefix μ q) :
    ∃ k ≤ q, ∃ ν, ν.card + t = μ.card ∧ StripChain k ν μ := by
  induction q generalizing t μ with
  | zero =>
    have hz : t = 0 := by simpa [rowPrefix] using ht
    exact ⟨0, le_rfl, μ, by omega, StripChain.nil μ⟩
  | succ q ih =>
    by_cases hz : t = 0
    · exact ⟨0, Nat.zero_le _, μ, by omega, StripChain.nil μ⟩
    by_cases hb : t ≤ μ.rowLen 0
    · let ν := stripRemove μ t
      have hc : ν.card + t = μ.card := by
        simpa only [ν, min_eq_left hb] using stripRemove_card μ t
      have hn : ν ≠ μ := by intro he; rw [he] at hc; omega
      exact ⟨1, by omega, ν, hc,
        StripChain.snoc (StripChain.nil ν) (stripRemove_horizontal μ t) hn⟩
    · let η := stripRemove μ (μ.rowLen 0)
      have hp : rowPrefix η q + μ.rowLen 0 = rowPrefix μ (q+1) :=
        stripRemove_full_prefix μ q
      have hcap : t - μ.rowLen 0 ≤ rowPrefix η q := by omega
      obtain ⟨k, hk, ν, hc, hchain⟩ := ih (t-μ.rowLen 0) η hcap
      have hec : η.card + μ.rowLen 0 = μ.card := by
        simpa only [η, min_self] using stripRemove_card μ (μ.rowLen 0)
      have hpos : 0 < μ.rowLen 0 := by
        by_contra h
        have hz0 : μ.rowLen 0 = 0 := by omega
        have hp0 : rowPrefix μ (q+1) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hh := μ.rowLen_anti 0 i (Nat.zero_le _)
          omega
        omega
      have hn : η ≠ μ := by intro he; rw [he] at hec; omega
      refine ⟨k+1, by omega, ν, ?_, StripChain.snoc hchain (stripRemove_horizontal μ _) hn⟩
      omega

lemma rowPrefix_mean (μ : YoungDiagram) {q k : ℕ} (hqk : q ≤ k) :
    q * rowPrefix μ k ≤ k * rowPrefix μ q := by
  have hlow : q * μ.rowLen q ≤ rowPrefix μ q := by
    calc
      q * μ.rowLen q = ∑ i ∈ Finset.range q, μ.rowLen q := by simp
      _ ≤ rowPrefix μ q := Finset.sum_le_sum (fun i hi =>
        μ.rowLen_anti i q (Nat.le_of_lt (Finset.mem_range.mp hi)))
  have he : rowPrefix μ k = rowPrefix μ q +
      ∑ i ∈ Finset.range (k-q), μ.rowLen (q+i) := by
    simp only [rowPrefix]
    rw [← Finset.sum_range_add]
    congr 2
    omega
  have htail : (∑ i ∈ Finset.range (k-q), μ.rowLen (q+i)) ≤ (k-q)*μ.rowLen q := by
    calc
      _ ≤ ∑ i ∈ Finset.range (k-q), μ.rowLen q :=
        Finset.sum_le_sum (fun i hi => μ.rowLen_anti q (q+i) (by omega))
      _ = _ := by simp
  have hm := Nat.mul_le_mul_left (k-q) hlow
  have hs := Nat.mul_le_mul_left q htail
  rw [he]
  have hsum : q + (k-q) = k := by omega
  nlinarith

lemma staircase_prefix_double (m k : ℕ) (hk : k ≤ m) :
    2 * rowPrefix (staircase m) k = k * (2*m+1-k) := by
  induction k with
  | zero => simp [rowPrefix]
  | succ k ih =>
    rw [rowPrefix_succ, staircase_rowLen]
    have hi := ih (by omega)
    have hs : k + (m-k) = m := by omega
    have ht : k + (2*m+1-k) = 2*m+1 := by omega
    have ht' : (k+1) + (2*m+1-(k+1)) = 2*m+1 := by omega
    nlinarith

/- The exact capacity alternative used by the main induction. -/
lemma strip_reduction_capacity (m : ℕ) (hm : 2 ≤ m) (μ : YoungDiagram)
    (hμ : μ.card = (staircase m).card) (hdom : ¬ Dominates (staircase m) μ)
    (hfirst : μ.rowLen 0 < m) : 5 ≤ m ∧ 2*m-1 ≤ rowPrefix μ 4 := by
  obtain ⟨k, hk⟩ : ∃ k, rowPrefix (staircase m) k < rowPrefix μ k := by
    simpa only [Dominates, not_forall, not_le] using hdom
  have hkm : k < m := by
    by_contra hh
    have hc : (staircase m).colLen 0 ≤ k := by simp; omega
    rw [rowPrefix_eq_card _ hc] at hk
    have hle := rowPrefix_le_card μ k
    omega
  have hbound : rowPrefix μ k ≤ k * (m-1) := by
    calc
      _ ≤ ∑ i ∈ Finset.range k, (m-1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hh := μ.rowLen_anti 0 i (Nat.zero_le _)
        omega
      _ = _ := by simp
  have hstair := staircase_prefix_double m k (by omega)
  have hk4 : 4 ≤ k := by
    have hm1 : m = (m-1)+1 := by omega
    by_contra hh
    interval_cases k <;> omega
  have hmean := rowPrefix_mean μ hk4
  have hpos : 0 < k := by omega
  have hsum : k + (2*m+1-k) = 2*m+1 := by omega
  constructor
  · omega
  · have ha : 4*(2*m+1-k) < 2*rowPrefix μ 4 := by
      nlinarith
    have hb : 2*m-1 ≤ 2*(2*m+1-k) := by omega
    omega

theorem strip_reduction (m : ℕ) (hm : 2 ≤ m) (μ : YoungDiagram)
    (hμ : μ.card = (staircase m).card) (hdom : ¬ Dominates (staircase m) μ) :
    (∃ ν, ν.card = (staircase (m-1)).card ∧ HorizontalStrip ν μ) ∨
    (5 ≤ m ∧ ∃ q ≤ 4, ∃ ν, ν.card = (staircase (m-2)).card ∧ StripChain q ν μ) := by
  by_cases hfirst : m ≤ μ.rowLen 0
  · left
    let ν := stripRemove μ m
    have hc : ν.card + m = μ.card := by
      simpa only [ν, min_eq_left hfirst] using stripRemove_card μ m
    have hs : (staircase m).card = (staircase (m-1)).card + m := by
      have hh := staircase_card_succ (m-1)
      have he : m-1+1 = m := by omega
      simpa only [he] using hh
    exact ⟨ν, by omega, stripRemove_horizontal μ m⟩
  · right
    obtain ⟨hm5, hcap⟩ := strip_reduction_capacity m hm μ hμ hdom (by omega)
    obtain ⟨q, hq, ν, hc, hs⟩ := stripChain_of_capacity 4 (2*m-1) μ hcap
    refine ⟨hm5, q, hq, ν, ?_, hs⟩
    have hc₁ := staircase_card_double m
    have hc₂ := staircase_card_double (m-2)
    have hh : m = (m-2)+2 := by omega
    have ht : 2*m-1+1 = 2*m := by omega
    nlinarith

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.strip_reduction := @_root_.OAI.Saxl.strip_reduction
