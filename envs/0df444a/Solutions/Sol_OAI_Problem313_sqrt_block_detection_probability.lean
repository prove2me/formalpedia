-- Prove2me | solution 1 for OAI.Problem313.sqrt_block_detection_probability
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:15:37.007856+00:00
-- url     : https://prove2.me/submissions/c48467ae-1fcf-4284-989c-53448a790310

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/GraphBlockCapture.lean:L127-L158
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.sqrt_block_detection_probability. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Theorems.Thm_OAI_Problem313_SupportCombinatorics_exists_small_positive_degree
import Theorems.Thm_OAI_Problem313_blockProbability_singleton_inter_ge
import Theorems.Thm_OAI_Problem313_block_filter_eq_vertex_filter
import Theorems.Thm_OAI_Problem313_sqrt_block_cutoff_budget
import Theorems.Thm_OAI_Problem313_sqrt_block_size_bounds
import Theorems.Thm_OAI_Problem313_support_vertices_card_le

-- ---- from OAI.Combinatorics.SharpThreshold.BlockIncidence ----
namespace OAI

noncomputable section

namespace Problem313

/-- The same capture identity with the disjointness predicate used for free edges. -/
theorem block_not_disjoint_filter_eq_vertex_filter {n : ℕ}
    (S : Finset (GraphEdge n)) (B : Finset (Fin n)) (u : Fin n)
    (h : B ∩ S.biUnion (fun e => e.val) = {u}) :
    S.filter (fun e => ¬Disjoint e.val B) =
      S.filter (fun e => u ∈ e.val) := by
  classical
  simpa only [Finset.not_disjoint_iff, Finset.Nonempty, Finset.mem_inter] using
    block_filter_eq_vertex_filter S B u h

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.BlockCounting ----
namespace OAI

universe u

noncomputable section

namespace Problem313

open Finset

variable {α : Type u} [DecidableEq α]

omit [DecidableEq α] in
theorem blockProbability_mono (U : Finset α) (m : ℕ)
    {P Q : Finset α → Prop}
    (hPQ : ∀ B ∈ U.powersetCard m, P B → Q B) :
    blockProbability U m P ≤ blockProbability U m Q := by
  classical
  unfold blockProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show (U.powersetCard m).filter P ⊆
      (U.powersetCard m).filter Q from by
    intro B hB
    obtain ⟨hB, hP⟩ := Finset.mem_filter.mp hB
    exact Finset.mem_filter.mpr ⟨hB, hPQ B hB hP⟩)

/-- Collision estimate reduced to a half yields the usual capture lower bound. -/
theorem blockProbability_singleton_inter_ge_half (U V : Finset α) {m : ℕ} {u : α}
    (hVU : V ⊆ U) (hu : u ∈ V) (hm : 2 ≤ m) (hmn : m ≤ U.card)
    (hcollision : ((V.card : ℝ) - 1) * ((m : ℝ) - 1) / ((U.card : ℝ) - 1) ≤ 1 / 2) :
    (m : ℝ) / (2 * U.card) ≤ blockProbability U m (fun B => B ∩ V = {u}) := by
  have hn : 0 ≤ (m : ℝ) / U.card := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  apply le_trans _ (blockProbability_singleton_inter_ge U V hVU hu hm hmn)
  calc
    (m : ℝ) / (2 * U.card) = ((m : ℝ) / U.card) * (1 / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hn

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.SupportDegreeGraph ----
namespace OAI

namespace Problem313

open Finset

lemma support_exists_small_positive_degree {n : ℕ} (S : Finset (GraphEdge n))
    (hS : S.Nonempty) :
    ∃ u ∈ S.biUnion (fun e => e.val),
      1 ≤ (S.filter (fun e => u ∈ e.val)).card ∧
      (S.filter (fun e => u ∈ e.val)).card ^ 2 ≤ 2 * S.card := by
  classical
  obtain ⟨u, hu, hpos, hsmall⟩ := SupportCombinatorics.exists_small_positive_degree
    (S := S.image Subtype.val) (by
      intro e he
      obtain ⟨f, hf, rfl⟩ := mem_image.mp he
      exact f.property) (hS.image Subtype.val)
  have hdeg : SupportCombinatorics.degree (S.image Subtype.val) u =
      (S.filter (fun e => u ∈ e.val)).card := by
    unfold SupportCombinatorics.degree
    rw [filter_image]
    exact card_image_of_injective _ Subtype.val_injective
  refine ⟨u, ?_, ?_, ?_⟩
  · simpa [SupportCombinatorics.vertices] using hu
  · simpa [hdeg] using hpos
  · simpa [hdeg, card_image_of_injective S Subtype.val_injective] using hsmall

lemma support_exists_degree_le_cutoff {n : ℕ} (S : Finset (GraphEdge n))
    (hS : S.Nonempty) {k : ℝ} (hk : 0 ≤ k)
    (hcard : (S.card : ℝ) ≤ k ^ 2 / 2) :
    ∃ u ∈ S.biUnion (fun e => e.val),
      1 ≤ (S.filter (fun e => u ∈ e.val)).card ∧
      ((S.filter (fun e => u ∈ e.val)).card : ℝ) ≤ k := by
  obtain ⟨u, hu, hpos, hsquare⟩ := support_exists_small_positive_degree S hS
  refine ⟨u, hu, hpos, ?_⟩
  have hsquare' : ((S.filter (fun e => u ∈ e.val)).card : ℝ)^2 ≤ 2 * S.card :=
    by exact_mod_cast hsquare
  nlinarith [Nat.cast_nonneg (α := ℝ) (S.filter (fun e => u ∈ e.val)).card]

end Problem313

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.GraphBlockCapture ----
namespace OAI

/-! The graph-combinatorial input to capture of low Fourier levels. -/

namespace Problem313

noncomputable section

/-- For a low-degree support, choose one positive-degree vertex whose isolation
by the random block guarantees detection. -/
theorem exists_vertex_singleton_implies_detection {n : ℕ}
    (S : Finset (GraphEdge n)) (hS : S.Nonempty) {k : ℝ}
    (hk : 0 ≤ k) (hcard : (S.card : ℝ) ≤ k ^ 2 / 2) :
    ∃ u ∈ S.biUnion (fun e => e.val), ∀ B : Finset (Fin n),
      B ∩ S.biUnion (fun e => e.val) = {u} → BlockDetects k S B := by
  classical
  obtain ⟨u, hu, hpos, hdeg⟩ := support_exists_degree_le_cutoff S hS hk hcard
  refine ⟨u, hu, ?_⟩
  intro B hB
  unfold BlockDetects
  rw [block_not_disjoint_filter_eq_vertex_filter S B u hB]
  exact ⟨hpos, hdeg⟩

/-- The support-vertex bound turns the random-block union-bound error into a
uniform error at most one half. -/
theorem support_singleton_error_le_half {n : ℕ}
    (S : Finset (GraphEdge n)) (k r : ℝ)
    (hcard : (S.card : ℝ) ≤ k ^ 2 / 2)
    (hr : 0 ≤ r) (hbudget : k ^ 2 * r ≤ 1 / 2) :
    (((S.biUnion (fun e => e.val)).card : ℝ) - 1) * r ≤ 1 / 2 := by
  have hv : ((S.biUnion (fun e => e.val)).card : ℝ) ≤ 2 * S.card := by
    exact_mod_cast support_vertices_card_le S
  have hvk : ((S.biUnion (fun e => e.val)).card : ℝ) - 1 ≤ k ^ 2 := by
    linarith
  exact (mul_le_mul_of_nonneg_right hvk hr).trans hbudget

/-- The biased Fourier cutoff for a square-root block never exceeds `log n`. -/
theorem sqrt_block_cutoff_le_log (n : ℕ) (sigma : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) (hsigma : 0 ≤ sigma) (hsigma1 : sigma ≤ 1 / 2) :
    0 ≤ sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64 ∧
      sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64 ≤ Real.log (n : ℝ) := by
  have hm := sqrt_block_size_bounds n hn ht
  have hmreal : (1 : ℝ) ≤ (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast (show 1 ≤ ⌊Real.sqrt (n : ℝ)⌋₊ by omega)
  have hlogm : 0 ≤ Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := Real.log_nonneg hmreal
  have hlogmn : Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ≤ Real.log (n : ℝ) := by
    apply Real.log_le_log (by linarith)
    exact_mod_cast hm.2.1
  have hprod := mul_le_mul_of_nonneg_right hsigma1 hlogm
  exact ⟨div_nonneg (mul_nonneg hsigma hlogm) (by norm_num), by linarith⟩

/-- Every nonempty support of degree at most `k²/2` is detected with probability
at least `m/(2*n)` by the square-root-sized random block. -/
theorem sqrt_block_detection_probability (n : ℕ) (sigma : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) (hsigma : 0 ≤ sigma) (hsigma1 : sigma ≤ 1 / 2)
    (S : Finset (GraphEdge n)) (hS : S.Nonempty)
    (hcard : (S.card : ℝ) ≤
      (sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2) :
    (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / (2 * n) ≤
      blockProbability (Finset.univ : Finset (Fin n)) ⌊Real.sqrt (n : ℝ)⌋₊
        (BlockDetects (sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) S) := by
  classical
  let m := ⌊Real.sqrt (n : ℝ)⌋₊
  let k := sigma * Real.log (m : ℝ) / 64
  have hm := sqrt_block_size_bounds n hn ht
  have hk := sqrt_block_cutoff_le_log n sigma hn ht hsigma hsigma1
  obtain ⟨u, hu, hdetect⟩ := exists_vertex_singleton_implies_detection S hS hk.1 hcard
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmreal : (3 : ℝ) ≤ m := by exact_mod_cast hm.1
  have hr : 0 ≤ ((m : ℝ) - 1) / ((n : ℝ) - 1) :=
    div_nonneg (by linarith) (by linarith)
  have hcollision := support_singleton_error_le_half S k
    (((m : ℝ) - 1) / ((n : ℝ) - 1)) hcard hr
    (sqrt_block_cutoff_budget n sigma hn ht hsigma hsigma1)
  have hsingle := blockProbability_singleton_inter_ge_half
    (Finset.univ : Finset (Fin n)) (S.biUnion (fun e => e.val))
    (Finset.subset_univ _) hu (show 2 ≤ m by omega)
    (show m ≤ (Finset.univ : Finset (Fin n)).card by
      simpa only [Finset.card_univ, Fintype.card_fin] using hm.2.1)
    (by simpa only [Finset.card_univ, Fintype.card_fin, mul_div_assoc] using hcollision)
  have hmono := blockProbability_mono (Finset.univ : Finset (Fin n)) m
    (fun B _ hB => hdetect B hB)
  simpa only [Finset.card_univ, Fintype.card_fin] using hsingle.trans hmono

end

end Problem313

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution : type_of% @_root_.OAI.Problem313.sqrt_block_detection_probability := @_root_.OAI.Problem313.sqrt_block_detection_probability
