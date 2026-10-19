-- Prove2me | solution 1 for OAI.Problem313.blockProbability_singleton_inter_ge
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:09:05.063721+00:00
-- url     : https://prove2.me/submissions/b5e7e663-1444-4ba2-9d2f-0864cc836e72

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockCounting.lean:L195-L225
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.blockProbability_singleton_inter_ge. The node keeps its source
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
import Theorems.Thm_OAI_Problem313_blockProbability_exists_le

-- ---- from OAI.Combinatorics.SharpThreshold.BlockCounting ----
namespace OAI

universe u

noncomputable section

namespace Problem313

open Finset

variable {α : Type u} [DecidableEq α]

omit [DecidableEq α] in
theorem blockProbability_eq (U : Finset α) (m : ℕ) (P : Finset α → Prop)
    [DecidablePred P] : blockProbability U m P =
      (((U.powersetCard m).filter P).card : ℝ) / (U.powersetCard m).card := by
  unfold blockProbability
  congr

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

theorem blockProbability_mem_count (U : Finset α) {m : ℕ} {u : α}
    (hu : u ∈ U) (hm : 1 ≤ m) :
    ((U.powersetCard m).filter (fun B => u ∈ B)).card =
      (U.card - 1).choose (m - 1) := by
  classical
  simpa using Finset.card_filter_powersetCard_subset {u} U m
    (Finset.singleton_subset_iff.mpr hu) (by simpa using hm)

theorem choose_pred_ratio {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    ((n - 1).choose (m - 1) : ℝ) / n.choose m = (m : ℝ) / n := by
  have hn : 1 ≤ n := hm.trans hmn
  have hchoose : (n.choose m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hmn).ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hid := Nat.add_one_mul_choose_eq (n - 1) (m - 1)
  rw [Nat.sub_add_cancel hn, Nat.sub_add_cancel hm] at hid
  have hid' : (n : ℝ) * ((n - 1).choose (m - 1) : ℝ) =
      (n.choose m : ℝ) * m := by exact_mod_cast hid
  apply (div_eq_div_iff hchoose hn0).mpr
  nlinarith

theorem blockProbability_mem (U : Finset α) {m : ℕ} {u : α}
    (hu : u ∈ U) (hm : 1 ≤ m) (hmn : m ≤ U.card) :
    blockProbability U m (fun B => u ∈ B) = (m : ℝ) / U.card := by
  classical
  rw [blockProbability_eq, blockProbability_mem_count U hu hm, Finset.card_powersetCard]
  exact choose_pred_ratio hm hmn

theorem blockProbability_pair_count (U : Finset α) {m : ℕ} {u v : α}
    (hu : u ∈ U) (hv : v ∈ U) (huv : u ≠ v) (hm : 2 ≤ m) :
    ((U.powersetCard m).filter (fun B => u ∈ B ∧ v ∈ B)).card =
      (U.card - 2).choose (m - 2) := by
  simpa [huv, Finset.insert_subset_iff, Finset.singleton_subset_iff] using Finset.card_filter_powersetCard_subset {u, v} U m
    (by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hu, hv⟩) (by simpa [huv] using hm)

theorem choose_two_pred_ratio {n m : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    ((n - 2).choose (m - 2) : ℝ) / n.choose m =
      (m : ℝ) / n * ((m : ℝ) - 1) / ((n : ℝ) - 1) := by
  have hm1 : 1 ≤ m := by omega
  have hn1 : 1 ≤ n := hm1.trans hmn
  have hmid : ((n - 1).choose (m - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show m - 1 ≤ n - 1 by omega)).ne'
  calc
    ((n - 2).choose (m - 2) : ℝ) / n.choose m =
        (((n - 1 - 1).choose (m - 1 - 1) : ℝ) / (n - 1).choose (m - 1)) *
          (((n - 1).choose (m - 1) : ℝ) / n.choose m) := by
      simp only [Nat.sub_sub]; norm_num only at *
      field_simp
    _ = ((m - 1 : ℕ) : ℝ) / (n - 1 : ℕ) * ((m : ℝ) / n) := by
      rw [choose_pred_ratio (by omega : 1 ≤ m - 1) (by omega : m - 1 ≤ n - 1),
        choose_pred_ratio hm1 hmn]
    _ = _ := by
      rw [Nat.cast_sub hm1, Nat.cast_sub hn1]
      push_cast
      ring

theorem blockProbability_pair (U : Finset α) {m : ℕ} {u v : α}
    (hu : u ∈ U) (hv : v ∈ U) (huv : u ≠ v) (hm : 2 ≤ m)
    (hmn : m ≤ U.card) :
    blockProbability U m (fun B => u ∈ B ∧ v ∈ B) =
      (m : ℝ) / U.card * ((m : ℝ) - 1) / ((U.card : ℝ) - 1) := by
  classical
  rw [blockProbability_eq, blockProbability_pair_count U hu hv huv hm,
    Finset.card_powersetCard]
  exact choose_two_pred_ratio hm hmn

omit [DecidableEq α] in
theorem blockProbability_congr (U : Finset α) (m : ℕ)
    {P Q : Finset α → Prop}
    (hPQ : ∀ B ∈ U.powersetCard m, P B ↔ Q B) :
    blockProbability U m P = blockProbability U m Q := by
  apply le_antisymm
  · exact blockProbability_mono U m (fun B hB => (hPQ B hB).mp)
  · exact blockProbability_mono U m (fun B hB => (hPQ B hB).mpr)

theorem blockProbability_or_le (U : Finset α) (m : ℕ)
    (P Q : Finset α → Prop) :
    blockProbability U m (fun B => P B ∨ Q B) ≤
      blockProbability U m P + blockProbability U m Q := by
  classical
  simp only [blockProbability_eq, Finset.filter_or]
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_union_le ((U.powersetCard m).filter P)
    ((U.powersetCard m).filter Q)

theorem blockProbability_avoid_ge (U : Finset α) (m : ℕ)
    (V : Finset α) (P : Finset α → Prop) (Q : α → Finset α → Prop) :
    blockProbability U m P - ∑ v ∈ V, blockProbability U m (fun B => P B ∧ Q v B) ≤
      blockProbability U m (fun B => P B ∧ ∀ v ∈ V, ¬ Q v B) := by
  classical
  have hcover : blockProbability U m P ≤
      blockProbability U m (fun B => (P B ∧ ∀ v ∈ V, ¬ Q v B) ∨
        ∃ v ∈ V, P B ∧ Q v B) := by
    apply blockProbability_mono
    intro B hB hP
    by_cases h : ∀ v ∈ V, ¬ Q v B
    · exact Or.inl ⟨hP, h⟩
    · push Not at h
      obtain ⟨v, hv, hQ⟩ := h
      exact Or.inr ⟨v, hv, hP, hQ⟩
  have hbound := hcover.trans ((blockProbability_or_le U m _ _).trans
    (add_le_add le_rfl (blockProbability_exists_le U m V (fun v B => P B ∧ Q v B))))
  linarith

theorem inter_eq_singleton_iff_mem_avoid (B V : Finset α) {u : α} (hu : u ∈ V) :
    B ∩ V = {u} ↔ u ∈ B ∧ ∀ v ∈ V.erase u, v ∉ B := by
  constructor
  · intro h
    constructor
    · have hmem : u ∈ B ∩ V := by rw [h]; simp
      exact (Finset.mem_inter.mp hmem).1
    · intro v hv hvB
      have hvV := (Finset.mem_erase.mp hv).2
      have hmem : v ∈ B ∩ V := Finset.mem_inter.mpr ⟨hvB, hvV⟩
      rw [h, Finset.mem_singleton] at hmem
      exact (Finset.mem_erase.mp hv).1 hmem
  · rintro ⟨huB, havoid⟩
    ext v
    simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨hvB, hvV⟩
      by_contra hvu
      exact havoid v (Finset.mem_erase.mpr ⟨hvu, hvV⟩) hvB
    · rintro rfl
      exact ⟨huB, hu⟩

/-- A union bound conditioned on containing a specified vertex. -/
theorem blockProbability_singleton_inter_ge (U V : Finset α) {m : ℕ} {u : α}
    (hVU : V ⊆ U) (hu : u ∈ V) (hm : 2 ≤ m) (hmn : m ≤ U.card) :
    (m : ℝ) / U.card *
        (1 - ((V.card : ℝ) - 1) * ((m : ℝ) - 1) / ((U.card : ℝ) - 1)) ≤
      blockProbability U m (fun B => B ∩ V = {u}) := by
  classical
  have h := blockProbability_avoid_ge U m (V.erase u) (fun B => u ∈ B)
    (fun v B => v ∈ B)
  have hevent : blockProbability U m (fun B => u ∈ B ∧ ∀ v ∈ V.erase u, v ∉ B) =
      blockProbability U m (fun B => B ∩ V = {u}) := by
    apply blockProbability_congr
    intro B hB
    exact (inter_eq_singleton_iff_mem_avoid B V hu).symm
  rw [hevent, blockProbability_mem U (hVU hu) (by omega) hmn] at h
  have hsum : (∑ v ∈ V.erase u, blockProbability U m (fun B => u ∈ B ∧ v ∈ B)) =
      ((V.card : ℝ) - 1) *
        ((m : ℝ) / U.card * ((m : ℝ) - 1) / ((U.card : ℝ) - 1)) := by
    calc
      _ = ∑ _v ∈ V.erase u,
          ((m : ℝ) / U.card * ((m : ℝ) - 1) / ((U.card : ℝ) - 1)) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact blockProbability_pair U (hVU hu) (hVU (Finset.mem_erase.mp hv).2)
          (Ne.symm (Finset.mem_erase.mp hv).1) hm hmn
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hu]
        rw [Nat.cast_sub (Finset.one_le_card.mpr ⟨u, hu⟩)]
        norm_num
  rw [hsum] at h
  convert h using 1; ring

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313
open Finset


theorem solution.{u} : type_of% @_root_.OAI.Problem313.blockProbability_singleton_inter_ge.{u} := @_root_.OAI.Problem313.blockProbability_singleton_inter_ge.{u}
