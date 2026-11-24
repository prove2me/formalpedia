-- Prove2me | solution 1 for GlobalTheory.RandomTops.marked_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:44:34.432628+00:00
-- url     : https://prove2.me/submissions/4ca909dd-25bc-4153-b09c-0c844ee8931b

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Theorems.Thm_GlobalTheory_RandomTops_ind_pos
import Theorems.Thm_GlobalTheory_RandomTops_ind_neg
import Theorems.Thm_GlobalTheory_RandomTops_ind_nonneg
import Theorems.Thm_GlobalTheory_RandomTops_ind_le_one
import Theorems.Thm_GlobalTheory_RandomTops_ex_mono
import Theorems.Thm_GlobalTheory_RandomTops_ex_prod
import Theorems.Thm_GlobalTheory_RandomTops_cell_subset
import Theorems.Thm_GlobalTheory_RandomTops_cell_card
import Theorems.Thm_GlobalTheory_RandomTops_ico_disjoint
import Theorems.Thm_GlobalTheory_RandomTops_ex_isEmpty
import Theorems.Thm_GlobalTheory_RandomTops_ex_single_even
import Theorems.Thm_GlobalTheory_RandomTops_prod_alternate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Formalism.G0
open GlobalTheory GlobalTheory.RandomTops
variable {δ : ℝ}
namespace GlobalTheory.RandomTops
theorem _root_.solution (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (r u s : ℕ) :
    markedBound δ r u ≤ ex δ (tile r u s) (fun T => ind (Marked T r u s)) := by
  have hm : 6 * r + 1 = 2 * (3 * r) + 1 := by ring
  have hcell : ∀ c, cell r u s (c + 1) =
      Ico (s * ((6 * r + 1) * u) + c * u) (s * ((6 * r + 1) * u) + c * u + u) := by
    intro c
    unfold cell
    rw [Nat.add_sub_cancel]
    congr 1
    ring
  have hX : 0 ≤ ((u / 2 : ℕ) : ℝ) * δ * (1 - δ) ^ (u - 1) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) h0) (pow_nonneg (by linarith) _)
  have hP0 : 0 ≤ (1 - δ) ^ u := pow_nonneg (by linarith) _
  have hind : ∀ (c' : ℕ) (V : Finset ℕ),
      0 ≤ (if Even c' then ind (V = ∅) else ind (∃ x, V = {x} ∧ Even x)) ∧
        (if Even c' then ind (V = ∅) else ind (∃ x, V = {x} ∧ Even x)) ≤ 1 := by
    intro c' V
    split_ifs
    · exact ⟨ind_nonneg _, ind_le_one _⟩
    · exact ⟨ind_nonneg _, ind_le_one _⟩
  have hpt : ∀ T ⊆ tile r u s, ∏ c' ∈ range (6 * r + 1),
      (if Even c' then ind (T ∩ cell r u s (c' + 1) = ∅)
        else ind (∃ x, T ∩ cell r u s (c' + 1) = {x} ∧ Even x)) ≤ ind (Marked T r u s) := by
    intro T _
    by_cases hM : Marked T r u s
    · rw [ind_pos hM]
      exact prod_le_one (fun c' _ => (hind c' _).1) (fun c' _ => (hind c' _).2)
    · rw [ind_neg hM]
      refine le_of_eq (prod_eq_zero_iff.mpr ?_)
      by_contra hall
      push Not at hall
      apply hM
      intro c hc1 hc2
      have h := hall (c - 1) (by rw [mem_range]; omega)
      have hcc : c - 1 + 1 = c := by omega
      rw [hcc] at h
      constructor
      · intro hodd
        have he : Even (c - 1) := by
          obtain ⟨k, hk⟩ := hodd
          exact ⟨k, by omega⟩
        rw [if_pos he] at h
        by_contra hne
        exact h (ind_neg hne)
      · intro hev
        have he : ¬ Even (c - 1) := by
          rintro ⟨k, hk⟩
          obtain ⟨k', hk'⟩ := hev
          omega
        rw [if_neg he] at h
        by_contra hne
        exact h (ind_neg hne)
  calc markedBound δ r u
      = ∏ c' ∈ range (6 * r + 1),
          (if Even c' then (1 - δ) ^ u else ((u / 2 : ℕ) : ℝ) * δ * (1 - δ) ^ (u - 1)) := by
        unfold markedBound
        rw [hm, prod_alternate]
    _ ≤ ∏ c' ∈ range (6 * r + 1), ex δ (cell r u s (c' + 1))
          (fun V => if Even c' then ind (V = ∅) else ind (∃ x, V = {x} ∧ Even x)) := by
        refine prod_le_prod (fun c' _ => ?_) (fun c' _ => ?_)
        · split_ifs
          · exact hP0
          · exact hX
        · by_cases he : Even c'
          · simp only [if_pos he]
            exact le_of_eq (by rw [ex_isEmpty, cell_card (c := c' + 1) (by omega)])
          · simp only [if_neg he]
            rw [hcell]
            exact ex_single_even h0 h1 _ u
    _ = ex δ (tile r u s) (fun T => ∏ c' ∈ range (6 * r + 1),
          (if Even c' then ind (T ∩ cell r u s (c' + 1) = ∅)
            else ind (∃ x, T ∩ cell r u s (c' + 1) = {x} ∧ Even x))) := by
        refine (ex_prod (range (6 * r + 1)) (fun c' => cell r u s (c' + 1))
          (fun c' V => if Even c' then ind (V = ∅) else ind (∃ x, V = {x} ∧ Even x)) ?_ (tile r u s) ?_).symm
        · intro i _ j _ hij
          show Disjoint (cell r u s (i + 1)) (cell r u s (j + 1))
          rw [hcell, hcell]
          have := ico_disjoint (a := s * ((6 * r + 1) * u)) (m := u) hij
          convert this using 2 <;> ring
        · intro c' hc'
          rw [mem_range] at hc'
          exact cell_subset (c := c' + 1) (by omega)
    _ ≤ _ := ex_mono h0 h1 hpt
end GlobalTheory.RandomTops
