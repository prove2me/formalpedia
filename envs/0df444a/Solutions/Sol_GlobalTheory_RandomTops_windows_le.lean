-- Prove2me | solution 1 for GlobalTheory.RandomTops.windows_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:44:24.465291+00:00
-- url     : https://prove2.me/submissions/8b2466fd-cc9b-400d-b5bd-b21249494d03

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Theorems.Thm_GlobalTheory_RandomTops_ind_pos
import Theorems.Thm_GlobalTheory_RandomTops_ind_nonneg
import Theorems.Thm_GlobalTheory_RandomTops_ind_le
import Theorems.Thm_GlobalTheory_RandomTops_ex_sum
import Theorems.Thm_GlobalTheory_RandomTops_ex_mono
import Theorems.Thm_GlobalTheory_RandomTops_ex_restrict

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
theorem _root_.solution (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (n i₀ L K K' : ℕ) (hK : K' ≤ K) (b : ℝ)
    (hb : ∀ A : Finset ℕ, A.card ≤ L → ex δ A (fun T => ind (K' ≤ T.card)) ≤ b) :
    ex δ ((Finset.range n).erase i₀)
      (fun U => ind (¬ ∀ i < n, (insert i₀ U ∩ window n i L).card ≤ K)) ≤ n * b := by
  have hpt : ∀ U ⊆ (range n).erase i₀, ind (¬ ∀ i < n, #(insert i₀ U ∩ window n i L) ≤ K) ≤
      ∑ i ∈ range n, ind (K' ≤ #(U ∩ (window n i L ∩ (range n).erase i₀))) := by
    intro U hU
    refine ind_le (sum_nonneg fun _ _ => ind_nonneg _) fun hn => ?_
    push Not at hn
    obtain ⟨i, hi, hgt⟩ := hn
    have e : U ∩ (window n i L ∩ (range n).erase i₀) = U ∩ window n i L := by
      ext x
      simp only [mem_inter]
      constructor
      · rintro ⟨a, b, _⟩
        exact ⟨a, b⟩
      · rintro ⟨a, b⟩
        exact ⟨a, b, hU a⟩
    have hc : #(insert i₀ U ∩ window n i L) ≤ #(U ∩ window n i L) + 1 :=
      calc #(insert i₀ U ∩ window n i L) ≤ #(insert i₀ (U ∩ window n i L)) :=
          card_le_card fun x hx => by
            simp only [mem_inter, mem_insert] at hx ⊢
            tauto
        _ ≤ _ := card_insert_le _ _
    have hK'' : K' ≤ #(U ∩ (window n i L ∩ (range n).erase i₀)) := by rw [e]; omega
    calc (1 : ℝ) = ind (K' ≤ #(U ∩ (window n i L ∩ (range n).erase i₀))) := (ind_pos hK'').symm
      _ ≤ _ := single_le_sum (f := fun i => ind (K' ≤ #(U ∩ (window n i L ∩ (range n).erase i₀))))
        (fun _ _ => ind_nonneg _) (mem_range.mpr hi)
  calc _ ≤ ex δ ((range n).erase i₀)
        (fun U => ∑ i ∈ range n, ind (K' ≤ #(U ∩ (window n i L ∩ (range n).erase i₀)))) :=
      ex_mono h0 h1 hpt
    _ = ∑ i ∈ range n, ex δ ((range n).erase i₀)
        (fun U => ind (K' ≤ #(U ∩ (window n i L ∩ (range n).erase i₀)))) :=
      ex_sum _ _ (fun i U => ind (K' ≤ #(U ∩ (window n i L ∩ (range n).erase i₀))))
    _ = ∑ i ∈ range n, ex δ (window n i L ∩ (range n).erase i₀) (fun T => ind (K' ≤ #T)) :=
      sum_congr rfl fun i _ => ex_restrict inter_subset_right (fun T => ind (K' ≤ #T))
    _ ≤ ∑ i ∈ range n, b := sum_le_sum fun i _ => hb _ (le_trans (card_le_card inter_subset_left)
        (by unfold window; exact card_image_le.trans (card_range L).le))
    _ = n * b := by rw [sum_const, card_range, nsmul_eq_mul]
end GlobalTheory.RandomTops
