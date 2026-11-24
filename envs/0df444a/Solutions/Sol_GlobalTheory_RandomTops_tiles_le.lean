-- Prove2me | solution 1 for GlobalTheory.RandomTops.tiles_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:59:50.378892+00:00
-- url     : https://prove2.me/submissions/d09caff6-9c8d-4dce-ad9b-681e504ebf8b

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Theorems.Thm_GlobalTheory_RandomTops_ind_neg
import Theorems.Thm_GlobalTheory_RandomTops_ind_le_one
import Theorems.Thm_GlobalTheory_RandomTops_ind_le
import Theorems.Thm_GlobalTheory_RandomTops_ex_const
import Theorems.Thm_GlobalTheory_RandomTops_ex_one_sub
import Theorems.Thm_GlobalTheory_RandomTops_ex_sum
import Theorems.Thm_GlobalTheory_RandomTops_ex_mono
import Theorems.Thm_GlobalTheory_RandomTops_ex_prod
import Theorems.Thm_GlobalTheory_RandomTops_tile_disjoint
import Theorems.Thm_GlobalTheory_RandomTops_marked_ge
import Theorems.Thm_GlobalTheory_RandomTops_marked_congr

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
theorem _root_.solution (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {n r u M₀ i₀ : ℕ} (hu : 1 ≤ u)
    (hn : (M₀ + 1) * ((6 * r + 1) * u) ≤ n) :
    ex δ ((Finset.range n).erase i₀) (fun U => ind (¬ CondTiles n (insert i₀ U) r u M₀)) ≤
      n * (1 - markedBound δ r u) ^ M₀ := by
  obtain ⟨N, hN⟩ : ∃ N, N = n / ((6 * r + 1) * u) := ⟨_, rfl⟩
  have hm1 : 1 ≤ (6 * r + 1) * u := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hMN : M₀ + 1 ≤ N := by rw [hN, Nat.le_div_iff_mul_le (by omega)]; exact hn
  have hNn : N ≤ n := hN ▸ Nat.div_le_self _ _
  have hNm : N * ((6 * r + 1) * u) ≤ n := hN ▸ Nat.div_mul_le_self _ _
  have htinj : ∀ s₀ j₁ j₂, j₁ < N → j₂ < N → (s₀ + j₁) % N = (s₀ + j₂) % N → j₁ = j₂ := by
    intro s₀ j₁ j₂ h1 h2 h
    have := Nat.ModEq.add_left_cancel' s₀ h
    rwa [Nat.ModEq, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
  have htlt : ∀ s₀ j, (s₀ + j) % N < N := fun s₀ j => Nat.mod_lt _ (by omega)
  have htile : ∀ t < N, tile r u t ⊆ range n := by
    intro t ht x hx
    simp only [tile, mem_Ico] at hx
    rw [mem_range]
    have h1 : (t + 1) * ((6 * r + 1) * u) ≤ N * ((6 * r + 1) * u) := Nat.mul_le_mul_right _ ht
    linarith [hx.2]
  have hgood : ∀ s₀, M₀ ≤ #((range (M₀ + 1)).filter (fun j => i₀ ∉ tile r u ((s₀ + j) % N))) := by
    intro s₀
    have hbad : #((range (M₀ + 1)).filter (fun j => ¬ i₀ ∉ tile r u ((s₀ + j) % N))) ≤ 1 := by
      refine card_le_one.mpr fun j₁ hj₁ j₂ hj₂ => ?_
      rw [mem_filter, mem_range, not_not] at hj₁ hj₂
      by_contra hne
      have hne' : (s₀ + j₁) % N ≠ (s₀ + j₂) % N := fun h => hne (htinj s₀ j₁ j₂ (by omega) (by omega) h)
      exact disjoint_left.mp (tile_disjoint hne') hj₁.2 hj₂.2
    have := card_filter_add_card_filter_not (s := range (M₀ + 1))
      (p := fun j => i₀ ∉ tile r u ((s₀ + j) % N))
    rw [card_range] at this
    omega
  choose J hJsub hJcard using fun s₀ => Finset.exists_subset_card_eq (hgood s₀)
  have hJ : ∀ s₀, ∀ j ∈ J s₀, j < M₀ + 1 ∧ i₀ ∉ tile r u ((s₀ + j) % N) := by
    intro s₀ j hj
    have := hJsub s₀ hj
    rw [mem_filter, mem_range] at this
    exact this
  have hfac : ∀ p : Prop, 0 ≤ 1 - ind p := fun p => by linarith [ind_le_one p]
  have hpt : ∀ U ⊆ (range n).erase i₀, ind (¬ CondTiles n (insert i₀ U) r u M₀) ≤
      ∑ s₀ ∈ range N, ∏ j ∈ J s₀,
        (1 - ind (Marked (U ∩ tile r u ((s₀ + j) % N)) r u ((s₀ + j) % N))) := by
    intro U _
    refine ind_le (sum_nonneg fun s₀ _ => prod_nonneg fun j _ => hfac _) fun hct => ?_
    unfold CondTiles at hct
    rw [← hN] at hct
    push Not at hct
    obtain ⟨s₀, hs₀, hall⟩ := hct
    have hone : ∏ j ∈ J s₀,
        (1 - ind (Marked (U ∩ tile r u ((s₀ + j) % N)) r u ((s₀ + j) % N))) = 1 := by
      refine prod_eq_one fun j hj => ?_
      obtain ⟨hjM, hji⟩ := hJ s₀ j hj
      rw [ind_neg, sub_zero]
      intro hM
      apply hall j (by omega)
      refine marked_congr ?_ hM
      ext x
      simp only [mem_inter, mem_insert]
      constructor
      · rintro ⟨⟨hxU, hxt⟩, _⟩
        exact ⟨Or.inr hxU, hxt⟩
      · rintro ⟨hx | hxU, hxt⟩
        · exact absurd (hx ▸ hxt) hji
        · exact ⟨⟨hxU, hxt⟩, hxt⟩
    calc (1 : ℝ) = _ := hone.symm
      _ ≤ _ := single_le_sum (f := fun s₀ => ∏ j ∈ J s₀,
          (1 - ind (Marked (U ∩ tile r u ((s₀ + j) % N)) r u ((s₀ + j) % N))))
        (fun s₀ _ => prod_nonneg fun j _ => hfac _) (mem_range.mpr hs₀)
  have hex1 : ∀ t, ex δ (tile r u t) (fun T => ind (Marked T r u t)) ≤ 1 := fun t =>
    (ex_mono h0 h1 fun T _ => ind_le_one _).trans (le_of_eq (ex_const _ _))
  have hmb1 : 0 ≤ 1 - markedBound δ r u := by linarith [marked_ge h0 h1 r u 0, hex1 0]
  calc ex δ ((range n).erase i₀) (fun U => ind (¬ CondTiles n (insert i₀ U) r u M₀))
      ≤ ex δ ((range n).erase i₀) (fun U => ∑ s₀ ∈ range N, ∏ j ∈ J s₀,
          (1 - ind (Marked (U ∩ tile r u ((s₀ + j) % N)) r u ((s₀ + j) % N)))) := ex_mono h0 h1 hpt
    _ = ∑ s₀ ∈ range N, ex δ ((range n).erase i₀) (fun U => ∏ j ∈ J s₀,
          (1 - ind (Marked (U ∩ tile r u ((s₀ + j) % N)) r u ((s₀ + j) % N)))) :=
        ex_sum _ _ (fun s₀ U => ∏ j ∈ J s₀,
          (1 - ind (Marked (U ∩ tile r u ((s₀ + j) % N)) r u ((s₀ + j) % N))))
    _ = ∑ s₀ ∈ range N, ∏ j ∈ J s₀, ex δ (tile r u ((s₀ + j) % N))
          (fun V => 1 - ind (Marked V r u ((s₀ + j) % N))) := by
        refine sum_congr rfl fun s₀ _ => ?_
        refine ex_prod (J s₀) (fun j => tile r u ((s₀ + j) % N))
          (fun j V => 1 - ind (Marked V r u ((s₀ + j) % N))) ?_ _ ?_
        · intro i hi k hk hik
          refine tile_disjoint fun h => hik (htinj s₀ i k ?_ ?_ h)
          · have := (hJ s₀ i hi).1
            omega
          · have := (hJ s₀ k hk).1
            omega
        · intro j hj x hx
          rw [mem_erase]
          exact ⟨fun h => (hJ s₀ j hj).2 (h ▸ hx), htile _ (htlt s₀ j) hx⟩
    _ ≤ ∑ s₀ ∈ range N, (1 - markedBound δ r u) ^ M₀ := by
        refine sum_le_sum fun s₀ _ => ?_
        calc _ ≤ ∏ j ∈ J s₀, (1 - markedBound δ r u) := by
              refine prod_le_prod (fun j _ => ?_) (fun j _ => ?_)
              · rw [ex_one_sub]
                linarith [hex1 ((s₀ + j) % N)]
              · rw [ex_one_sub]
                linarith [marked_ge h0 h1 r u ((s₀ + j) % N)]
          _ = _ := by rw [prod_const, hJcard]
    _ = N * (1 - markedBound δ r u) ^ M₀ := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ n * (1 - markedBound δ r u) ^ M₀ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hNn) (pow_nonneg hmb1 _)
end GlobalTheory.RandomTops
