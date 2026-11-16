-- Prove2me | solution 1 for ListReplicableBias.LowerBound.Supplement.lemma_6_7
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:01:48.263296+00:00
-- url     : https://prove2.me/submissions/58c447d4-030b-4918-8ed4-53292eefc219

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_Geometry
import Definitions.Def_ListReplicableBias_LowerBound_Supplement_Rounding

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open ListReplicableBias.LowerBound ListReplicableBias.LowerBound.Supplement

lemma lrb67_floor_eq {ε z : ℝ} (k : ℤ) (hε : 0 < ε)
    (h1 : (k : ℝ) * ε ≤ z) (h2 : z < ((k : ℝ) + 1) * ε) : ⌊z / ε⌋ = k := by
  rw [Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hε]; exact h1
  · rw [div_lt_iff₀ hε]; exact h2

lemma lrb67_floor_shift {ε x u : ℝ} (hε : 0 < ε) (hu0 : 0 ≤ u) (hu1 : u < ε) :
    ⌊(x + u) / ε⌋ = if ((⌊x / ε⌋ : ℝ) + 1) * ε - x ≤ u then ⌊x / ε⌋ + 1 else ⌊x / ε⌋ := by
  have ha1 : (⌊x / ε⌋ : ℝ) ≤ x / ε := Int.floor_le _
  have ha2 : x / ε < (⌊x / ε⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hε] at ha1
  rw [div_lt_iff₀ hε] at ha2
  split_ifs with h
  · apply lrb67_floor_eq _ hε
    · push_cast; linarith
    · push_cast; nlinarith
  · apply lrb67_floor_eq _ hε
    · nlinarith
    · linarith

lemma lrb67_close {ε u x : ℝ} (hε : 0 < ε) (hu0 : 0 ≤ u) (hu1 : u < ε) :
    |roundShift ε u x - x| < ε := by
  unfold roundShift
  have ha1 : (⌊(x + u) / ε⌋ : ℝ) ≤ (x + u) / ε := Int.floor_le _
  have ha2 : (x + u) / ε < (⌊(x + u) / ε⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hε] at ha1
  rw [div_lt_iff₀ hε] at ha2
  rw [abs_lt]; constructor <;> nlinarith

theorem solution (ε : ℝ) (hε : 0 < ε) (d : ℕ) (p : Fin d → ℝ) (hp : p ∈ cube d 0 1) :
    (∀ y ∈ canonicalList ε p, ‖y - p‖ < ε) ∧
    (canonicalList ε p).encard ≤ (d : ℕ∞) + 1 := by
  constructor
  · rintro y ⟨u, hu, rfl⟩
    rw [pi_norm_lt_iff hε]
    intro i
    rw [Real.norm_eq_abs]
    exact lrb67_close hε hu.1 hu.2
  · -- thresholds
    set t : Fin d → ℝ := fun i => ((⌊p i / ε⌋ : ℝ) + 1) * ε - p i with ht
    set T : Finset ℝ := Finset.univ.image t with hT
    let c : ℝ → ℕ := fun u => (T.filter (· ≤ u)).card
    have hcle : ∀ u, c u ∈ Finset.range (d + 1) := by
      intro u
      rw [Finset.mem_range, Nat.lt_succ_iff]
      calc c u ≤ T.card := Finset.card_filter_le _ _
        _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_image_le
        _ = d := by simp
    have key : ∀ u ∈ Set.Ico (0 : ℝ) ε, ∀ u' ∈ Set.Ico (0 : ℝ) ε, u ≤ u' → c u = c u' →
        roundVec ε u p = roundVec ε u' p := by
      intro u hu u' hu' hle hc
      have hsub : T.filter (· ≤ u) ⊆ T.filter (· ≤ u') := by
        intro z hz
        rw [Finset.mem_filter] at hz ⊢
        exact ⟨hz.1, le_trans hz.2 hle⟩
      have heq : T.filter (· ≤ u) = T.filter (· ≤ u') :=
        Finset.eq_of_subset_of_card_le hsub (le_of_eq hc.symm)
      funext i
      unfold roundVec roundShift
      rw [lrb67_floor_shift hε hu.1 hu.2, lrb67_floor_shift hε hu'.1 hu'.2]
      have hiff : t i ≤ u ↔ t i ≤ u' := by
        constructor
        · intro h; exact le_trans h hle
        · intro h
          have hm : t i ∈ T.filter (· ≤ u') := by
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), h⟩
          rw [← heq, Finset.mem_filter] at hm
          exact hm.2
      have hiff' : ((⌊p i / ε⌋ : ℝ) + 1) * ε - p i ≤ u ↔
          ((⌊p i / ε⌋ : ℝ) + 1) * ε - p i ≤ u' := hiff
      by_cases h : ((⌊p i / ε⌋ : ℝ) + 1) * ε - p i ≤ u
      · rw [if_pos h, if_pos (hiff'.mp h)]
      · rw [if_neg h, if_neg (fun h' => h (hiff'.mpr h'))]
    have key2 : ∀ u ∈ Set.Ico (0 : ℝ) ε, ∀ u' ∈ Set.Ico (0 : ℝ) ε, c u = c u' →
        roundVec ε u p = roundVec ε u' p := by
      intro u hu u' hu' hc
      rcases le_total u u' with h | h
      · exact key u hu u' hu' h hc
      · exact (key u' hu' u hu h hc.symm).symm
    classical
    let g : ℕ → (Fin d → ℝ) := fun k =>
      if h : ∃ u ∈ Set.Ico (0 : ℝ) ε, c u = k then roundVec ε h.choose p else 0
    have hsub : canonicalList ε p ⊆ g '' ((Finset.range (d + 1) : Finset ℕ) : Set ℕ) := by
      rintro y ⟨u, hu, rfl⟩
      refine ⟨c u, hcle u, ?_⟩
      have hex : ∃ v ∈ Set.Ico (0 : ℝ) ε, c v = c u := ⟨u, hu, rfl⟩
      simp only [g, dif_pos hex]
      exact key2 _ hex.choose_spec.1 u hu hex.choose_spec.2
    calc (canonicalList ε p).encard
        ≤ (g '' ((Finset.range (d + 1) : Finset ℕ) : Set ℕ)).encard := Set.encard_le_encard hsub
      _ ≤ ((Finset.range (d + 1) : Finset ℕ) : Set ℕ).encard := Set.encard_image_le _ _
      _ = (d : ℕ∞) + 1 := by
        rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_range]; push_cast; rfl
