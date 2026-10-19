-- Prove2me | solution 1 for OAI.EntropyRateDimension.FairPairs.coupling_distance_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:50:15.210183+00:00
-- url     : https://prove2.me/submissions/7c5a5590-5768-482d-a129-d8ed5d826323

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FairPairs
universe uι uα uβ
open scoped BigOperators ENNReal
open MeasureTheory
theorem h44_band (d : ℝ) (hd : 0 < d) (ℓ : ℤ) :
    bandIndex d = ℓ ↔ (2:ℝ)^(-ℓ) ≤ d ∧ d < (2:ℝ)^(1-ℓ) := by
  unfold bandIndex
  rw [neg_eq_iff_eq_neg, Int.floor_eq_iff, Real.le_logb_iff_rpow_le one_lt_two hd,
    Real.logb_lt_iff_lt_rpow one_lt_two hd]
  have e1 : (2:ℝ)^((-ℓ:ℤ):ℝ) = (2:ℝ)^(-ℓ) := Real.rpow_intCast 2 (-ℓ)
  have e2 : (2:ℝ)^(((-ℓ:ℤ):ℝ)+1) = (2:ℝ)^(1-ℓ) := by
    rw [show ((-ℓ:ℤ):ℝ)+1 = ((1-ℓ:ℤ):ℝ) by push_cast; ring]; exact Real.rpow_intCast 2 _
  rw [e1, e2]

theorem h44_edges_mem (ν : Law) (ℓ : ℤ) (e : ℝ × ℝ) :
    e ∈ ν.edges ℓ ↔ e ∈ ν.support ×ˢ ν.support ∧ e.1 < e.2 ∧ bandIndex |e.2 - e.1| = ℓ := by
  unfold Law.edges
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hd : 0 < e.2 - e.1 := sub_pos.mpr h2
    exact ⟨h1, h2, (h44_band _ (abs_pos.mpr hd.ne') ℓ).mpr (by rw [abs_of_pos hd]; exact h3)⟩
  · rintro ⟨h1, h2, h3⟩
    have hd : 0 < e.2 - e.1 := sub_pos.mpr h2
    have := (h44_band _ (abs_pos.mpr hd.ne') ℓ).mp h3
    rw [abs_of_pos hd] at this
    exact ⟨h1, h2, this⟩

theorem h44_cap_ge (ν : Law) (ℓ : ℤ) (π : ℝ → ℝ → ℝ)
    (hπ : ∀ x ∈ ν.support, ∀ y ∈ ν.support, 0 ≤ π x y)
    (hsym : ∀ x ∈ ν.support, ∀ y ∈ ν.support, π x y = π y x)
    (hrow : ∀ x ∈ ν.support, ∑ y ∈ ν.support, π x y ≤ ν.prob x) :
    2 * ∑ e ∈ ν.edges ℓ, π e.1 e.2 ≤ capacity ν ℓ := by
  classical
  set S := ν.support
  set E := ν.edges ℓ
  have hES : ∀ e ∈ E, e ∈ S ×ˢ S := fun e he => ((h44_edges_mem ν ℓ e).mp he).1
  have hprob1 : ∀ x ∈ S, ν.prob x ≤ 1 := fun x hx => by
    rw [← ν.prob_sum]
    exact Finset.single_le_sum (fun y hy => (ν.prob_pos y hy).le) hx
  -- bounded above
  have hbdd : BddAbove {t : ℝ | ∃ w : E → ℝ, Feasible w ∧ ∑ e, w e = t} := by
    refine ⟨2 * Fintype.card E, ?_⟩
    rintro t ⟨w, ⟨hw0, hwx⟩, rfl⟩
    have hle : ∀ e : E, w e ≤ 2 := by
      intro e
      have hx : e.1.1 ∈ S := (Finset.mem_product.mp (hES e.1 e.2)).1
      have h1 := hwx e.1.1 hx
      unfold incident at h1
      have h2 : w e / 2 ≤ ∑ e' : E, ((if e'.val.1 = e.1.1 then w e' / 2 else 0) +
          (if e'.val.2 = e.1.1 then w e' / 2 else 0)) := by
        refine le_trans ?_ (Finset.single_le_sum (f := fun e' : E =>
          (if e'.val.1 = e.1.1 then w e' / 2 else 0) + (if e'.val.2 = e.1.1 then w e' / 2 else 0))
          (fun e' _ => add_nonneg (by split_ifs <;> linarith [hw0 e'])
            (by split_ifs <;> linarith [hw0 e'])) (Finset.mem_univ e))
        simp only [if_pos rfl]
        split_ifs <;> linarith [hw0 e]
      have h3 : w e / 2 ≤ ν.prob e.1.1 := by
        refine h2.trans (le_of_eq_of_le ?_ h1)
        refine Finset.sum_congr rfl fun e' _ => ?_
        by_cases ha : e'.val.1 = e.1.1 <;> by_cases hb : e'.val.2 = e.1.1 <;> simp [ha, hb]
      linarith [hprob1 _ hx]
    calc ∑ e, w e ≤ ∑ _e : E, (2:ℝ) := Finset.sum_le_sum fun e _ => hle e
      _ = 2 * Fintype.card E := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  -- the feasible weight
  set w : E → ℝ := fun e => 2 * π e.1.1 e.1.2 with hw
  have hsumw : ∑ e, w e = 2 * ∑ e ∈ E, π e.1 e.2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_coe_sort E (fun e => 2 * π e.1 e.2)
  have hfeas : Feasible w := by
    constructor
    · intro e
      have := Finset.mem_product.mp (hES e.1 e.2)
      exact mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hπ _ this.1 _ this.2)
    · intro x hx
      unfold incident
      calc _ = ∑ e ∈ E, ((if e.1 = x ∧ e.1 < e.2 then π e.1 e.2 else 0) +
            (if e.2 = x ∧ e.1 < e.2 then π e.1 e.2 else 0)) := by
            rw [← Finset.sum_coe_sort E]
            refine Finset.sum_congr rfl fun e _ => ?_
            have hlt := ((h44_edges_mem ν ℓ e.1).mp e.2).2.1
            have hne : e.val.1 ≠ e.val.2 := hlt.ne
            by_cases ha : e.val.1 = x
            · have hb : ¬ e.val.2 = x := fun hb => hne (ha.trans hb.symm)
              have hlt' : x < e.val.2 := ha ▸ hlt
              simp [ha, hb, hw, hlt']
            · by_cases hb : e.val.2 = x
              · have hlt' : e.val.1 < x := hb ▸ hlt
                simp [ha, hb, hw, hlt']
              · simp [ha, hb]
        _ ≤ ∑ e ∈ S ×ˢ S, ((if e.1 = x ∧ e.1 < e.2 then π e.1 e.2 else 0) +
            (if e.2 = x ∧ e.1 < e.2 then π e.1 e.2 else 0)) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hES
            intro e he _
            have := Finset.mem_product.mp he
            have h0 := hπ _ this.1 _ this.2
            apply add_nonneg <;> split_ifs <;> linarith
        _ = ∑ y ∈ S, ((if x < y then π x y else 0) + (if y < x then π x y else 0)) := by
            rw [Finset.sum_product]
            dsimp only
            simp only [Finset.sum_add_distrib]
            congr 1
            · rw [Finset.sum_eq_single_of_mem x hx]
              · simp only [true_and]
              · intro a _ hax
                exact Finset.sum_eq_zero fun b _ => by simp [hax]
            · refine Finset.sum_congr rfl fun a ha => ?_
              rw [Finset.sum_eq_single_of_mem x hx]
              · simp only [true_and]
                rw [hsym a ha x hx]
              · intro b _ hb; simp [hb]
        _ ≤ ∑ y ∈ S, π x y := by
            refine Finset.sum_le_sum fun y hy => ?_
            have h0 := hπ x hx y hy
            by_cases h1 : x < y
            · rw [if_pos h1, if_neg (lt_asymm h1)]; simp
            · rw [if_neg h1]; split_ifs <;> simp [h0]
        _ ≤ ν.prob x := hrow x hx
  rw [← hsumw]
  exact le_csSup hbdd ⟨w, hfeas, rfl⟩

theorem solution {ν : Law} (π : ℝ → ℝ → ℝ) (R : ℝ)
    (hπ : ∀ x ∈ ν.support, ∀ y ∈ ν.support, 0 ≤ π x y)
    (hsym : ∀ x ∈ ν.support, ∀ y ∈ ν.support, π x y = π y x)
    (hrow : ∀ x ∈ ν.support, ∑ y ∈ ν.support, π x y ≤ ν.prob x)
    (hdiam : ∀ x ∈ ν.support, ∀ y ∈ ν.support, R < |y - x| → π x y = 0) :
    (∑ x ∈ ν.support, ∑ y ∈ ν.support, π x y * |y - x|) ≤
      ∑ ℓ ∈ ((ν.support ×ˢ ν.support).image (fun e => bandIndex |e.2 - e.1|)).filter
        (fun ℓ => (2 : ℝ) ^ (-ℓ) ≤ R), (2 : ℝ) ^ (1 - ℓ) * capacity ν ℓ := by
  classical
  set S := ν.support
  have hd0 : ∀ e : ℝ × ℝ, e.1 ≠ e.2 → 0 < |e.2 - e.1| := fun e h =>
    abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h))
  rw [← Finset.sum_product' (f := fun x y => π x y * |y - x|)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun e : ℝ × ℝ => bandIndex |e.2 - e.1|)
    (t := (S ×ˢ S).image (fun e => bandIndex |e.2 - e.1|)) (fun e he => Finset.mem_image_of_mem _ he)]
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun ℓ : ℤ => (2 : ℝ) ^ (-ℓ) ≤ R)]
  rw [Finset.sum_eq_zero (s := Finset.filter (fun ℓ : ℤ => ¬ (2 : ℝ) ^ (-ℓ) ≤ R) _), add_zero]
  swap
  · intro ℓ hℓ
    have hR := (Finset.mem_filter.mp hℓ).2
    refine Finset.sum_eq_zero fun e he => ?_
    obtain ⟨heS, hb⟩ := Finset.mem_filter.mp he
    have hm := Finset.mem_product.mp heS
    by_cases hee : e.1 = e.2
    · simp [hee]
    · have hpos := hd0 e hee
      have h1 := ((h44_band _ hpos ℓ).mp hb).1
      rw [hdiam e.1 hm.1 e.2 hm.2 (by linarith [not_le.mp hR])]; simp
  refine Finset.sum_le_sum fun ℓ _ => ?_
  set E := ν.edges ℓ
  have hE := h44_edges_mem ν ℓ
  have hcap := h44_cap_ge ν ℓ π hπ hsym hrow
  calc ∑ e ∈ (S ×ˢ S).filter (fun e : ℝ × ℝ => bandIndex |e.2 - e.1| = ℓ), π e.1 e.2 * |e.2 - e.1|
      ≤ ∑ e ∈ S ×ˢ S, (2:ℝ)^(1-ℓ) * ((if e ∈ E then π e.1 e.2 else 0) +
          (if e.swap ∈ E then π e.1 e.2 else 0)) := by
        rw [Finset.sum_filter]
        refine Finset.sum_le_sum fun e he => ?_
        have hm := Finset.mem_product.mp he
        have h0 := hπ _ hm.1 _ hm.2
        have hz : (0:ℝ) < (2:ℝ)^(1-ℓ) := zpow_pos two_pos _
        have hA : 0 ≤ (if e ∈ E then π e.1 e.2 else 0) := by split_ifs <;> simp [h0]
        have hB : 0 ≤ (if e.swap ∈ E then π e.1 e.2 else 0) := by split_ifs <;> simp [h0]
        by_cases hb : bandIndex |e.2 - e.1| = ℓ
        · rw [if_pos hb]
          by_cases hee : e.1 = e.2
          · rw [show |e.2 - e.1| = 0 by rw [hee, sub_self, abs_zero], mul_zero]; exact mul_nonneg hz.le (add_nonneg hA hB)
          · have hpos := hd0 e hee
            have hlt := ((h44_band _ hpos ℓ).mp hb).2
            have hmain : π e.1 e.2 * |e.2 - e.1| ≤ (2:ℝ)^(1-ℓ) * π e.1 e.2 := by
              rw [mul_comm]; exact mul_le_mul_of_nonneg_right hlt.le h0
            refine hmain.trans (mul_le_mul_of_nonneg_left ?_ hz.le)
            rcases lt_or_gt_of_ne hee with h | h
            · have : e ∈ E := (hE e).mpr ⟨he, h, hb⟩
              rw [if_pos this]; linarith
            · have : e.swap ∈ E := (hE e.swap).mpr ⟨Finset.mem_product.mpr ⟨hm.2, hm.1⟩, h,
                by simp only [Prod.fst_swap, Prod.snd_swap]; rw [abs_sub_comm]; exact hb⟩
              rw [if_pos this]; linarith
        · rw [if_neg hb]; exact mul_nonneg hz.le (add_nonneg hA hB)
    _ = (2:ℝ)^(1-ℓ) * (2 * ∑ e ∈ E, π e.1 e.2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        have hsw : ∑ e ∈ S ×ˢ S, (if e.swap ∈ E then π e.1 e.2 else 0) =
            ∑ e ∈ S ×ˢ S, (if e ∈ E then π e.1 e.2 else 0) := by
          rw [Finset.sum_product, Finset.sum_product, Finset.sum_comm]
          refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
          simp only [Prod.swap_prod_mk]
          rw [hsym b hb a ha]
        have hfe : ∑ e ∈ S ×ˢ S, (if e ∈ E then π e.1 e.2 else 0) = ∑ e ∈ E, π e.1 e.2 := by
          rw [← Finset.sum_filter]
          congr 1
          ext e
          simp only [Finset.mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨((hE e).mp h).1, h⟩⟩
        rw [hsw, hfe]; ring
    _ ≤ (2:ℝ)^(1-ℓ) * capacity ν ℓ := mul_le_mul_of_nonneg_left hcap (zpow_pos two_pos _).le

