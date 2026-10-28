-- Prove2me | solution 1 for NetInspect.Rate.lemma_EC_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:49:18.519979+00:00
-- url     : https://prove2.me/submissions/226a4562-8753-4fb9-b479-1c8352ed45dc

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum
import Definitions.Def_NetInspect_Rate_Model

namespace Aux_NetInspect_Rate_lemma_EC_3
open Finset NetInspect.Rate Fin.NatCast

variable {α : Type*} [Fintype α] [DecidableEq α] {n b : ℕ}

theorem cast_inj [NeZero n] {i1 i2 : ℕ} (h1 : i1 < n) (h2 : i2 < n)
    (h : ((i1 : Fin n)) = (i2 : Fin n)) : i1 = i2 := by
  have := congrArg Fin.val h
  rwa [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this

theorem win_eq [NeZero n] (x : Fin n → α) (k : Fin n) :
    window x b k = (range b).image (fun i : ℕ => x (k + (i : Fin n))) := by
  unfold window
  apply Finset.image_congr
  intro i _
  show x _ = x _
  congr 1
  ext
  rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod]

theorem win_card [NeZero n] (x : Fin n → α) (hx : Function.Injective x) (hbn : b ≤ n)
    (k : Fin n) : (window x b k).card = b := by
  rw [win_eq, card_image_of_injOn, card_range]
  intro i1 h1 i2 h2 heq
  have h1' : i1 < b := mem_range.mp h1
  have h2' : i2 < b := mem_range.mp h2
  have := add_left_cancel (hx heq)
  exact cast_inj (by omega) (by omega) this

theorem win_count [NeZero n] (x : Fin n → α) (hx : Function.Injective x) (hbn : b ≤ n)
    (j : Fin n) : (univ.filter fun k : Fin n => x j ∈ window x b k).card = b := by
  have hset : (univ.filter fun k : Fin n => x j ∈ window x b k) =
      (range b).image (fun i : ℕ => j - (i : Fin n)) := by
    ext k
    simp only [mem_filter, mem_univ, true_and, win_eq, mem_image]
    constructor
    · rintro ⟨i, hi, hk⟩
      exact ⟨i, hi, by rw [← hx hk]; abel⟩
    · rintro ⟨i, hi, hk⟩
      exact ⟨i, hi, by rw [← hk]; congr 1; abel⟩
  rw [hset, card_image_of_injOn, card_range]
  intro i1 h1 i2 h2 heq
  have h1' : i1 < b := mem_range.mp h1
  have h2' : i2 < b := mem_range.mp h2
  have : ((i1 : Fin n)) = (i2 : Fin n) := sub_right_injective heq
  exact cast_inj (by omega) (by omega) this

theorem fiber_sum (x : Fin n → α) (P : Finset α → Prop) [DecidablePred P] :
    ∑ X : Act α b, (if P X.1 then (((univ.filter fun k => window x b k = X.1).card : ℕ) : ℝ) else 0)
      = ((univ.filter fun k => P (window x b k)).card : ℝ) := by
  rw [card_eq_sum_card_fiberwise (f := fun k => (⟨window x b k, window_card_le x b k⟩ : Act α b))
    (t := univ) (fun _ _ => mem_coe.mpr (mem_univ _))]
  push_cast
  refine Finset.sum_congr rfl fun X _ => ?_
  split_ifs with hP
  · congr 2
    ext k
    simp only [mem_filter, mem_univ, true_and, Subtype.ext_iff]
    constructor
    · intro h; exact ⟨h ▸ hP, h⟩
    · intro h; exact h.2
  · symm
    norm_cast
    rw [card_eq_zero, filter_eq_empty_iff]
    intro k hk hfk
    simp only [mem_filter, mem_univ, true_and] at hk
    apply hP
    rw [← hfk]; exact hk

theorem mixed (x : Fin n → α) (hn : 0 < n) : BlottoLP.Flow.IsMixed (cycStrat x b) := by
  refine ⟨fun X => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
  unfold cycStrat
  rw [← Finset.sum_div]
  have := fiber_sum (b := b) x (fun _ => True)
  have hu : (univ.filter fun _ : Fin n => True) = univ := by ext; simp
  simp only [if_true] at this
  rw [this, hu, card_univ, Fintype.card_fin, div_self]
  exact_mod_cast hn.ne'

theorem margv [NeZero n] (x : Fin n → α) (hx : Function.Injective x) (hbn : b ≤ n) (j : Fin n) :
    marg (cycStrat x b) (x j) = (b : ℝ) / (n : ℝ) := by
  unfold marg cycStrat
  have h := fiber_sum (b := b) x (fun X => x j ∈ X)
  rw [win_count x hx hbn] at h
  rw [← h, Finset.sum_div]
  refine Finset.sum_congr rfl fun X _ => ?_
  split_ifs <;> simp

end Aux_NetInspect_Rate_lemma_EC_3

open Finset NetInspect.Rate NetInspect.Rate.DetectionModel Aux_NetInspect_Rate_lemma_EC_3 in
theorem solution {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E)
    {n m b1 b2 : ℕ} (x : Fin n → V) (hx : Function.Injective x)
    (y : Fin m → E) (hy : Function.Injective y)
    (hb1 : 1 ≤ b1) (hb1n : b1 ≤ n) (hb2 : 1 ≤ b2) (hb2m : b2 ≤ m) :
    (BlottoLP.Flow.IsMixed (cycStrat x b1) ∧ BlottoLP.Flow.IsMixed (cycStrat y b2)) ∧
    ((∀ k : Fin n, (window x b1 k).card = b1) ∧ (∀ l : Fin m, (window y b2 l).card = b2)) ∧
    ((∀ j : Fin n, marg (cycStrat x b1) (x j) = (b1 : ℝ) / (n : ℝ)) ∧
      (∀ j : Fin m, marg (cycStrat y b2) (y j) = (b2 : ℝ) / (m : ℝ))) ∧
    ((∀ j : Fin n, (univ.filter fun k : Fin n => x j ∈ window x b1 k).card = b1) ∧
      (∀ j : Fin m, (univ.filter fun l : Fin m => y j ∈ window y b2 l).card = b2)) ∧
    (∀ e : E, (G.F (univ.image x) {e} : ℝ) ≤
      (1 / (b1 : ℝ)) * ∑ k : Fin n, (G.F (window x b1 k) {e} : ℝ)) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : NeZero m := ⟨by omega⟩
  refine ⟨⟨mixed x (by omega), mixed y (by omega)⟩, ⟨win_card x hx hb1n, win_card y hy hb2m⟩,
    ⟨margv x hx hb1n, margv y hy hb2m⟩, ⟨win_count x hx hb1n, win_count y hy hb2m⟩, ?_⟩
  intro e
  have hle1 : ∀ S : Finset V, G.F S {e} ≤ 1 := by
    intro S
    unfold DetectionModel.F
    exact (card_le_card inter_subset_right).trans (by simp)
  have hb1R : (0 : ℝ) < b1 := by exact_mod_cast hb1
  by_cases he : e ∈ G.CS (univ.image x)
  · obtain ⟨v, hv, hev⟩ := mem_biUnion.mp he
    obtain ⟨j, -, rfl⟩ := mem_image.mp hv
    have hone : ∀ k ∈ univ.filter (fun k : Fin n => x j ∈ window x b1 k),
        (G.F (window x b1 k) {e} : ℝ) = 1 := by
      intro k hk
      simp only [mem_filter, mem_univ, true_and] at hk
      have : e ∈ G.CS (window x b1 k) := mem_biUnion.mpr ⟨x j, hk, hev⟩
      unfold DetectionModel.F
      rw [inter_singleton_of_mem this, card_singleton, Nat.cast_one]
    have hsum : (b1 : ℝ) ≤ ∑ k : Fin n, (G.F (window x b1 k) {e} : ℝ) := by
      calc (b1 : ℝ) = ∑ k ∈ univ.filter (fun k : Fin n => x j ∈ window x b1 k),
            (G.F (window x b1 k) {e} : ℝ) := by
            rw [sum_congr rfl hone, sum_const, win_count x hx hb1n, nsmul_eq_mul, mul_one]
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun _ _ _ => Nat.cast_nonneg _)
    have h1 : (G.F (univ.image x) {e} : ℝ) ≤ 1 := by exact_mod_cast hle1 _
    calc (G.F (univ.image x) {e} : ℝ) ≤ 1 := h1
      _ = (1 / (b1 : ℝ)) * b1 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  · have : G.F (univ.image x) {e} = 0 := by
      unfold DetectionModel.F
      rw [inter_singleton_of_notMem he, card_empty]
    rw [this, Nat.cast_zero]
    exact mul_nonneg (by positivity) (sum_nonneg fun _ _ => Nat.cast_nonneg _)
