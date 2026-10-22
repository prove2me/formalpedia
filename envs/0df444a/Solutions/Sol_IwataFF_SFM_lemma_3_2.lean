-- Prove2me | solution 1 for IwataFF.SFM.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T11:58:31.910459+00:00
-- url     : https://prove2.me/submissions/776642c0-b845-44bb-ad55-f72ceefeb377

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic
open IwataFF.SFM

theorem g69g_kmul_le_choose (k j : ℕ) : k * j ≤ (k + j).choose 2 := by
  rw [Nat.choose_two_right]
  apply Nat.le_div_iff_mul_le (by norm_num) |>.mpr
  have hk : k ≤ k * k := Nat.le_mul_self k
  have hj : j ≤ j * j := Nat.le_mul_self j
  rcases Nat.eq_zero_or_pos (k + j) with h | h
  · simp at h; simp [h.1, h.2]
  · have : (k + j) * (k + j - 1) + (k + j) = (k + j) * (k + j) := by
      rw [← Nat.mul_succ]; congr 1; omega
    nlinarith

theorem g69g_skew_sum_zero {α : Type} (X : Finset α) (phi : α → α → ℝ)
    (hskew : ∀ u ∈ X, ∀ v ∈ X, phi u v + phi v u = 0) :
    ∑ v ∈ X, ∑ u ∈ X, phi u v = 0 := by
  have h1 : ∑ v ∈ X, ∑ u ∈ X, phi u v = ∑ v ∈ X, ∑ u ∈ X, phi v u := Finset.sum_comm
  have h2 : ∑ v ∈ X, ∑ u ∈ X, phi u v + ∑ v ∈ X, ∑ u ∈ X, phi v u = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro v hv
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro u hu
    exact hskew u hu v hv
  linarith

theorem solution {α : Type} [DecidableEq α] (V : Finset α) (hV : V.Nonempty)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (x : α → ℝ) (hx : x ∈ basePoly V f) (phi : α → α → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hskew : ∀ u ∈ V, ∀ v ∈ V, phi u v + phi v u = 0)
    (hfeas : ∀ u ∈ V, ∀ v ∈ V, -δ ≤ phi u v ∧ phi u v ≤ δ)
    (X : Finset α) (hX : X ⊆ V) :
    xsum (xneg (fun v => x v - ∑ u ∈ V, phi u v)) V ≤
      f X + ((V.card.choose 2 : ℕ) : ℝ) * δ := by
  set z : α → ℝ := fun v => x v - ∑ u ∈ V, phi u v with hz
  have s1 : xsum (xneg z) V ≤ xsum z X := by
    unfold xsum xneg
    rw [← Finset.sum_sdiff hX]
    have a : ∑ v ∈ V \ X, min 0 (z v) ≤ 0 := Finset.sum_nonpos (fun i _ => min_le_left _ _)
    have b : ∑ v ∈ X, min 0 (z v) ≤ ∑ v ∈ X, z v := Finset.sum_le_sum (fun i _ => min_le_right _ _)
    linarith
  have s2 : xsum z X = xsum x X - ∑ v ∈ X, ∑ u ∈ V, phi u v := by
    unfold xsum; rw [hz]; simp only; rw [Finset.sum_sub_distrib]
  have s3 : xsum x X ≤ f X := hx.2.2 X hX
  have s4 : ∑ v ∈ X, ∑ u ∈ V, phi u v =
      ∑ v ∈ X, ∑ u ∈ X, phi u v + ∑ v ∈ X, ∑ u ∈ V \ X, phi u v := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro v _
    rw [add_comm, Finset.sum_sdiff hX]
  have s5 : ∑ v ∈ X, ∑ u ∈ X, phi u v = 0 :=
    g69g_skew_sum_zero X phi (fun u hu v hv => hskew u (hX hu) v (hX hv))
  have s6 : -(((X.card * (V \ X).card : ℕ) : ℝ) * δ) ≤ ∑ v ∈ X, ∑ u ∈ V \ X, phi u v := by
    have : ∑ v ∈ X, ∑ u ∈ V \ X, (-δ) ≤ ∑ v ∈ X, ∑ u ∈ V \ X, phi u v := by
      apply Finset.sum_le_sum; intro v hv; apply Finset.sum_le_sum; intro u hu
      exact (hfeas u (Finset.sdiff_subset hu) v (hX hv)).1
    simp only [Finset.sum_const, nsmul_eq_mul] at this
    push_cast; linarith
  have s7 : X.card * (V \ X).card ≤ V.card.choose 2 := by
    have := g69g_kmul_le_choose X.card (V \ X).card
    have hc : X.card + (V \ X).card = V.card := by
      rw [add_comm]; exact Finset.card_sdiff_add_card_eq_card hX
    rwa [hc] at this
  have s8 : ((X.card * (V \ X).card : ℕ) : ℝ) * δ ≤ ((V.card.choose 2 : ℕ) : ℝ) * δ := by
    apply mul_le_mul_of_nonneg_right _ hδ.le; exact_mod_cast s7
  linarith
