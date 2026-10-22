-- Prove2me | solution 1 for HLambdaG.Main.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:10:42.729956+00:00
-- url     : https://prove2.me/submissions/e79fe2f7-fd9e-40f6-9ff0-081a8384e273

import Mathlib
import Definitions.Def_HLambdaG_Main_Setting

set_option autoImplicit false
open scoped NNReal
open HLambdaG.Main Filter Topology

lemma hlg_inv_lt (τ : TimeChange) (t s : ℝ≥0) (h : inv τ t < s) : t < τ.T s := by
  have hne : ({s | t < τ.T s} : Set ℝ≥0).Nonempty := by
    have := (τ.tendsto.eventually (eventually_gt_atTop t)).and (eventually_ge_atTop 0)
    obtain ⟨s, hs, _⟩ := this.exists
    exact ⟨s, hs⟩
  obtain ⟨a, haA, has⟩ := exists_lt_of_csInf_lt hne h
  exact lt_of_lt_of_le haA (τ.mono has.le)

lemma hlg_inv_le (τ : TimeChange) (t s : ℝ≥0) (h : t < τ.T s) : inv τ t ≤ s :=
  csInf_le (OrderBot.bddBelow _) h

lemma hlg_le_inv (τ : TimeChange) (s : ℝ≥0) : s ≤ inv τ (τ.T s) := by
  by_contra hlt
  push_neg at hlt
  exact lt_irrefl _ (hlg_inv_lt τ (τ.T s) s hlt)

lemma hlg_A (τ : TimeChange) (c : ℝ) (hc : 0 < c) (s0 : ℝ≥0)
    (hT : ∀ s : ℝ≥0, s0 ≤ s → (τ.T s : ℝ) < (s : ℝ) / c) (t : ℝ≥0) (ht : (s0 : ℝ) < c * t) :
    c * (t : ℝ) ≤ (inv τ t : ℝ) := by
  by_contra hcon
  push_neg at hcon
  have hnn : 0 ≤ c * (t : ℝ) := mul_nonneg hc.le t.coe_nonneg
  set U : ℝ≥0 := (c * t).toNNReal with hU
  have hUr : (U : ℝ) = c * t := Real.coe_toNNReal _ hnn
  have h1 : inv τ t < U := by rw [← NNReal.coe_lt_coe, hUr]; exact hcon
  have h2 : s0 < U := by rw [← NNReal.coe_lt_coe, hUr]; exact ht
  obtain ⟨s, hs1, hs2⟩ := exists_between (max_lt h1 h2)
  have hs_inv : inv τ t < s := lt_of_le_of_lt (le_max_left _ _) hs1
  have hs_s0 : s0 ≤ s := (lt_of_le_of_lt (le_max_right _ _) hs1).le
  have hTs : t < τ.T s := hlg_inv_lt τ t s hs_inv
  have h3 := hT s hs_s0
  have hsU : (s : ℝ) < c * t := by rw [← hUr]; exact_mod_cast hs2
  have h4 : (τ.T s : ℝ) < t := by
    calc (τ.T s : ℝ) < (s : ℝ) / c := h3
      _ < c * t / c := by gcongr
      _ = t := by field_simp
  have h5 := NNReal.coe_lt_coe.2 hTs
  linarith

lemma hlg_B (τ : TimeChange) (c : ℝ) (hc : 0 < c) (s0 : ℝ≥0)
    (hT : ∀ s : ℝ≥0, s0 ≤ s → (s : ℝ) / c < (τ.T s : ℝ)) (t : ℝ≥0) (ht : (s0 : ℝ) < c * t) :
    (inv τ t : ℝ) ≤ c * (t : ℝ) := by
  by_contra hcon
  push_neg at hcon
  have hnn : 0 ≤ c * (t : ℝ) := mul_nonneg hc.le t.coe_nonneg
  set U : ℝ≥0 := (c * t).toNNReal with hU
  have hUr : (U : ℝ) = c * t := Real.coe_toNNReal _ hnn
  have h1 : U < inv τ t := by rw [← NNReal.coe_lt_coe, hUr]; exact hcon
  obtain ⟨s, hs1, hs2⟩ := exists_between h1
  have hsU : c * (t : ℝ) < (s : ℝ) := by rw [← hUr]; exact_mod_cast hs1
  have hs0 : s0 ≤ s := by
    have : (s0 : ℝ) < s := by linarith
    exact_mod_cast this.le
  have h3 := hT s hs0
  have h4 : (t : ℝ) < (τ.T s : ℝ) := by
    have : (t : ℝ) < (s : ℝ) / c := by rw [lt_div_iff₀ hc]; linarith
    linarith
  have h5 : t < τ.T s := by exact_mod_cast h4
  have h6 := hlg_inv_le τ t s h5
  exact absurd hs2 (not_lt.2 h6)

lemma hlg_C (τ : TimeChange) (c : ℝ) (t0 : ℝ≥0)
    (hS : ∀ t : ℝ≥0, t0 ≤ t → (inv τ t : ℝ) < c * t) (s : ℝ≥0) (hs : t0 ≤ τ.T s) :
    (s : ℝ) < c * (τ.T s : ℝ) :=
  lt_of_le_of_lt (NNReal.coe_le_coe.2 (hlg_le_inv τ s)) (hS (τ.T s) hs)

lemma hlg_D (τ : TimeChange) (c : ℝ) (hc : 0 < c) (t0 : ℝ≥0)
    (hS : ∀ t : ℝ≥0, t0 ≤ t → c * (t : ℝ) < (inv τ t : ℝ)) (s : ℝ≥0)
    (hs : (t0 : ℝ) ≤ (s : ℝ) / c) : (τ.T s : ℝ) ≤ (s : ℝ) / c := by
  by_contra hcon
  push_neg at hcon
  have hnn : 0 ≤ (s : ℝ) / c := div_nonneg s.coe_nonneg hc.le
  set V : ℝ≥0 := ((s : ℝ) / c).toNNReal with hV
  have hVr : (V : ℝ) = (s : ℝ) / c := Real.coe_toNNReal _ hnn
  have h1 : V < τ.T s := by rw [← NNReal.coe_lt_coe, hVr]; exact hcon
  obtain ⟨t, ht1, ht2⟩ := exists_between h1
  have ht1' : (s : ℝ) / c < (t : ℝ) := by rw [← hVr]; exact_mod_cast ht1
  have ht0 : t0 ≤ t := by
    have : (t0 : ℝ) < t := by linarith
    exact_mod_cast this.le
  have h2 := hS t ht0
  have h3 := hlg_inv_le τ t s ht2
  have h4 : (s : ℝ) < c * t := by
    have := (div_lt_iff₀ hc).1 ht1'
    linarith
  have h5 : (inv τ t : ℝ) ≤ s := NNReal.coe_le_coe.2 h3
  linarith

theorem solution (τ : TimeChange) (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun t : ℝ≥0 => (inv τ t : ℝ) / (t : ℝ)) atTop (𝓝 lam) ↔
      Tendsto (fun s : ℝ≥0 => (τ.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹) := by
  constructor
  · intro hS
    rw [tendsto_order]
    constructor
    · intro a' ha'
      set c' : ℝ := (max a' 0 + lam⁻¹) / 2 with hc'
      have hlt : max a' 0 < lam⁻¹ := max_lt ha' (inv_pos.2 hlam)
      have hc'1 : max a' 0 < c' := by rw [hc']; linarith
      have hc'2 : c' < lam⁻¹ := by rw [hc']; linarith
      have hc'pos : 0 < c' := lt_of_le_of_lt (le_max_right _ _) hc'1
      have hgt : lam < 1 / c' := by
        rw [lt_div_iff₀ hc'pos]
        have := mul_lt_mul_of_pos_left hc'2 hlam
        rwa [mul_inv_cancel₀ hlam.ne'] at this
      obtain ⟨t0, ht0⟩ := eventually_atTop.1 ((tendsto_order.1 hS).2 (1 / c') hgt)
      have hSc : ∀ t : ℝ≥0, max t0 1 ≤ t → (inv τ t : ℝ) < (1 / c') * t := by
        intro t ht
        have h1 := ht0 t (le_trans (le_max_left _ _) ht)
        have h1' : (1 : ℝ≥0) ≤ t := le_trans (le_max_right _ _) ht
        have tpos : 0 < (t : ℝ) := lt_of_lt_of_le one_pos (by exact_mod_cast h1')
        rwa [div_lt_iff₀ tpos] at h1
      have hev := τ.tendsto.eventually (eventually_ge_atTop (max t0 1))
      filter_upwards [hev, eventually_ge_atTop (1 : ℝ≥0)] with s hs hs1
      have hspos : 0 < (s : ℝ) := lt_of_lt_of_le one_pos (by exact_mod_cast hs1)
      have h2 := hlg_C τ (1 / c') (max t0 1) hSc s hs
      have h3 : c' * (s : ℝ) < (τ.T s : ℝ) := by
        rw [one_div, ← div_eq_inv_mul, lt_div_iff₀ hc'pos] at h2
        linarith
      rw [lt_div_iff₀ hspos]
      have : a' < c' := lt_of_le_of_lt (le_max_left _ _) hc'1
      nlinarith
    · intro a' ha'
      set c' : ℝ := (lam⁻¹ + a') / 2 with hc'
      have hlt : lam⁻¹ < a' := ha'
      have hc'1 : lam⁻¹ < c' := by rw [hc']; linarith
      have hc'2 : c' < a' := by rw [hc']; linarith
      have hc'pos : 0 < c' := lt_trans (inv_pos.2 hlam) hc'1
      have hlt2 : 1 / c' < lam := by
        rw [div_lt_iff₀ hc'pos]
        have := mul_lt_mul_of_pos_left hc'1 hlam
        rw [mul_inv_cancel₀ hlam.ne'] at this
        linarith
      obtain ⟨t0, ht0⟩ := eventually_atTop.1 ((tendsto_order.1 hS).1 (1 / c') hlt2)
      have hSc : ∀ t : ℝ≥0, max t0 1 ≤ t → (1 / c') * (t : ℝ) < (inv τ t : ℝ) := by
        intro t ht
        have h1 := ht0 t (le_trans (le_max_left _ _) ht)
        have h1' : (1 : ℝ≥0) ≤ t := le_trans (le_max_right _ _) ht
        have tpos : 0 < (t : ℝ) := lt_of_lt_of_le one_pos (by exact_mod_cast h1')
        rwa [lt_div_iff₀ tpos] at h1
      -- s with c' s ≥ max t0 1
      have hev : ∀ᶠ s : ℝ≥0 in atTop, (max t0 1 : ℝ≥0) ≤ (c' * (s : ℝ)).toNNReal := by
        have : ∀ᶠ s : ℝ≥0 in atTop, ((max t0 1 : ℝ≥0) : ℝ) / c' ≤ (s : ℝ) := by
          filter_upwards [eventually_ge_atTop ((max t0 1 : ℝ≥0) / c'.toNNReal)] with s hs
          have : ((max t0 1 : ℝ≥0) : ℝ) / c' = (((max t0 1 : ℝ≥0) / c'.toNNReal : ℝ≥0) : ℝ) := by
            rw [NNReal.coe_div, Real.coe_toNNReal _ hc'pos.le]
          rw [this]; exact_mod_cast hs
        filter_upwards [this] with s hs
        have : ((max t0 1 : ℝ≥0) : ℝ) ≤ c' * (s : ℝ) := by
          rw [div_le_iff₀ hc'pos] at hs; linarith
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (mul_nonneg hc'pos.le s.coe_nonneg)]
        exact this
      filter_upwards [hev, eventually_ge_atTop (1 : ℝ≥0)] with s hs hs1
      have hspos : 0 < (s : ℝ) := lt_of_lt_of_le one_pos (by exact_mod_cast hs1)
      have hd := hlg_D τ (1 / c') (by positivity) (max t0 1) hSc s (by
        have : ((max t0 1 : ℝ≥0) : ℝ) ≤ c' * (s : ℝ) := by
          rw [← Real.coe_toNNReal (c' * (s : ℝ)) (mul_nonneg hc'pos.le s.coe_nonneg)]
          exact_mod_cast hs
        rw [div_div_eq_mul_div, div_one]
        linarith)
      rw [div_div_eq_mul_div, div_one] at hd
      rw [div_lt_iff₀ hspos]
      nlinarith
  · intro hT
    rw [tendsto_order]
    constructor
    · intro a' ha'
      set c : ℝ := (max a' 0 + lam) / 2 with hc
      have hlt : max a' 0 < lam := max_lt ha' hlam
      have hc1 : max a' 0 < c := by rw [hc]; linarith
      have hc2 : c < lam := by rw [hc]; linarith
      have hcpos : 0 < c := lt_of_le_of_lt (le_max_right _ _) hc1
      have hgt : lam⁻¹ < 1 / c := by
        rw [one_div]; exact inv_strictAnti₀ hcpos hc2
      obtain ⟨s0, hs0⟩ := eventually_atTop.1 ((tendsto_order.1 hT).2 (1 / c) hgt)
      have hTc : ∀ s : ℝ≥0, max s0 1 ≤ s → (τ.T s : ℝ) < (s : ℝ) / c := by
        intro s hs
        have h1 := hs0 s (le_trans (le_max_left _ _) hs)
        have h1' : (1 : ℝ≥0) ≤ s := le_trans (le_max_right _ _) hs
        have spos : 0 < (s : ℝ) := lt_of_lt_of_le one_pos (by exact_mod_cast h1')
        rw [div_lt_iff₀ spos] at h1
        rw [div_eq_mul_inv, mul_comm, ← one_div]
        linarith [h1]
      have hev : ∀ᶠ t : ℝ≥0 in atTop, ((max s0 1 : ℝ≥0) : ℝ) < c * (t : ℝ) := by
        have : ∀ᶠ t : ℝ≥0 in atTop, ((max s0 1 : ℝ≥0) : ℝ) / c < (t : ℝ) := by
          filter_upwards [eventually_gt_atTop ((max s0 1 : ℝ≥0) / c.toNNReal)] with t ht
          have : ((max s0 1 : ℝ≥0) : ℝ) / c = (((max s0 1 : ℝ≥0) / c.toNNReal : ℝ≥0) : ℝ) := by
            rw [NNReal.coe_div, Real.coe_toNNReal _ hcpos.le]
          rw [this]; exact_mod_cast ht
        filter_upwards [this] with t ht
        rw [div_lt_iff₀ hcpos] at ht; linarith
      filter_upwards [hev, eventually_gt_atTop (0 : ℝ≥0)] with t ht htpos
      have tpos : 0 < (t : ℝ) := by exact_mod_cast htpos
      have h2 := hlg_A τ c hcpos (max s0 1) hTc t ht
      rw [lt_div_iff₀ tpos]
      have : a' < c := lt_of_le_of_lt (le_max_left _ _) hc1
      nlinarith
    · intro a' ha'
      set c : ℝ := (lam + a') / 2 with hc
      have hc1 : lam < c := by rw [hc]; linarith
      have hc2 : c < a' := by rw [hc]; linarith
      have hcpos : 0 < c := lt_trans hlam hc1
      have hlt2 : 1 / c < lam⁻¹ := by
        rw [one_div]; exact inv_strictAnti₀ hlam hc1
      obtain ⟨s0, hs0⟩ := eventually_atTop.1 ((tendsto_order.1 hT).1 (1 / c) hlt2)
      have hTc : ∀ s : ℝ≥0, max s0 1 ≤ s → (s : ℝ) / c < (τ.T s : ℝ) := by
        intro s hs
        have h1 := hs0 s (le_trans (le_max_left _ _) hs)
        have h1' : (1 : ℝ≥0) ≤ s := le_trans (le_max_right _ _) hs
        have spos : 0 < (s : ℝ) := lt_of_lt_of_le one_pos (by exact_mod_cast h1')
        rw [lt_div_iff₀ spos] at h1
        rw [div_eq_mul_inv, mul_comm, ← one_div]
        linarith [h1]
      have hev : ∀ᶠ t : ℝ≥0 in atTop, ((max s0 1 : ℝ≥0) : ℝ) < c * (t : ℝ) := by
        have : ∀ᶠ t : ℝ≥0 in atTop, ((max s0 1 : ℝ≥0) : ℝ) / c < (t : ℝ) := by
          filter_upwards [eventually_gt_atTop ((max s0 1 : ℝ≥0) / c.toNNReal)] with t ht
          have : ((max s0 1 : ℝ≥0) : ℝ) / c = (((max s0 1 : ℝ≥0) / c.toNNReal : ℝ≥0) : ℝ) := by
            rw [NNReal.coe_div, Real.coe_toNNReal _ hcpos.le]
          rw [this]; exact_mod_cast ht
        filter_upwards [this] with t ht
        rw [div_lt_iff₀ hcpos] at ht; linarith
      filter_upwards [hev, eventually_gt_atTop (0 : ℝ≥0)] with t ht htpos
      have tpos : 0 < (t : ℝ) := by exact_mod_cast htpos
      have h2 := hlg_B τ c hcpos (max s0 1) hTc t ht
      rw [div_lt_iff₀ tpos]
      nlinarith
