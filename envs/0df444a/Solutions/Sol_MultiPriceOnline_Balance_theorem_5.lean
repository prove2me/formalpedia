-- Prove2me | solution 1 for MultiPriceOnline.Balance.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:52:35.049554+00:00
-- url     : https://prove2.me/submissions/eaacfd28-4987-41e1-b070-fab51f4b08fc

import Mathlib
import Definitions.Def_MultiPriceOnline_Balance_PriceSet
import Definitions.Def_MultiPriceOnline_Balance_Procedure

open MultiPriceOnline.Balance Finset MeasureTheory

private lemma r_pos_of_priceSet {m : ℕ} {r : ℕ → ℝ} (hr : IsPriceSet m r) :
    ∀ j, 1 ≤ j → j ≤ m → 0 < r j := by
  intro j hj1 hjm
  induction j with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le hj1 with h | h
    · rw [← h]; exact hr.1
    · have hk_pos : 0 < r k := ih (by omega) (by omega)
      have hlt : r k < r (k + 1) := hr.2 k (by omega) (by omega)
      linarith

private lemma r_strictMono_of_priceSet {m : ℕ} {r : ℕ → ℝ} (hr : IsPriceSet m r) :
    ∀ j₁ j₂, 1 ≤ j₁ → j₁ < j₂ → j₂ ≤ m → r j₁ < r j₂ := by
  intro j₁ j₂ hj1 hlt hj2m
  induction j₂ with
  | zero => omega
  | succ n ih =>
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ hlt) with rfl | hlt'
    · exact hr.2 j₁ hj1 (by omega)
    · exact lt_trans (ih hlt' (by omega)) (hr.2 n (by omega) (by omega))

private lemma pr_diff_pos {m : ℕ} {r : ℕ → ℝ} (hr : IsPriceSet m r) :
    ∀ j, 1 ≤ j → j ≤ m → 0 < pr r j - pr r (j - 1) := by
  intro j hj1 hjm
  have hrj : pr r j = r j := if_neg (by omega)
  rw [hrj]
  rcases eq_or_lt_of_le hj1 with h | h
  · rw [← h]
    change 0 < r 1 - pr r 0
    unfold pr
    simp [hr.1]
  · have hrj1 : pr r (j - 1) = r (j - 1) := if_neg (by omega)
    rw [hrj1]
    have hlt := hr.2 (j - 1) (by omega) (by omega)
    have heq : j - 1 + 1 = j := by omega
    rw [heq] at hlt
    linarith

private lemma Fval_bounds {m : ℕ} (hm : 1 ≤ m) {r α : ℕ → ℝ} (hα : IsBookingLimits m r α) :
    0 < Fval α ∧ Fval α < 1 := by
  unfold Fval
  have hα1 : 0 < α 1 := hα.1 1 le_rfl hm
  have hexp_lt : Real.exp (-α 1) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hexp_pos : 0 < Real.exp (-α 1) := Real.exp_pos _
  constructor <;> linarith

private lemma booking_identity {m : ℕ} {r α : ℕ → ℝ} (hr : IsPriceSet m r)
    (hα : IsBookingLimits m r α) {j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    (pr r j - pr r (j - 1)) / (1 - Real.exp (-α j)) = r j / Fval α := by
  have hαj : 0 < α j := hα.1 j hj1 hjm
  have h1exp_pos : 0 < 1 - Real.exp (-α j) := by
    have : Real.exp (-α j) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hF_pos : 0 < Fval α := (Fval_bounds (le_trans hj1 hjm) hα).1
  have hrj_pos : 0 < r j := r_pos_of_priceSet hr j hj1 hjm
  have hrj_eq : pr r j = r j := if_neg (by omega)
  rw [hrj_eq]
  rcases eq_or_lt_of_le hj1 with h | h
  · rw [← h]
    change (r 1 - pr r 0) / (1 - Real.exp (-α 1)) = r 1 / Fval α
    have hpr0 : pr r 0 = 0 := rfl
    rw [hpr0, sub_zero]
    rfl
  · have hj2 : 2 ≤ j := by omega
    have hrj1_eq : pr r (j - 1) = r (j - 1) := if_neg (by omega)
    rw [hrj1_eq]
    have h7 := hα.2.2 j hj2 hjm
    change Fval α = (1 - Real.exp (-α j)) / (1 - r (j - 1) / r j) at h7
    have hlt : r (j - 1) < r j := by
      have := hr.2 (j - 1) (by omega) (by omega)
      rwa [Nat.sub_add_cancel hj1] at this
    have hratio_pos : 0 < 1 - r (j - 1) / r j := by
      rw [sub_pos, div_lt_one hrj_pos]
      exact hlt
    have h7' : 1 - Real.exp (-α j) = Fval α * (1 - r (j - 1) / r j) := by
      rw [h7, div_mul_cancel₀ _ (ne_of_gt hratio_pos)]
    have hdiff : r j - r (j - 1) = r j * (1 - r (j - 1) / r j) := by
      calc
        r j - r (j - 1) = r j - r (j - 1) / r j * r j := by
          rw [div_mul_cancel₀ _ (ne_of_gt hrj_pos)]
        _ = r j * (1 - r (j - 1) / r j) := by ring
    rw [hdiff, h7', mul_div_mul_right _ _ (ne_of_gt hratio_pos)]

private lemma booking_identity_exp {m : ℕ} {r α : ℕ → ℝ} (hr : IsPriceSet m r)
    (hα : IsBookingLimits m r α) {j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    (pr r j - pr r (j - 1)) / (Real.exp (α j) - 1) = (r j / Fval α) * Real.exp (-α j) := by
  have h1 : Real.exp (α j) - 1 = (1 - Real.exp (-α j)) * Real.exp (α j) := by
    rw [sub_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [h1, div_mul_eq_div_div, booking_identity hr hα hj1 hjm, Real.exp_neg]
  exact div_eq_mul_inv (r j / Fval α) (Real.exp (α j))

private lemma r_pred_le_mul_exp {m : ℕ} {r α : ℕ → ℝ} (hr : IsPriceSet m r)
    (hα : IsBookingLimits m r α) {j : ℕ} (hj2 : 2 ≤ j) (hjm : j ≤ m) :
    r (j - 1) ≤ r j * Real.exp (-α j) := by
  have hj1 : 1 ≤ j := by omega
  have hrj_pos : 0 < r j := r_pos_of_priceSet hr j hj1 hjm
  have hlt : r (j - 1) < r j := by
    have := hr.2 (j - 1) (by omega) (by omega)
    rwa [Nat.sub_add_cancel hj1] at this
  have hratio_pos : 0 < 1 - r (j - 1) / r j := by
    rw [sub_pos, div_lt_one hrj_pos]
    exact hlt
  have h7 := hα.2.2 j hj2 hjm
  change Fval α = (1 - Real.exp (-α j)) / (1 - r (j - 1) / r j) at h7
  have h7' : 1 - Real.exp (-α j) = Fval α * (1 - r (j - 1) / r j) := by
    rw [h7, div_mul_cancel₀ _ (ne_of_gt hratio_pos)]
  have hF_lt1 : Fval α < 1 := (Fval_bounds (le_trans hj1 hjm) hα).2
  have hle : 1 - Real.exp (-α j) ≤ 1 - r (j - 1) / r j := by
    nlinarith
  have hle2 : r (j - 1) / r j ≤ Real.exp (-α j) := by linarith
  have := mul_le_mul_of_nonneg_right hle2 (le_of_lt hrj_pos)
  rwa [div_mul_cancel₀ _ (ne_of_gt hrj_pos), mul_comm (Real.exp (-α j))] at this

private lemma Lsum_zero (α : ℕ → ℝ) : Lsum α 0 = 0 := by
  unfold Lsum
  simp

private lemma Lsum_step (α : ℕ → ℝ) {j : ℕ} (hj : 1 ≤ j) :
    Lsum α j - Lsum α (j - 1) = α j := by
  unfold Lsum
  have h : Icc 1 j = insert j (Icc 1 (j - 1)) := by
    ext x
    simp only [mem_Icc, mem_insert]
    omega
  have hnotmem : j ∉ Icc 1 (j - 1) := by
    simp only [mem_Icc]
    omega
  rw [h, sum_insert hnotmem]
  ring

private lemma Lsum_mono {m : ℕ} {r α : ℕ → ℝ} (hα : IsBookingLimits m r α) :
    ∀ j₁ j₂, j₁ ≤ j₂ → j₂ ≤ m → Lsum α j₁ ≤ Lsum α j₂ := by
  intro j₁ j₂ h12 h2m
  unfold Lsum
  apply sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [mem_Icc] at hx ⊢
    exact ⟨hx.1, le_trans hx.2 h12⟩
  · intro x hx _
    rw [mem_Icc] at hx
    exact le_of_lt (hα.1 x hx.1 (le_trans hx.2 h2m))

private lemma Lsum_bounds {m : ℕ} {r α : ℕ → ℝ} (hα : IsBookingLimits m r α)
    {j : ℕ} (hjm : j ≤ m) : 0 ≤ Lsum α j ∧ Lsum α j ≤ 1 := by
  constructor
  · rw [← Lsum_zero α]
    exact Lsum_mono hα 0 j (Nat.zero_le j) hjm
  · rw [← hα.2.1]
    exact Lsum_mono hα j m hjm le_rfl

private noncomputable def rd (x W : ℝ) : ℕ :=
  ⌊x⌋₊ + if W < x - ⌊x⌋₊ then 1 else 0

private lemma rd_le_k {k : ℕ} {x W : ℝ} (hx0 : 0 ≤ x) (hxk : x ≤ k) (hW0 : 0 ≤ W) :
    rd x W ≤ k := by
  unfold rd
  have hfl : ⌊x⌋₊ ≤ k := Nat.floor_le_of_le hxk
  rcases eq_or_lt_of_le hfl with heq | hlt
  · have hxk_ge : (k : ℝ) ≤ x := by
      rw [← heq]
      exact Nat.floor_le hx0
    have hxk_eq : x = k := le_antisymm hxk hxk_ge
    rw [heq, hxk_eq, sub_self, if_neg (not_lt.mpr hW0), add_zero]
  · split_ifs <;> omega

private lemma rd_mono {x y W : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) :
    rd x W ≤ rd y W := by
  unfold rd
  have hfl : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hxy
  rcases eq_or_lt_of_le hfl with heq | hlt
  · rw [heq]
    split_ifs with h1 h2
    · omega
    · exfalso; apply h2; linarith
    · omega
    · omega
  · split_ifs <;> omega

private lemma rd_bounds {x W : ℝ} (hx0 : 0 ≤ x) (hW0 : 0 ≤ W) (hW1 : W ≤ 1) :
    x - W ≤ (rd x W : ℝ) ∧ (rd x W : ℝ) ≤ x + 1 - W := by
  unfold rd
  have hfl1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hfl2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  split_ifs with h
  · push_cast
    constructor <;> linarith
  · push_cast
    constructor <;> linarith

private lemma def3Config_eq_rd (k m : ℕ) {r α : ℕ → ℝ} (hα : IsBookingLimits m r α)
    {W : ℝ} (hW0 : 0 ≤ W) (j : Fin (m + 1)) :
    (def3Config k m α W j : ℕ) = rd (Lsum α j.val * k) W := by
  unfold def3Config rd
  dsimp
  have hL := Lsum_bounds hα (Nat.le_of_lt_succ j.isLt)
  have hx0 : 0 ≤ Lsum α j.val * k := mul_nonneg hL.1 (Nat.cast_nonneg k)
  have hxk : Lsum α j.val * k ≤ k := by
    calc
      Lsum α j.val * k ≤ 1 * (k : ℝ) := mul_le_mul_of_nonneg_right hL.2 (Nat.cast_nonneg k)
      _ = k := one_mul _
  exact min_eq_right (rd_le_k hx0 hxk hW0)

private lemma cv_def3Config_eq_rd (k m : ℕ) {r α : ℕ → ℝ} (hα : IsBookingLimits m r α)
    {W : ℝ} (hW0 : 0 ≤ W) {j : ℕ} (hjm : j ≤ m) :
    cv (def3Config k m α W) j = rd (Lsum α j * k) W := by
  unfold cv
  have hj_lt : j < m + 1 := by omega
  rw [dif_pos hj_lt]
  exact def3Config_eq_rd k m hα hW0 ⟨j, hj_lt⟩

private lemma isConfig_def3Config (k m : ℕ) {r α : ℕ → ℝ} (hα : IsBookingLimits m r α)
    {W : ℝ} (hW0 : 0 ≤ W) : IsConfig (def3Config k m α W) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [def3Config_eq_rd k m hα hW0 0]
    unfold rd
    change ⌊Lsum α 0 * (k : ℝ)⌋₊ + (if W < Lsum α 0 * (k : ℝ) - ⌊Lsum α 0 * (k : ℝ)⌋₊ then 1 else 0) = 0
    rw [Lsum_zero, zero_mul, Nat.floor_zero, Nat.cast_zero, sub_zero, if_neg (not_lt.mpr hW0), add_zero]
  · rw [def3Config_eq_rd k m hα hW0 (Fin.last m)]
    unfold rd
    change ⌊Lsum α m * (k : ℝ)⌋₊ + (if W < Lsum α m * (k : ℝ) - ⌊Lsum α m * (k : ℝ)⌋₊ then 1 else 0) = k
    have hLm : Lsum α m = 1 := hα.2.1
    rw [hLm, one_mul, Nat.floor_natCast, sub_self, if_neg (not_lt.mpr hW0), add_zero]
  · intro j₁ j₂ h12
    rw [Fin.le_iff_val_le_val] at h12 ⊢
    rw [def3Config_eq_rd k m hα hW0 j₁, def3Config_eq_rd k m hα hW0 j₂]
    have hL1 := Lsum_bounds hα (Nat.le_of_lt_succ j₁.isLt)
    have hL12 := Lsum_mono hα j₁.val j₂.val h12 (Nat.le_of_lt_succ j₂.isLt)
    exact rd_mono (mul_nonneg hL1.1 (Nat.cast_nonneg k))
      (mul_le_mul_of_nonneg_right hL12 (Nat.cast_nonneg k))

private lemma cv_zero_of_isConfig {k m : ℕ} {c : Config k m} (hc : IsConfig c) :
    cv c 0 = 0 := by
  unfold cv
  rw [dif_pos (Nat.zero_lt_succ m)]
  exact hc.1

private lemma cv_m_of_isConfig {k m : ℕ} {c : Config k m} (hc : IsConfig c) :
    cv c m = k := by
  unfold cv
  rw [dif_pos (Nat.lt_succ_self m)]
  exact hc.2.1

private lemma cv_le_k_all {k m : ℕ} (c : Config k m) (j : ℕ) : cv c j ≤ k := by
  unfold cv
  split_ifs with h
  · exact Nat.le_of_lt_succ (c ⟨j, h⟩).isLt
  · exact le_rfl

private lemma cv_mono_of_isConfig {k m : ℕ} {c : Config k m} (hc : IsConfig c) :
    ∀ j₁ j₂, j₁ ≤ j₂ → cv c j₁ ≤ cv c j₂ := by
  intro j₁ j₂ h12
  by_cases h2 : j₂ < m + 1
  · have h1 : j₁ < m + 1 := lt_of_le_of_lt h12 h2
    unfold cv
    rw [dif_pos h1, dif_pos h2]
    exact hc.2.2 (Fin.le_iff_val_le_val.mpr h12)
  · have hcv2 : cv c j₂ = k := by unfold cv; exact dif_neg h2
    rw [hcv2]
    exact cv_le_k_all c j₁

private lemma filter_antitone_eq_Icc (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ j₁ j₂, 1 ≤ j₁ → j₁ ≤ j₂ → P j₂ → P j₁) :
    ∀ n, (Icc 1 n).filter P = Icc 1 ((Icc 1 n).filter P).card := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hIcc : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    have hnotmem : n + 1 ∉ Icc 1 n := by simp only [mem_Icc]; omega
    by_cases hn1 : P (n + 1)
    · have hall : (Icc 1 (n + 1)).filter P = Icc 1 (n + 1) := by
        rw [filter_eq_self]
        intro x hx
        rw [mem_Icc] at hx
        exact hP x (n + 1) hx.1 hx.2 hn1
      rw [hall, Nat.card_Icc]
      have : n + 1 + 1 - 1 = n + 1 := by omega
      rw [this]
    · rw [hIcc, filter_insert, if_neg hn1]
      exact ih

private lemma ellTilde_filter_eq {k m : ℕ} {c : Config k m} (hc : IsConfig c) (N : ℕ) :
    (Icc 1 (m - 1)).filter (fun j => cv c j ≤ N) = Icc 1 (ellTilde c N - 1) := by
  have hanti : ∀ j₁ j₂, 1 ≤ j₁ → j₁ ≤ j₂ → cv c j₂ ≤ N → cv c j₁ ≤ N :=
    fun j₁ j₂ _ h12 h2 => le_trans (cv_mono_of_isConfig hc j₁ j₂ h12) h2
  have h := filter_antitone_eq_Icc (fun j => cv c j ≤ N) hanti (m - 1)
  have hcard : ellTilde c N - 1 = ((Icc 1 (m - 1)).filter (fun j => cv c j ≤ N)).card := by
    unfold ellTilde
    omega
  rw [hcard]
  exact h

private lemma ellTilde_bounds {k m : ℕ} (hm : 1 ≤ m) (c : Config k m) (N : ℕ) :
    1 ≤ ellTilde c N ∧ ellTilde c N ≤ m := by
  unfold ellTilde
  have hsub : ((Icc 1 (m - 1)).filter (fun j => cv c j ≤ N)).card ≤ (Icc 1 (m - 1)).card :=
    card_filter_le _ _
  rw [Nat.card_Icc] at hsub
  omega

private lemma ellTilde_spec {k m : ℕ} (hm : 1 ≤ m) {c : Config k m} (hc : IsConfig c)
    {N : ℕ} (hNk : N ≤ k) :
    (∀ j, 1 ≤ j → j ≤ ellTilde c N - 1 → cv c j ≤ N) ∧
    cv c (ellTilde c N - 1) ≤ N ∧
    N ≤ cv c (ellTilde c N) ∧
    (∀ j, ellTilde c N ≤ j → j ≤ m → N ≤ cv c j) ∧
    (N < k → N < cv c (ellTilde c N)) ∧
    (∀ j, 1 ≤ j → j ≤ m → N < cv c j → ellTilde c N ≤ j) := by
  have h_bds := ellTilde_bounds hm c N
  have h_filt := ellTilde_filter_eq hc N
  have h_le : ∀ j, 1 ≤ j → j ≤ ellTilde c N - 1 → cv c j ≤ N := by
    intro j hj1 hj2
    have hj_mem : j ∈ Icc 1 (ellTilde c N - 1) := mem_Icc.mpr ⟨hj1, hj2⟩
    rw [← h_filt, mem_filter] at hj_mem
    exact hj_mem.2
  have h_prev : cv c (ellTilde c N - 1) ≤ N := by
    rcases eq_or_lt_of_le h_bds.1 with heq | hlt
    · rw [← heq, Nat.sub_self, cv_zero_of_isConfig hc]
      exact Nat.zero_le N
    · exact h_le (ellTilde c N - 1) (by omega) le_rfl
  have h_curr_lt : N < k → N < cv c (ellTilde c N) := by
    intro hN_lt
    rcases eq_or_lt_of_le h_bds.2 with heq | hlt
    · rw [heq, cv_m_of_isConfig hc]
      exact hN_lt
    · by_contra hge
      push_neg at hge
      have hmem : ellTilde c N ∈ (Icc 1 (m - 1)).filter (fun j => cv c j ≤ N) := by
        rw [mem_filter, mem_Icc]
        exact ⟨⟨h_bds.1, by omega⟩, hge⟩
      rw [h_filt, mem_Icc] at hmem
      omega
  have h_curr : N ≤ cv c (ellTilde c N) := by
    rcases eq_or_lt_of_le hNk with hNk_eq | hlt
    · rw [hNk_eq] at h_bds h_filt ⊢
      rcases eq_or_lt_of_le h_bds.2 with heq | hlt'
      · rw [heq, cv_m_of_isConfig hc]
      · exact le_of_lt (by
          by_contra hge
          push_neg at hge
          have hmem : ellTilde c k ∈ (Icc 1 (m - 1)).filter (fun j => cv c j ≤ k) := by
            rw [mem_filter, mem_Icc]
            exact ⟨⟨h_bds.1, by omega⟩, hge⟩
          rw [h_filt, mem_Icc] at hmem
          omega)
    · exact le_of_lt (h_curr_lt hlt)
  have h_ge : ∀ j, ellTilde c N ≤ j → j ≤ m → N ≤ cv c j := by
    intro j hj1 _
    exact le_trans h_curr (cv_mono_of_isConfig hc (ellTilde c N) j hj1)
  have h_lt_imp : ∀ j, 1 ≤ j → j ≤ m → N < cv c j → ellTilde c N ≤ j := by
    intro j hj1 _ hlt
    by_contra hgt
    have hj_le : j ≤ ellTilde c N - 1 := by omega
    have := h_le j hj1 hj_le
    omega
  exact ⟨h_le, h_prev, h_curr, h_ge, h_curr_lt, h_lt_imp⟩

private noncomputable def phiTerm (k : ℕ) {m : ℕ} (r α : ℕ → ℝ) (c : Config k m) (N j : ℕ) : ℝ :=
  (pr r j - pr r (j - 1)) *
    (Real.exp (((min (cv c j) N : ℕ) : ℝ) / k - ((min (cv c (j - 1)) N : ℕ) : ℝ) / k) - 1) /
      (Real.exp (α j) - 1)

private lemma def3Phi_eq_sum_min {k m : ℕ} (hm : 1 ≤ m) (r α : ℕ → ℝ)
    {c : Config k m} (hc : IsConfig c) {N : ℕ} (hNk : N ≤ k) :
    def3Phi k m r α c N = ∑ j ∈ Icc 1 m, phiTerm k r α c N j := by
  have h_bds := ellTilde_bounds hm c N
  have h_spec := ellTilde_spec hm hc hNk
  set ℓ := ellTilde c N
  have h_split1 : Icc 1 m = Icc 1 ℓ ∪ Icc (ℓ + 1) m := by
    ext x; simp only [mem_union, mem_Icc]; omega
  have h_disj1 : Disjoint (Icc 1 ℓ) (Icc (ℓ + 1) m) := by
    rw [disjoint_iff_ne]
    intro x hx y hy; rw [mem_Icc] at hx hy; omega
  have h_split2 : Icc 1 ℓ = insert ℓ (Icc 1 (ℓ - 1)) := by
    ext x; simp only [mem_insert, mem_Icc]; omega
  have h_notmem2 : ℓ ∉ Icc 1 (ℓ - 1) := by
    simp only [mem_Icc]; omega
  rw [h_split1, sum_union h_disj1, h_split2, sum_insert h_notmem2]
  have h_zero : ∑ j ∈ Icc (ℓ + 1) m, phiTerm k r α c N j = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [mem_Icc] at hj
    have hj_prev : N ≤ cv c (j - 1) := h_spec.2.2.2.1 (j - 1) (by omega) (by omega)
    have hj_curr : N ≤ cv c j := h_spec.2.2.2.1 j (by omega) hj.2
    unfold phiTerm
    rw [min_eq_right hj_curr, min_eq_right hj_prev, sub_self, Real.exp_zero, sub_self,
        mul_zero, zero_div]
  have h_prefix : ∑ j ∈ Icc 1 (ℓ - 1), phiTerm k r α c N j =
      ∑ j ∈ Icc 1 (ℓ - 1),
        (pr r j - pr r (j - 1)) *
          (Real.exp ((cv c j : ℝ) / k - (cv c (j - 1) : ℝ) / k) - 1) / (Real.exp (α j) - 1) := by
    apply sum_congr rfl
    intro j hj
    rw [mem_Icc] at hj
    have hj_curr : cv c j ≤ N := h_spec.1 j hj.1 hj.2
    have hj_prev : cv c (j - 1) ≤ N :=
      le_trans (cv_mono_of_isConfig hc (j - 1) j (by omega)) hj_curr
    unfold phiTerm
    rw [min_eq_left hj_curr, min_eq_left hj_prev]
  have h_ell : phiTerm k r α c N ℓ =
      (pr r ℓ - pr r (ℓ - 1)) *
        (Real.exp ((N : ℝ) / k - (cv c (ℓ - 1) : ℝ) / k) - 1) / (Real.exp (α ℓ) - 1) := by
    unfold phiTerm
    rw [min_eq_right h_spec.2.2.1, min_eq_left h_spec.2.1]
  rw [h_zero, add_zero, h_prefix, h_ell, add_comm]
  rfl

private lemma isValueFn_def3Phi {k m : ℕ} (hm : 1 ≤ m) {r α : ℕ → ℝ}
    (hr : IsPriceSet m r) (hα : IsBookingLimits m r α)
    {c : Config k m} (hc : IsConfig c) : IsValueFn k (def3Phi k m r α c) := by
  refine ⟨?_, ?_⟩
  · rw [def3Phi_eq_sum_min hm r α hc (Nat.zero_le k)]
    apply sum_eq_zero
    intro j _
    unfold phiTerm
    simp
  · intro N hNk
    rw [def3Phi_eq_sum_min hm r α hc (le_of_lt hNk),
        def3Phi_eq_sum_min hm r α hc (by omega : N + 1 ≤ k)]
    apply sum_le_sum
    intro j hj
    rw [mem_Icc] at hj
    unfold phiTerm
    have hpr_pos : 0 ≤ pr r j - pr r (j - 1) := le_of_lt (pr_diff_pos hr j hj.1 hj.2)
    have hα_pos : 0 < Real.exp (α j) - 1 := by
      rw [sub_pos, Real.one_lt_exp_iff]
      exact hα.1 j hj.1 hj.2
    have hcv_le : cv c (j - 1) ≤ cv c j := cv_mono_of_isConfig hc (j - 1) j (by omega)
    have hmin_diff : min (cv c j) N - min (cv c (j - 1)) N ≤
        min (cv c j) (N + 1) - min (cv c (j - 1)) (N + 1) := by omega
    have h1 : min (cv c (j - 1)) N ≤ min (cv c j) N := by omega
    have h2 : min (cv c (j - 1)) (N + 1) ≤ min (cv c j) (N + 1) := by omega
    have hcast1 : ((min (cv c j) N : ℕ) : ℝ) / k - ((min (cv c (j - 1)) N : ℕ) : ℝ) / k =
        ((min (cv c j) N - min (cv c (j - 1)) N : ℕ) : ℝ) / k := by
      rw [Nat.cast_sub h1, sub_div]
    have hcast2 : ((min (cv c j) (N + 1) : ℕ) : ℝ) / k - ((min (cv c (j - 1)) (N + 1) : ℕ) : ℝ) / k =
        ((min (cv c j) (N + 1) - min (cv c (j - 1)) (N + 1) : ℕ) : ℝ) / k := by
      rw [Nat.cast_sub h2, sub_div]
    rw [hcast1, hcast2]
    have hexp_le : Real.exp (((min (cv c j) N - min (cv c (j - 1)) N : ℕ) : ℝ) / k) - 1 ≤
        Real.exp (((min (cv c j) (N + 1) - min (cv c (j - 1)) (N + 1) : ℕ) : ℝ) / k) - 1 := by
      apply sub_le_sub_right
      apply Real.exp_le_exp.mpr
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hmin_diff) (Nat.cast_nonneg k)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_le hpr_pos) (le_of_lt hα_pos)

private lemma def3Phi_step {k m : ℕ} (hm : 1 ≤ m) (r α : ℕ → ℝ)
    {c : Config k m} (hc : IsConfig c) {N : ℕ} (hNk : N < k) :
    def3Phi k m r α c (N + 1) - def3Phi k m r α c N =
      (pr r (ellTilde c N) - pr r (ellTilde c N - 1)) *
        (Real.exp (((N + 1 : ℕ) : ℝ) / k - (cv c (ellTilde c N - 1) : ℝ) / k) -
          Real.exp ((N : ℝ) / k - (cv c (ellTilde c N - 1) : ℝ) / k)) /
        (Real.exp (α (ellTilde c N)) - 1) := by
  have h_bds := ellTilde_bounds hm c N
  have h_spec := ellTilde_spec hm hc (le_of_lt hNk)
  have h_lt : N < cv c (ellTilde c N) := h_spec.2.2.2.2.1 hNk
  set ℓ := ellTilde c N
  rw [def3Phi_eq_sum_min hm r α hc (by omega : N + 1 ≤ k),
      def3Phi_eq_sum_min hm r α hc (le_of_lt hNk), ← sum_sub_distrib]
  have hterm : ∀ j ∈ Icc 1 m,
      phiTerm k r α c (N + 1) j - phiTerm k r α c N j =
        if j = ℓ then
          (pr r ℓ - pr r (ℓ - 1)) *
            (Real.exp (((N + 1 : ℕ) : ℝ) / k - (cv c (ℓ - 1) : ℝ) / k) -
              Real.exp ((N : ℝ) / k - (cv c (ℓ - 1) : ℝ) / k)) /
            (Real.exp (α ℓ) - 1)
        else 0 := by
    intro j hj
    rw [mem_Icc] at hj
    by_cases hjeq : j = ℓ
    · subst hjeq
      rw [if_pos rfl]
      unfold phiTerm
      have h1 : min (cv c ℓ) (N + 1) = N + 1 := min_eq_right (Nat.succ_le_of_lt h_lt)
      have h2 : min (cv c (ℓ - 1)) (N + 1) = cv c (ℓ - 1) :=
        min_eq_left (le_trans h_spec.2.1 (Nat.le_succ N))
      have h3 : min (cv c ℓ) N = N := min_eq_right (le_of_lt h_lt)
      have h4 : min (cv c (ℓ - 1)) N = cv c (ℓ - 1) := min_eq_left h_spec.2.1
      rw [h1, h2, h3, h4]
      ring
    · rw [if_neg hjeq]
      rcases lt_or_gt_of_ne hjeq with hjlt | hjgt
      · have hj_curr : cv c j ≤ N := h_spec.1 j hj.1 (by omega)
        have hj_prev : cv c (j - 1) ≤ N :=
          le_trans (cv_mono_of_isConfig hc (j - 1) j (by omega)) hj_curr
        unfold phiTerm
        rw [min_eq_left (le_trans hj_curr (Nat.le_succ N)),
            min_eq_left (le_trans hj_prev (Nat.le_succ N)),
            min_eq_left hj_curr, min_eq_left hj_prev, sub_self]
      · have hj_prev : N + 1 ≤ cv c (j - 1) :=
          le_trans (Nat.succ_le_of_lt h_lt) (cv_mono_of_isConfig hc ℓ (j - 1) (by omega))
        have hj_curr : N + 1 ≤ cv c j :=
          le_trans hj_prev (cv_mono_of_isConfig hc (j - 1) j (by omega))
        unfold phiTerm
        rw [min_eq_right hj_curr, min_eq_right hj_prev,
            min_eq_right (le_trans (Nat.le_succ N) hj_curr),
            min_eq_right (le_trans (Nat.le_succ N) hj_prev)]
        simp
  rw [sum_congr rfl hterm, sum_ite_eq' (Icc 1 m) ℓ _, if_pos (mem_Icc.mpr ⟨h_bds.1, h_bds.2⟩)]

private lemma def3Phi_cv {k m : ℕ} (hm : 1 ≤ m) (r α : ℕ → ℝ)
    {c : Config k m} (hc : IsConfig c) {j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    def3Phi k m r α c (cv c j) =
      ∑ j' ∈ Icc 1 j,
        (pr r j' - pr r (j' - 1)) *
          (Real.exp ((cv c j' : ℝ) / k - (cv c (j' - 1) : ℝ) / k) - 1) /
          (Real.exp (α j') - 1) := by
  rw [def3Phi_eq_sum_min hm r α hc (cv_le_k_all c j)]
  have h_split : Icc 1 m = Icc 1 j ∪ Icc (j + 1) m := by
    ext x; simp only [mem_union, mem_Icc]; omega
  have h_disj : Disjoint (Icc 1 j) (Icc (j + 1) m) := by
    rw [disjoint_iff_ne]
    intro x hx y hy; rw [mem_Icc] at hx hy; omega
  rw [h_split, sum_union h_disj]
  have h_zero : ∑ j' ∈ Icc (j + 1) m, phiTerm k r α c (cv c j) j' = 0 := by
    apply sum_eq_zero
    intro j' hj'
    rw [mem_Icc] at hj'
    have h1 : cv c j ≤ cv c (j' - 1) := cv_mono_of_isConfig hc j (j' - 1) (by omega)
    have h2 : cv c j ≤ cv c j' := cv_mono_of_isConfig hc j j' (by omega)
    unfold phiTerm
    rw [min_eq_right h2, min_eq_right h1, sub_self, Real.exp_zero, sub_self, mul_zero, zero_div]
  rw [h_zero, add_zero]
  apply sum_congr rfl
  intro j' hj'
  rw [mem_Icc] at hj'
  have h1 : cv c j' ≤ cv c j := cv_mono_of_isConfig hc j' j hj'.2
  have h2 : cv c (j' - 1) ≤ cv c j := cv_mono_of_isConfig hc (j' - 1) j (by omega)
  unfold phiTerm
  rw [min_eq_left h1, min_eq_left h2]

private lemma measurableSet_def3Config_eq (k m : ℕ) (α : ℕ → ℝ) (c : Config k m) :
    MeasurableSet {W : ℝ | def3Config k m α W = c} := by
  have heq : {W : ℝ | def3Config k m α W = c} =
      ⋂ j : Fin (m + 1), {W : ℝ | def3Config k m α W j = c j} := by
    ext W
    simp [funext_iff]
  rw [heq]
  apply MeasurableSet.iInter
  intro j
  let θ := Lsum α j.val * k - ⌊Lsum α j.val * k⌋₊
  let v (b : ℕ) : Fin (k + 1) :=
    ⟨min k (⌊Lsum α j.val * k⌋₊ + b), Nat.lt_succ_of_le (min_le_left _ _)⟩
  have hj_set : {W : ℝ | def3Config k m α W j = c j} =
      {W : ℝ | (if W < θ then v 1 else v 0) = c j} := by
    ext W
    simp only [Set.mem_setOf_eq, def3Config, Fin.ext_iff, v, θ]
    split_ifs <;> rfl
  rw [hj_set]
  by_cases h1 : v 1 = c j <;> by_cases h0 : v 0 = c j
  · have : {W : ℝ | (if W < θ then v 1 else v 0) = c j} = Set.univ := by
      ext W; simp [h1, h0]
    rw [this]; exact MeasurableSet.univ
  · have : {W : ℝ | (if W < θ then v 1 else v 0) = c j} = Set.Iio θ := by
      ext W; simp only [Set.mem_setOf_eq, Set.mem_Iio]
      split_ifs with h <;> simp [h, h1, h0]
    rw [this]; exact measurableSet_Iio
  · have : {W : ℝ | (if W < θ then v 1 else v 0) = c j} = (Set.Iio θ)ᶜ := by
      ext W; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_Iio]
      split_ifs with h <;> simp [h, h1, h0]
    rw [this]; exact measurableSet_Iio.compl
  · have : {W : ℝ | (if W < θ then v 1 else v 0) = c j} = ∅ := by
      ext W; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
      split_ifs <;> simp [h1, h0]
    rw [this]; exact MeasurableSet.empty

private lemma sum_volume_partition (k m : ℕ) (α : ℕ → ℝ) (A : Set ℝ)
    (hA_meas : MeasurableSet A) (hA_sub : A ⊆ Set.Icc (0 : ℝ) 1) :
    (∑ c : Config k m, (volume (A ∩ {W | def3Config k m α W = c})).toReal) =
      (volume A).toReal := by
  let S (c : Config k m) : Set ℝ := A ∩ {W | def3Config k m α W = c}
  have hS_meas : ∀ c, MeasurableSet (S c) :=
    fun c => hA_meas.inter (measurableSet_def3Config_eq k m α c)
  have hS_lt_top : ∀ c, volume (S c) < ⊤ := by
    intro c
    have hsub : S c ⊆ Set.Icc (0 : ℝ) 1 :=
      Set.Subset.trans Set.inter_subset_left hA_sub
    calc
      volume (S c) ≤ volume (Set.Icc (0 : ℝ) 1) := measure_mono hsub
      _ = ENNReal.ofReal (1 - 0) := Real.volume_Icc
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hS_disj : Set.PairwiseDisjoint (↑(univ : Finset (Config k m))) S := by
    intro c₁ _ c₂ _ hne
    rw [Function.onFun, Set.disjoint_iff]
    intro W ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
    exact hne (h1.symm.trans h2)
  have hS_union : (⋃ c ∈ (univ : Finset (Config k m)), S c) = A := by
    ext W
    simp [S]
  rw [← ENNReal.toReal_sum (fun c _ => ne_of_lt (hS_lt_top c)),
      ← measure_biUnion_finset hS_disj (fun c _ => hS_meas c), hS_union]

private lemma exists_seed_of_rho_ne_zero {k m : ℕ} {r α : ℕ → ℝ} {c : Config k m}
    (hρ : (def3Proc k m r α).ρ c ≠ 0) :
    ∃ W ∈ Set.Icc (0 : ℝ) 1, def3Config k m α W = c := by
  by_contra h
  push_neg at h
  have hempty : Set.Icc (0 : ℝ) 1 ∩ {W | def3Config k m α W = c} = ∅ := by
    ext W
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    exact h W
  apply hρ
  unfold def3Proc
  dsimp
  rw [hempty, measure_empty, ENNReal.toReal_zero]

private lemma isProcedure_def3Proc (k m : ℕ) (hm : 1 ≤ m) {r α : ℕ → ℝ}
    (hr : IsPriceSet m r) (hα : IsBookingLimits m r α) :
    IsProcedure (def3Proc k m r α) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    exact ENNReal.toReal_nonneg
  · unfold def3Proc
    dsimp
    rw [sum_volume_partition k m α (Set.Icc (0 : ℝ) 1) measurableSet_Icc Set.Subset.rfl,
        Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal zero_le_one]
  · intro c hρ
    obtain ⟨W, hW_mem, rfl⟩ := exists_seed_of_rho_ne_zero hρ
    have hc : IsConfig (def3Config k m α W) := isConfig_def3Config k m hα hW_mem.1
    exact ⟨hc, isValueFn_def3Phi hm hr hα hc⟩

private lemma expected_cv (k m : ℕ) {r α : ℕ → ℝ} (hα : IsBookingLimits m r α)
    {j : ℕ} (hjm : j ≤ m) :
    (∑ c : Config k m, (def3Proc k m r α).ρ c * (cv c j : ℝ)) = Lsum α j * k := by
  let x := Lsum α j * k
  let q := ⌊x⌋₊
  let θ := x - q
  have hL := Lsum_bounds hα hjm
  have hx0 : 0 ≤ x := mul_nonneg hL.1 (Nat.cast_nonneg k)
  have hxk : x ≤ k := by
    calc
      Lsum α j * k ≤ 1 * (k : ℝ) := mul_le_mul_of_nonneg_right hL.2 (Nat.cast_nonneg k)
      _ = k := one_mul _
  have hfl_le : (q : ℝ) ≤ x := Nat.floor_le hx0
  have hfl_lt : x < (q : ℝ) + 1 := Nat.lt_floor_add_one x
  have hθ0 : 0 ≤ θ := by dsimp [θ]; linarith
  have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith
  let A₁ := Set.Ico (0 : ℝ) θ
  let A₂ := Set.Icc θ 1
  let E (c : Config k m) : Set ℝ := {W | def3Config k m α W = c}
  have hA_union : Set.Icc (0 : ℝ) 1 = A₁ ∪ A₂ := (Set.Ico_union_Icc_eq_Icc hθ0 hθ1).symm
  have hA_disj : Disjoint A₁ A₂ := by
    rw [Set.disjoint_iff]
    intro W ⟨h1, h2⟩
    exact not_lt_of_ge h2.1 h1.2
  have hA1_sub : A₁ ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [hA_union]; exact Set.subset_union_left
  have hA2_sub : A₂ ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [hA_union]; exact Set.subset_union_right
  have hterm : ∀ c : Config k m,
      (def3Proc k m r α).ρ c * (cv c j : ℝ) =
        (volume (A₁ ∩ E c)).toReal * ((q + 1 : ℕ) : ℝ) +
          (volume (A₂ ∩ E c)).toReal * (q : ℝ) := by
    intro c
    have hEc_meas : MeasurableSet (E c) := measurableSet_def3Config_eq k m α c
    have h_split : Set.Icc (0 : ℝ) 1 ∩ E c = (A₁ ∩ E c) ∪ (A₂ ∩ E c) := by
      rw [hA_union, Set.union_inter_distrib_right]
    have h_disj_c : Disjoint (A₁ ∩ E c) (A₂ ∩ E c) :=
      hA_disj.mono Set.inter_subset_left Set.inter_subset_left
    have h1_lt : volume (A₁ ∩ E c) < ⊤ := by
      calc
        volume (A₁ ∩ E c) ≤ volume (Set.Icc (0 : ℝ) 1) :=
          measure_mono (Set.Subset.trans Set.inter_subset_left hA1_sub)
        _ = ENNReal.ofReal (1 - 0) := Real.volume_Icc
        _ < ⊤ := ENNReal.ofReal_lt_top
    have h2_lt : volume (A₂ ∩ E c) < ⊤ := by
      calc
        volume (A₂ ∩ E c) ≤ volume (Set.Icc (0 : ℝ) 1) :=
          measure_mono (Set.Subset.trans Set.inter_subset_left hA2_sub)
        _ = ENNReal.ofReal (1 - 0) := Real.volume_Icc
        _ < ⊤ := ENNReal.ofReal_lt_top
    have hρ_split : (def3Proc k m r α).ρ c =
        (volume (A₁ ∩ E c)).toReal + (volume (A₂ ∩ E c)).toReal := by
      unfold def3Proc
      dsimp
      rw [h_split, measure_union h_disj_c (measurableSet_Icc.inter hEc_meas),
          ENNReal.toReal_add (ne_of_lt h1_lt) (ne_of_lt h2_lt)]
    have hpart1 : (volume (A₁ ∩ E c)).toReal * (cv c j : ℝ) =
        (volume (A₁ ∩ E c)).toReal * ((q + 1 : ℕ) : ℝ) := by
      by_cases hne : (A₁ ∩ E c).Nonempty
      · obtain ⟨W, hW1, rfl⟩ := hne
        rw [cv_def3Config_eq_rd k m hα hW1.1 hjm]
        unfold rd
        change (volume (A₁ ∩ E (def3Config k m α W))).toReal *
            ((q + (if W < θ then 1 else 0) : ℕ) : ℝ) = _
        rw [if_pos hW1.2]
      · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty, ENNReal.toReal_zero,
            zero_mul, zero_mul]
    have hpart2 : (volume (A₂ ∩ E c)).toReal * (cv c j : ℝ) =
        (volume (A₂ ∩ E c)).toReal * (q : ℝ) := by
      by_cases hne : (A₂ ∩ E c).Nonempty
      · obtain ⟨W, hW2, rfl⟩ := hne
        rw [cv_def3Config_eq_rd k m hα (le_trans hθ0 hW2.1) hjm]
        unfold rd
        change (volume (A₂ ∩ E (def3Config k m α W))).toReal *
            ((q + (if W < θ then 1 else 0) : ℕ) : ℝ) = _
        rw [if_neg (not_lt.mpr hW2.1), add_zero]
      · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty, ENNReal.toReal_zero,
            zero_mul, zero_mul]
    rw [hρ_split, add_mul, hpart1, hpart2]
  rw [sum_congr rfl (fun c _ => hterm c), sum_add_distrib, ← sum_mul, ← sum_mul,
      sum_volume_partition k m α A₁ measurableSet_Ico hA1_sub,
      sum_volume_partition k m α A₂ measurableSet_Icc hA2_sub,
      Real.volume_Ico, Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal hθ0, ENNReal.toReal_ofReal (sub_nonneg.mpr hθ1)]
  push_cast
  dsimp [θ]
  ring

private lemma cond18_def3Proc (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) {r α : ℕ → ℝ}
    (hr : IsPriceSet m r) (hα : IsBookingLimits m r α) :
    Cond18 r (def3Proc k m r α) := by
  have hproc := isProcedure_def3Proc k m hm hr hα
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  intro j hj1 hjm
  have hterm_c : ∀ c : Config k m,
      (def3Proc k m r α).ρ c * (def3Proc k m r α).Φ c (cv c j) =
        ∑ j' ∈ Icc 1 j,
          (pr r j' - pr r (j' - 1)) / (Real.exp (α j') - 1) *
            ((def3Proc k m r α).ρ c *
              (Real.exp ((cv c j' : ℝ) / k - (cv c (j' - 1) : ℝ) / k) - 1)) := by
    intro c
    by_cases hρ : (def3Proc k m r α).ρ c = 0
    · simp [hρ]
    · have hc : IsConfig c := (hproc.2.2 c hρ).1
      change (def3Proc k m r α).ρ c * def3Phi k m r α c (cv c j) = _
      rw [def3Phi_cv hm r α hc hj1 hjm, mul_sum]
      apply sum_congr rfl
      intro j' _
      ring
  rw [sum_congr rfl (fun c _ => hterm_c c), sum_comm]
  have h_tele : r j = ∑ j' ∈ Icc 1 j, (pr r j' - pr r (j' - 1)) := by
    have : ∀ n, 1 ≤ n → (∑ j' ∈ Icc 1 n, (pr r j' - pr r (j' - 1))) = r n := by
      intro n hn
      induction n with
      | zero => omega
      | succ n ih =>
        rcases eq_or_lt_of_le hn with h | h
        · rw [← h]
          simp [pr]
        · have hIcc : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
            ext x; simp only [mem_Icc, mem_insert]; omega
          have hnotmem : n + 1 ∉ Icc 1 n := by simp only [mem_Icc]; omega
          rw [hIcc, sum_insert hnotmem, ih (by omega)]
          have h1 : pr r (n + 1) = r (n + 1) := if_neg (by omega)
          have h2 : pr r (n + 1 - 1) = r n := if_neg (by omega)
          rw [h1, h2]
          ring
    exact (this j hj1).symm
  rw [h_tele]
  apply sum_le_sum
  intro j' hj'
  rw [mem_Icc] at hj'
  have hj'm : j' ≤ m := le_trans hj'.2 hjm
  have hα_pos : 0 < Real.exp (α j') - 1 := by
    rw [sub_pos, Real.one_lt_exp_iff]
    exact hα.1 j' hj'.1 hj'm
  have hpr_pos : 0 ≤ (pr r j' - pr r (j' - 1)) / (Real.exp (α j') - 1) :=
    div_nonneg (le_of_lt (pr_diff_pos hr j' hj'.1 hj'm)) (le_of_lt hα_pos)
  rw [← mul_sum]
  have h_exp_lb : Real.exp (α j') - 1 ≤
      ∑ c : Config k m,
        (def3Proc k m r α).ρ c *
          (Real.exp ((cv c j' : ℝ) / k - (cv c (j' - 1) : ℝ) / k) - 1) := by
    have h_pt : ∀ c : Config k m,
        (def3Proc k m r α).ρ c *
          (Real.exp (α j') * (1 + ((cv c j' : ℝ) / k - (cv c (j' - 1) : ℝ) / k - α j')) - 1) ≤
        (def3Proc k m r α).ρ c *
          (Real.exp ((cv c j' : ℝ) / k - (cv c (j' - 1) : ℝ) / k) - 1) := by
      intro c
      apply mul_le_mul_of_nonneg_left _ (hproc.1 c)
      apply sub_le_sub_right
      let d := (cv c j' : ℝ) / k - (cv c (j' - 1) : ℝ) / k
      have h1 := Real.add_one_le_exp (d - α j')
      have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos (α j')))
      rw [← Real.exp_add] at h2
      have heq : α j' + (d - α j') = d := by ring
      rw [heq] at h2
      linarith
    have h_sum_lb : (∑ c : Config k m,
        (def3Proc k m r α).ρ c *
          (Real.exp (α j') * (1 + ((cv c j' : ℝ) / k - (cv c (j' - 1) : ℝ) / k - α j')) - 1)) =
        Real.exp (α j') - 1 := by
      have h_lin : ∀ c : Config k m,
          (def3Proc k m r α).ρ c *
            (Real.exp (α j') * (1 + ((cv c j' : ℝ) / k - (cv c (j' - 1) : ℝ) / k - α j')) - 1) =
          (Real.exp (α j') * (1 - α j') - 1) * (def3Proc k m r α).ρ c +
            (Real.exp (α j') / k) * ((def3Proc k m r α).ρ c * (cv c j' : ℝ)) -
            (Real.exp (α j') / k) * ((def3Proc k m r α).ρ c * (cv c (j' - 1) : ℝ)) := by
        intro c; ring
      rw [sum_congr rfl (fun c _ => h_lin c), sum_sub_distrib, sum_add_distrib,
          ← mul_sum, ← mul_sum, ← mul_sum, hproc.2.1,
          expected_cv k m hα hj'm, expected_cv k m hα (by omega)]
      have hL_step := Lsum_step α hj'.1
      calc
        (Real.exp (α j') * (1 - α j') - 1) * 1 +
            Real.exp (α j') / (k : ℝ) * (Lsum α j' * (k : ℝ)) -
            Real.exp (α j') / (k : ℝ) * (Lsum α (j' - 1) * (k : ℝ))
          = (Real.exp (α j') * (1 - α j') - 1) +
              Real.exp (α j') * (Lsum α j' - Lsum α (j' - 1)) * ((k : ℝ) / (k : ℝ)) := by ring
        _ = (Real.exp (α j') * (1 - α j') - 1) + Real.exp (α j') * α j' * 1 := by
            rw [hL_step, div_self (ne_of_gt hk_pos)]
        _ = Real.exp (α j') - 1 := by ring
    rw [← h_sum_lb]
    exact sum_le_sum (fun c _ => h_pt c)
  calc
    pr r j' - pr r (j' - 1)
      = (pr r j' - pr r (j' - 1)) / (Real.exp (α j') - 1) * (Real.exp (α j') - 1) := by
        rw [div_mul_cancel₀ _ (ne_of_gt hα_pos)]
    _ ≤ (pr r j' - pr r (j' - 1)) / (Real.exp (α j') - 1) *
          ∑ c : Config k m,
            (def3Proc k m r α).ρ c *
              (Real.exp ((cv c j' : ℝ) / k - (cv c (j' - 1) : ℝ) / k) - 1) :=
        mul_le_mul_of_nonneg_left h_exp_lb hpr_pos

private lemma beta_ge_one {k : ℕ} (hk : 1 ≤ k) :
    1 ≤ (1 + (k : ℝ)) * (1 - Real.exp (-1 / (k : ℝ))) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have h1 : 1 / (k : ℝ) + 1 ≤ Real.exp (1 / (k : ℝ)) := Real.add_one_le_exp (1 / (k : ℝ))
  have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos (-1 / (k : ℝ))))
  rw [← Real.exp_add] at h2
  have hzero : 1 / (k : ℝ) + -1 / (k : ℝ) = 0 := by ring
  rw [hzero, Real.exp_zero] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt hk_pos)
  have h4 : (k : ℝ) * ((1 / (k : ℝ) + 1) * Real.exp (-1 / (k : ℝ))) =
      (1 + (k : ℝ)) * Real.exp (-1 / (k : ℝ)) := by
    calc
      (k : ℝ) * ((1 / (k : ℝ) + 1) * Real.exp (-1 / (k : ℝ)))
        = ((k : ℝ) / (k : ℝ) + (k : ℝ)) * Real.exp (-1 / (k : ℝ)) := by ring
      _ = (1 + (k : ℝ)) * Real.exp (-1 / (k : ℝ)) := by
          rw [div_self (ne_of_gt hk_pos)]
  rw [h4, mul_one] at h3
  linarith

private lemma cond17_core {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) {r α : ℕ → ℝ}
    (hr : IsPriceSet m r) (hα : IsBookingLimits m r α)
    {c₀ : Config k m} (hc₀ : IsConfig c₀)
    {j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m) {N : ℕ} (hN_lt : N < cv c₀ j) :
    ∃ ℓ'' ∈ Icc (ellTilde c₀ N) j,
      (k : ℝ) * (def3Phi k m r α c₀ (N + 1) - def3Phi k m r α c₀ N) +
          def3Phi k m r α c₀ (cv c₀ j) - def3Phi k m r α c₀ N ≤
        (r j / Fval α) *
          Real.exp ((cv c₀ j : ℝ) / k - (cv c₀ (ℓ'' - 1) : ℝ) / k -
            (Lsum α j - Lsum α (ℓ'' - 1))) *
          ((1 + (k : ℝ)) * (1 - Real.exp (-1 / (k : ℝ)))) := by
  have hNk : N < k := lt_of_lt_of_le hN_lt (cv_le_k_all c₀ j)
  have h_bds := ellTilde_bounds hm c₀ N
  have h_spec := ellTilde_spec hm hc₀ (le_of_lt hNk)
  set ℓ := ellTilde c₀ N
  have hℓj : ℓ ≤ j := h_spec.2.2.2.2.2 j hj1 hjm hN_lt
  have hN_lt_ℓ : N < cv c₀ ℓ := h_spec.2.2.2.2.1 hNk
  have hℓm : ℓ ≤ m := h_bds.2
  let β := (1 + (k : ℝ)) * (1 - Real.exp (-1 / (k : ℝ)))
  have hβ1 : 1 ≤ β := beta_ge_one hk
  have hF_pos : 0 < Fval α := (Fval_bounds hm hα).1
  let bound (j' ℓ'' : ℕ) : ℝ :=
    (r j' / Fval α) *
      Real.exp ((cv c₀ j' : ℝ) / k - (cv c₀ (ℓ'' - 1) : ℝ) / k -
        (Lsum α j' - Lsum α (ℓ'' - 1))) * β
  let piece (ℓ' : ℕ) : ℝ :=
    (pr r ℓ' - pr r (ℓ' - 1)) *
      (Real.exp ((cv c₀ ℓ' : ℝ) / k - (cv c₀ (ℓ' - 1) : ℝ) / k) - 1) /
      (Real.exp (α ℓ') - 1)
  have h_base : (k : ℝ) * (def3Phi k m r α c₀ (N + 1) - def3Phi k m r α c₀ N) +
      def3Phi k m r α c₀ (cv c₀ ℓ) - def3Phi k m r α c₀ N ≤ bound ℓ ℓ := by
    rw [def3Phi_step hm r α hc₀ hNk, def3Phi_cv hm r α hc₀ h_bds.1 hℓm]
    have h_defN : def3Phi k m r α c₀ N =
        (∑ j' ∈ Icc 1 (ℓ - 1),
          (pr r j' - pr r (j' - 1)) *
            (Real.exp ((cv c₀ j' : ℝ) / k - (cv c₀ (j' - 1) : ℝ) / k) - 1) / (Real.exp (α j') - 1)) +
        (pr r ℓ - pr r (ℓ - 1)) *
          (Real.exp ((N : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) - 1) / (Real.exp (α ℓ) - 1) := rfl
    have h_split : Icc 1 ℓ = insert ℓ (Icc 1 (ℓ - 1)) := by
      ext x; simp only [mem_insert, mem_Icc]; omega
    have h_notmem : ℓ ∉ Icc 1 (ℓ - 1) := by simp only [mem_Icc]; omega
    rw [h_split, sum_insert h_notmem, h_defN]
    have h_alg : (k : ℝ) *
        ((pr r ℓ - pr r (ℓ - 1)) *
          (Real.exp (((N + 1 : ℕ) : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) -
            Real.exp ((N : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k)) /
          (Real.exp (α ℓ) - 1)) +
        ((pr r ℓ - pr r (ℓ - 1)) *
          (Real.exp ((cv c₀ ℓ : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) - 1) / (Real.exp (α ℓ) - 1) +
          ∑ x ∈ Icc 1 (ℓ - 1),
            (pr r x - pr r (x - 1)) *
              (Real.exp ((cv c₀ x : ℝ) / k - (cv c₀ (x - 1) : ℝ) / k) - 1) / (Real.exp (α x) - 1)) -
        ((∑ j' ∈ Icc 1 (ℓ - 1),
          (pr r j' - pr r (j' - 1)) *
            (Real.exp ((cv c₀ j' : ℝ) / k - (cv c₀ (j' - 1) : ℝ) / k) - 1) / (Real.exp (α j') - 1)) +
          (pr r ℓ - pr r (ℓ - 1)) *
            (Real.exp ((N : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) - 1) / (Real.exp (α ℓ) - 1)) =
        ((pr r ℓ - pr r (ℓ - 1)) / (Real.exp (α ℓ) - 1)) *
          ((k : ℝ) * Real.exp (((N + 1 : ℕ) : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) -
            (1 + (k : ℝ)) * Real.exp ((N : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) +
            Real.exp ((cv c₀ ℓ : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k)) := by ring
    rw [h_alg]
    have h_expN : Real.exp ((N : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) =
        Real.exp (((N + 1 : ℕ) : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) * Real.exp (-1 / (k : ℝ)) := by
      rw [← Real.exp_add]
      push_cast
      ring_nf
    have h_factor : (k : ℝ) * Real.exp (((N + 1 : ℕ) : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) -
        (1 + (k : ℝ)) * Real.exp ((N : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) +
        Real.exp ((cv c₀ ℓ : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) =
        Real.exp (((N + 1 : ℕ) : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) * (β - 1) +
          Real.exp ((cv c₀ ℓ : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) := by
      rw [h_expN]
      dsimp [β]
      ring
    rw [h_factor]
    have h_exp_le : Real.exp (((N + 1 : ℕ) : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) ≤
        Real.exp ((cv c₀ ℓ : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) := by
      apply Real.exp_le_exp.mpr
      apply sub_le_sub_right
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.succ_le_of_lt hN_lt_ℓ)) (Nat.cast_nonneg k)
    have h_sum_le : Real.exp (((N + 1 : ℕ) : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) * (β - 1) +
        Real.exp ((cv c₀ ℓ : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) ≤
        Real.exp ((cv c₀ ℓ : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) * β := by
      nlinarith
    have hα_pos : 0 < Real.exp (α ℓ) - 1 := by
      rw [sub_pos, Real.one_lt_exp_iff]
      exact hα.1 ℓ h_bds.1 hℓm
    have hcoeff_pos : 0 ≤ (pr r ℓ - pr r (ℓ - 1)) / (Real.exp (α ℓ) - 1) :=
      div_nonneg (le_of_lt (pr_diff_pos hr ℓ h_bds.1 hℓm)) (le_of_lt hα_pos)
    have h_le := mul_le_mul_of_nonneg_left h_sum_le hcoeff_pos
    have h_rhs : ((pr r ℓ - pr r (ℓ - 1)) / (Real.exp (α ℓ) - 1)) *
        (Real.exp ((cv c₀ ℓ : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) * β) = bound ℓ ℓ := by
      dsimp [bound]
      rw [booking_identity_exp hr hα h_bds.1 hℓm, Lsum_step α h_bds.1]
      have : Real.exp (-α ℓ) * Real.exp ((cv c₀ ℓ : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) =
          Real.exp ((cv c₀ ℓ : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k - α ℓ) := by
        rw [← Real.exp_add]
        ring_nf
      calc
        r ℓ / Fval α * Real.exp (-α ℓ) *
            (Real.exp ((cv c₀ ℓ : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k) * β)
          = r ℓ / Fval α *
              (Real.exp (-α ℓ) * Real.exp ((cv c₀ ℓ : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k)) * β := by ring
        _ = r ℓ / Fval α *
              Real.exp ((cv c₀ ℓ : ℝ) / k - (cv c₀ (ℓ - 1) : ℝ) / k - α ℓ) * β := by rw [this]
    rwa [h_rhs] at h_le
  have h_step : ∀ j', ℓ ≤ j' → j' < m → ∀ ℓ'' ∈ Icc ℓ j',
      ∃ ℓ''' ∈ Icc ℓ (j' + 1), bound j' ℓ'' + piece (j' + 1) ≤ bound (j' + 1) ℓ''' := by
    intro j' hj'1 hj'm ℓ'' hℓ''
    rw [mem_Icc] at hℓ''
    have hj'2 : 2 ≤ j' + 1 := by omega
    have hj'1_le_m : j' + 1 ≤ m := by omega
    have h_piece_eq : piece (j' + 1) =
        (r (j' + 1) / Fval α) * Real.exp (-α (j' + 1)) *
          (Real.exp ((cv c₀ (j' + 1) : ℝ) / k - (cv c₀ j' : ℝ) / k) - 1) := by
      unfold piece
      have h_id := booking_identity_exp hr hα (by omega) hj'1_le_m
      have h_sub : j' + 1 - 1 = j' := by omega
      rw [h_sub] at h_id ⊢
      calc
        (pr r (j' + 1) - pr r j') *
            (Real.exp ((cv c₀ (j' + 1) : ℝ) / k - (cv c₀ j' : ℝ) / k) - 1) /
            (Real.exp (α (j' + 1)) - 1)
          = ((pr r (j' + 1) - pr r j') / (Real.exp (α (j' + 1)) - 1)) *
              (Real.exp ((cv c₀ (j' + 1) : ℝ) / k - (cv c₀ j' : ℝ) / k) - 1) := by ring
        _ = (r (j' + 1) / Fval α) * Real.exp (-α (j' + 1)) *
              (Real.exp ((cv c₀ (j' + 1) : ℝ) / k - (cv c₀ j' : ℝ) / k) - 1) := by rw [h_id]
    have hr_le : r j' ≤ r (j' + 1) * Real.exp (-α (j' + 1)) := by
      have := r_pred_le_mul_exp hr hα hj'2 hj'1_le_m
      rwa [Nat.add_sub_cancel] at this
    let A := (cv c₀ j' : ℝ) / k - (cv c₀ (ℓ'' - 1) : ℝ) / k - (Lsum α j' - Lsum α (ℓ'' - 1))
    let B := (cv c₀ (j' + 1) : ℝ) / k - (cv c₀ j' : ℝ) / k
    have hB_nonneg : 0 ≤ B := by
      dsimp [B]
      rw [sub_nonneg]
      exact div_le_div_of_nonneg_right
        (Nat.cast_le.mpr (cv_mono_of_isConfig hc₀ j' (j' + 1) (by omega))) (Nat.cast_nonneg k)
    have hexpB_ge1 : 1 ≤ Real.exp B := Real.one_le_exp hB_nonneg
    have h_bound_le : bound j' ℓ'' ≤
        (r (j' + 1) / Fval α) * Real.exp (-α (j' + 1)) * (Real.exp A * β) := by
      dsimp [bound, A]
      have hpos : 0 ≤ Real.exp A * β / Fval α :=
        div_nonneg (mul_nonneg (le_of_lt (Real.exp_pos A)) ( by linarith )) (le_of_lt hF_pos)
      have := mul_le_mul_of_nonneg_right hr_le hpos
      calc
        r j' / Fval α * Real.exp A * β = r j' * (Real.exp A * β / Fval α) := by ring
        _ ≤ (r (j' + 1) * Real.exp (-α (j' + 1))) * (Real.exp A * β / Fval α) := this
        _ = (r (j' + 1) / Fval α) * Real.exp (-α (j' + 1)) * (Real.exp A * β) := by ring
    have hcoeff_pos : 0 ≤ (r (j' + 1) / Fval α) * Real.exp (-α (j' + 1)) :=
      mul_nonneg (div_nonneg (le_of_lt (r_pos_of_priceSet hr (j' + 1) (by omega) hj'1_le_m))
        (le_of_lt hF_pos)) (le_of_lt (Real.exp_pos _))
    rcases le_or_gt A 0 with hA | hA
    · refine ⟨j' + 1, mem_Icc.mpr ⟨by omega, le_rfl⟩, ?_⟩
      have hexpA_le1 : Real.exp A ≤ 1 := Real.exp_le_one_iff.mpr hA
      have hexpA_pos : 0 ≤ Real.exp A := le_of_lt (Real.exp_pos A)
      have h_ineq : Real.exp A * β + (Real.exp B - 1) ≤ Real.exp B * β := by nlinarith
      have h_rhs_eq : (r (j' + 1) / Fval α) * Real.exp (-α (j' + 1)) * (Real.exp B * β) =
          bound (j' + 1) (j' + 1) := by
        dsimp [bound, B]
        have hL := Lsum_step α (by omega : 1 ≤ j' + 1)
        rw [Nat.add_sub_cancel] at hL
        rw [hL]
        have : Real.exp (-α (j' + 1)) * Real.exp ((cv c₀ (j' + 1) : ℝ) / k - (cv c₀ j' : ℝ) / k) =
            Real.exp ((cv c₀ (j' + 1) : ℝ) / k - (cv c₀ j' : ℝ) / k - α (j' + 1)) := by
          rw [← Real.exp_add]; ring_nf
        calc
          r (j' + 1) / Fval α * Real.exp (-α (j' + 1)) *
              (Real.exp ((cv c₀ (j' + 1) : ℝ) / k - (cv c₀ j' : ℝ) / k) * β)
            = r (j' + 1) / Fval α *
                (Real.exp (-α (j' + 1)) * Real.exp ((cv c₀ (j' + 1) : ℝ) / k - (cv c₀ j' : ℝ) / k)) * β := by ring
          _ = _ := by rw [this]
      rw [h_piece_eq, ← h_rhs_eq]
      have h_mul := mul_le_mul_of_nonneg_left h_ineq hcoeff_pos
      linarith
    · refine ⟨ℓ'', mem_Icc.mpr ⟨hℓ''.1, by omega⟩, ?_⟩
      have hexpA_ge1 : 1 ≤ Real.exp A := Real.one_le_exp (le_of_lt hA)
      have h_ineq : Real.exp A * β + (Real.exp B - 1) ≤ Real.exp A * Real.exp B * β := by
        have : 0 ≤ Real.exp A * (Real.exp B - 1) * (β - 1) + (Real.exp A - 1) * (Real.exp B - 1) :=
          add_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
            (mul_nonneg (by linarith) (by linarith))
        linarith
      have h_rhs_eq : (r (j' + 1) / Fval α) * Real.exp (-α (j' + 1)) * (Real.exp A * Real.exp B * β) =
          bound (j' + 1) ℓ'' := by
        dsimp [bound, A, B]
        have hL := Lsum_step α (by omega : 1 ≤ j' + 1)
        have h_sub : j' + 1 - 1 = j' := by omega
        rw [h_sub] at hL
        have h_exp : Real.exp (-α (j' + 1)) *
            Real.exp ((cv c₀ j' : ℝ) / k - (cv c₀ (ℓ'' - 1) : ℝ) / k - (Lsum α j' - Lsum α (ℓ'' - 1))) *
            Real.exp ((cv c₀ (j' + 1) : ℝ) / k - (cv c₀ j' : ℝ) / k) =
            Real.exp ((cv c₀ (j' + 1) : ℝ) / k - (cv c₀ (ℓ'' - 1) : ℝ) / k -
              (Lsum α (j' + 1) - Lsum α (ℓ'' - 1))) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          linarith
        calc
          r (j' + 1) / Fval α * Real.exp (-α (j' + 1)) *
              (Real.exp ((cv c₀ j' : ℝ) / k - (cv c₀ (ℓ'' - 1) : ℝ) / k - (Lsum α j' - Lsum α (ℓ'' - 1))) *
                Real.exp ((cv c₀ (j' + 1) : ℝ) / k - (cv c₀ j' : ℝ) / k) * β)
            = r (j' + 1) / Fval α *
                (Real.exp (-α (j' + 1)) *
                  Real.exp ((cv c₀ j' : ℝ) / k - (cv c₀ (ℓ'' - 1) : ℝ) / k - (Lsum α j' - Lsum α (ℓ'' - 1))) *
                  Real.exp ((cv c₀ (j' + 1) : ℝ) / k - (cv c₀ j' : ℝ) / k)) * β := by ring
          _ = _ := by rw [h_exp]
      rw [h_piece_eq, ← h_rhs_eq]
      have h_mul := mul_le_mul_of_nonneg_left h_ineq hcoeff_pos
      linarith
  have h_ind : ∀ j', ℓ ≤ j' → j' ≤ m →
      ∃ ℓ'' ∈ Icc ℓ j',
        bound ℓ ℓ + (∑ ℓ' ∈ Icc (ℓ + 1) j', piece ℓ') ≤ bound j' ℓ'' := by
    intro j' hj'1 hj'm
    induction j' with
    | zero => omega
    | succ n ih =>
      rcases eq_or_lt_of_le hj'1 with heq | hlt
      · rw [← heq]
        have hempty : Icc (ℓ + 1) ℓ = ∅ := by simp
        rw [hempty, sum_empty, add_zero]
        exact ⟨ℓ, mem_Icc.mpr ⟨le_rfl, le_rfl⟩, le_rfl⟩
      · obtain ⟨ℓ'', hℓ'', h_ih⟩ := ih (by omega) (by omega)
        obtain ⟨ℓ''', hℓ''', h_st⟩ := h_step n (by omega) (by omega) ℓ'' hℓ''
        have hIcc : Icc (ℓ + 1) (n + 1) = insert (n + 1) (Icc (ℓ + 1) n) := by
          ext x; simp only [mem_Icc, mem_insert]; omega
        have hnotmem : n + 1 ∉ Icc (ℓ + 1) n := by simp only [mem_Icc]; omega
        rw [hIcc, sum_insert hnotmem]
        exact ⟨ℓ''', hℓ''', by linarith⟩
  obtain ⟨ℓ'', hℓ'', h_j_bound⟩ := h_ind j hℓj hjm
  refine ⟨ℓ'', hℓ'', ?_⟩
  have h_diff_cv : def3Phi k m r α c₀ (cv c₀ j) - def3Phi k m r α c₀ (cv c₀ ℓ) =
      ∑ ℓ' ∈ Icc (ℓ + 1) j, piece ℓ' := by
    rw [def3Phi_cv hm r α hc₀ hj1 hjm, def3Phi_cv hm r α hc₀ h_bds.1 hℓm]
    have h_split : Icc 1 j = Icc 1 ℓ ∪ Icc (ℓ + 1) j := by
      ext x; simp only [mem_union, mem_Icc]; omega
    have h_disj : Disjoint (Icc 1 ℓ) (Icc (ℓ + 1) j) := by
      rw [disjoint_iff_ne]
      intro x hx y hy; rw [mem_Icc] at hx hy; omega
    rw [h_split, sum_union h_disj]
    dsimp [piece]
    ring
  linarith

theorem solution (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (r α : ℕ → ℝ)
    (hr : IsPriceSet m r) (hα : IsBookingLimits m r α) :
    IsProcedure (def3Proc k m r α) ∧
    Cond17 r (def3Proc k m r α) (Fval α / ((1 + k) * (Real.exp (1 / k) - 1))) ∧
    Cond18 r (def3Proc k m r α) ∧
    (m = 1 → Cond17 r (def3Proc k m r α) (Fval α / ((1 + k) * (1 - Real.exp (-1 / k))))) := by
  have hproc := isProcedure_def3Proc k m hm hr hα
  have hF_pos : 0 < Fval α := (Fval_bounds hm hα).1
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hβ_ge1 : 1 ≤ (1 + (k : ℝ)) * (1 - Real.exp (-1 / (k : ℝ))) := beta_ge_one hk
  refine ⟨hproc, ?_, cond18_def3Proc k m hk hm hr hα, ?_⟩
  · -- Cond17 for general m
    intro c₀ hρ j hj1 hjm N hN_lt
    obtain ⟨W, hW_mem, hW_eq⟩ := exists_seed_of_rho_ne_zero hρ
    have hc₀ : IsConfig c₀ := (hproc.2.2 c₀ hρ).1
    obtain ⟨ℓ'', hℓ'', h_core⟩ := cond17_core hk hm hr hα hc₀ hj1 hjm hN_lt
    rw [mem_Icc] at hℓ''
    have hℓ''_le_m : ℓ'' - 1 ≤ m := by omega
    have h_cv_j : cv c₀ j = rd (Lsum α j * k) W := by
      rw [← hW_eq]; exact cv_def3Config_eq_rd k m hα hW_mem.1 hjm
    have h_cv_ℓ : cv c₀ (ℓ'' - 1) = rd (Lsum α (ℓ'' - 1) * k) W := by
      rw [← hW_eq]; exact cv_def3Config_eq_rd k m hα hW_mem.1 hℓ''_le_m
    have hLj := Lsum_bounds hα hjm
    have hLℓ := Lsum_bounds hα hℓ''_le_m
    have hb_j := rd_bounds (mul_nonneg hLj.1 (Nat.cast_nonneg k)) hW_mem.1 hW_mem.2
    have hb_ℓ := rd_bounds (mul_nonneg hLℓ.1 (Nat.cast_nonneg k)) hW_mem.1 hW_mem.2
    have h_diff_le1 : (cv c₀ j : ℝ) - (cv c₀ (ℓ'' - 1) : ℝ) -
        (Lsum α j - Lsum α (ℓ'' - 1)) * k ≤ 1 := by
      rw [h_cv_j, h_cv_ℓ]
      linarith
    have h_exp_arg_le : (cv c₀ j : ℝ) / k - (cv c₀ (ℓ'' - 1) : ℝ) / k -
        (Lsum α j - Lsum α (ℓ'' - 1)) ≤ 1 / (k : ℝ) := by
      have := div_le_div_of_nonneg_right h_diff_le1 (le_of_lt hk_pos)
      calc
        (cv c₀ j : ℝ) / k - (cv c₀ (ℓ'' - 1) : ℝ) / k - (Lsum α j - Lsum α (ℓ'' - 1))
          = (cv c₀ j : ℝ) / k - (cv c₀ (ℓ'' - 1) : ℝ) / k -
              (Lsum α j - Lsum α (ℓ'' - 1)) * ((k : ℝ) / k) := by
            rw [div_self (ne_of_gt hk_pos), mul_one]
        _ = ((cv c₀ j : ℝ) - (cv c₀ (ℓ'' - 1) : ℝ) - (Lsum α j - Lsum α (ℓ'' - 1)) * k) / k := by ring
        _ ≤ 1 / (k : ℝ) := this
    have h_exp_le : Real.exp ((cv c₀ j : ℝ) / k - (cv c₀ (ℓ'' - 1) : ℝ) / k -
        (Lsum α j - Lsum α (ℓ'' - 1))) ≤ Real.exp (1 / (k : ℝ)) :=
      Real.exp_le_exp.mpr h_exp_arg_le
    have hrj_pos : 0 ≤ r j / Fval α :=
      div_nonneg (le_of_lt (r_pos_of_priceSet hr j hj1 hjm)) (le_of_lt hF_pos)
    have h_rhs_le : (r j / Fval α) *
        Real.exp ((cv c₀ j : ℝ) / k - (cv c₀ (ℓ'' - 1) : ℝ) / k -
          (Lsum α j - Lsum α (ℓ'' - 1))) *
        ((1 + (k : ℝ)) * (1 - Real.exp (-1 / (k : ℝ)))) ≤
        r j / (Fval α / ((1 + (k : ℝ)) * (Real.exp (1 / (k : ℝ)) - 1))) := by
      have h_prod : Real.exp (1 / (k : ℝ)) * (1 - Real.exp (-1 / (k : ℝ))) =
          Real.exp (1 / (k : ℝ)) - 1 := by
        rw [mul_sub, mul_one, ← Real.exp_add]
        have : 1 / (k : ℝ) + -1 / (k : ℝ) = 0 := by ring
        rw [this, Real.exp_zero]
      calc
        (r j / Fval α) *
            Real.exp ((cv c₀ j : ℝ) / k - (cv c₀ (ℓ'' - 1) : ℝ) / k -
              (Lsum α j - Lsum α (ℓ'' - 1))) *
            ((1 + (k : ℝ)) * (1 - Real.exp (-1 / (k : ℝ))))
          ≤ (r j / Fval α) * Real.exp (1 / (k : ℝ)) *
              ((1 + (k : ℝ)) * (1 - Real.exp (-1 / (k : ℝ)))) := by
            apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul_of_nonneg_left h_exp_le hrj_pos
            · linarith
        _ = (r j / Fval α) * ((1 + (k : ℝ)) *
              (Real.exp (1 / (k : ℝ)) * (1 - Real.exp (-1 / (k : ℝ))))) := by ring
        _ = (r j / Fval α) * ((1 + (k : ℝ)) * (Real.exp (1 / (k : ℝ)) - 1)) := by rw [h_prod]
        _ = r j / (Fval α / ((1 + (k : ℝ)) * (Real.exp (1 / (k : ℝ)) - 1))) := by
            rw [div_div_eq_mul_div, mul_div_right_comm]
    exact le_trans h_core h_rhs_le
  · -- Cond17 for m = 1
    intro hm1
    subst hm1
    intro c₀ hρ j hj1 hjm N hN_lt
    have hc₀ : IsConfig c₀ := (hproc.2.2 c₀ hρ).1
    obtain ⟨ℓ'', hℓ'', h_core⟩ := cond17_core hk hm hr hα hc₀ hj1 hjm hN_lt
    rw [mem_Icc] at hℓ''
    have hℓ_bds := ellTilde_bounds hm c₀ N
    have hj_eq1 : j = 1 := by omega
    have hℓ''_eq1 : ℓ'' = 1 := by omega
    subst hj_eq1 hℓ''_eq1
    have hcv1 : cv c₀ 1 = k := cv_m_of_isConfig hc₀
    have hcv0 : cv c₀ 0 = 0 := cv_zero_of_isConfig hc₀
    have hL1 : Lsum α 1 = 1 := hα.2.1
    have hL0 : Lsum α 0 = 0 := Lsum_zero α
    have h_exp0 : (cv c₀ 1 : ℝ) / k - (cv c₀ (1 - 1) : ℝ) / k -
        (Lsum α 1 - Lsum α (1 - 1)) = 0 := by
      change (cv c₀ 1 : ℝ) / k - (cv c₀ 0 : ℝ) / k - (Lsum α 1 - Lsum α 0) = 0
      rw [hcv1, hcv0, hL1, hL0, Nat.cast_zero, zero_div, sub_zero, sub_zero,
          div_self (ne_of_gt hk_pos), sub_self]
    rw [h_exp0, Real.exp_zero, mul_one] at h_core
    have h_rhs_eq : (r 1 / Fval α) * ((1 + (k : ℝ)) * (1 - Real.exp (-1 / (k : ℝ)))) =
        r 1 / (Fval α / ((1 + (k : ℝ)) * (1 - Real.exp (-1 / (k : ℝ))))) := by
      rw [div_div_eq_mul_div, mul_div_right_comm]
    rwa [h_rhs_eq] at h_core
