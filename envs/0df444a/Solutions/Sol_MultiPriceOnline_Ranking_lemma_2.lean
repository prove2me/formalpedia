-- Prove2me | solution 1 for MultiPriceOnline.Ranking.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:25:39.325251+00:00
-- url     : https://prove2.me/submissions/94c03b25-9c28-44a2-9277-0d40b5d60639

import Mathlib
import Definitions.Def_MultiPriceOnline_Ranking_LP
import Definitions.Def_MultiPriceOnline_Ranking_Setting

open MultiPriceOnline.Ranking MultiPriceOnline.Balance Finset

private lemma r_pos_of_priceSet {m : ℕ} {r : ℕ → ℝ} (hr : MultiPriceOnline.Ranking.IsPriceSet m r) :
    ∀ j, 1 ≤ j → j ≤ m → 0 < r j := by
  intro j hj1 hjm
  induction j with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le hj1 with h | h
    · rw [← h]; exact hr.2.1
    · have hk_pos : 0 < r k := ih (by omega) (by omega)
      have hlt : r k < r (k + 1) := hr.2.2 k (by omega) (by omega)
      linarith

private lemma pr_mono {m : ℕ} {r : ℕ → ℝ} (hr : MultiPriceOnline.Ranking.IsPriceSet m r) :
    ∀ j₁ j₂, j₁ ≤ j₂ → j₂ ≤ m → pr r j₁ ≤ pr r j₂ := by
  intro j₁ j₂ h12 h2m
  induction j₂ with
  | zero =>
    have : j₁ = 0 := by omega
    subst this; exact le_rfl
  | succ k ih =>
    rcases eq_or_lt_of_le h12 with rfl | hlt
    · exact le_rfl
    · apply le_trans (ih (by omega) (by omega))
      have h1 : pr r (k + 1) = r (k + 1) := if_neg (by omega)
      rw [h1]
      rcases Nat.eq_zero_or_pos k with rfl | hk_pos
      · change pr r 0 ≤ r 1
        unfold pr
        simp [le_of_lt hr.2.1]
      · have h2 : pr r k = r k := if_neg (by omega)
        rw [h2]
        exact le_of_lt (hr.2.2 k (by omega) (by omega))

private lemma pr_diff_pos {m : ℕ} {r : ℕ → ℝ} (hr : MultiPriceOnline.Ranking.IsPriceSet m r) :
    ∀ j, 1 ≤ j → j ≤ m → 0 < r j - pr r (j - 1) := by
  intro j hj1 hjm
  rcases eq_or_lt_of_le hj1 with h | h
  · rw [← h]
    change 0 < r 1 - pr r 0
    unfold pr
    simp [hr.2.1]
  · have hrj1 : pr r (j - 1) = r (j - 1) := if_neg (by omega)
    rw [hrj1]
    have hlt := hr.2.2 (j - 1) (by omega) (by omega)
    have heq : j - 1 + 1 = j := by omega
    rw [heq] at hlt
    linarith

private lemma booking_mul_identity {m : ℕ} {r α : ℕ → ℝ}
    (hr : MultiPriceOnline.Ranking.IsPriceSet m r) (hα : IsBookingLimits m r α)
    {j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    (1 - Real.exp (-α 1)) *
      ((r j - pr r (j - 1)) / (Real.exp (α j) - 1) + (r j - pr r (j - 1))) = r j := by
  have hαj : 0 < α j := hα.1 j hj1 hjm
  have hexp_pos : 0 < Real.exp (α j) - 1 := by
    rw [sub_pos, Real.one_lt_exp_iff]; exact hαj
  have h1exp_pos : 0 < 1 - Real.exp (-α j) := by
    have : Real.exp (-α j) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have h_sum : (r j - pr r (j - 1)) / (Real.exp (α j) - 1) + (r j - pr r (j - 1)) =
      (r j - pr r (j - 1)) / (1 - Real.exp (-α j)) := by
    have h1 : Real.exp (α j) - 1 = Real.exp (α j) * (1 - Real.exp (-α j)) := by
      rw [mul_sub, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc
      (r j - pr r (j - 1)) / (Real.exp (α j) - 1) + (r j - pr r (j - 1))
        = (r j - pr r (j - 1)) * (1 + (Real.exp (α j) - 1)) / (Real.exp (α j) - 1) := by
          rw [mul_add, mul_one, add_div, mul_div_cancel_right₀ _ (ne_of_gt hexp_pos), add_comm]
      _ = (r j - pr r (j - 1)) * Real.exp (α j) / (Real.exp (α j) * (1 - Real.exp (-α j))) := by
          rw [← h1]; ring_nf
      _ = (r j - pr r (j - 1)) / (1 - Real.exp (-α j)) := by
          rw [mul_comm (Real.exp (α j)), mul_div_mul_right _ _ (ne_of_gt (Real.exp_pos (α j)))]
  rw [h_sum]
  rcases eq_or_lt_of_le hj1 with h | h
  · subst h
    change (1 - Real.exp (-α 1)) * ((r 1 - pr r 0) / (1 - Real.exp (-α 1))) = r 1
    have hpr0 : pr r 0 = 0 := rfl
    rw [hpr0, sub_zero, mul_div_cancel₀ _ (ne_of_gt h1exp_pos)]
  · have hj2 : 2 ≤ j := by omega
    have hrj1 : pr r (j - 1) = r (j - 1) := if_neg (by omega)
    rw [hrj1]
    have h7 := hα.2.2 j hj2 hjm
    have hrj_pos : 0 < r j := r_pos_of_priceSet hr j hj1 hjm
    have hlt : r (j - 1) < r j := by
      have := hr.2.2 (j - 1) (by omega) (by omega)
      rwa [Nat.sub_add_cancel hj1] at this
    have hratio_pos : 0 < 1 - r (j - 1) / r j := by
      rw [sub_pos, div_lt_one hrj_pos]; exact hlt
    have hdiff : r j - r (j - 1) = r j * (1 - r (j - 1) / r j) := by
      calc
        r j - r (j - 1) = r j - r (j - 1) / r j * r j := by
          rw [div_mul_cancel₀ _ (ne_of_gt hrj_pos)]
        _ = r j * (1 - r (j - 1) / r j) := by ring
    rw [h7, hdiff]
    calc
      (1 - Real.exp (-α j)) / (1 - r (j - 1) / r j) *
          (r j * (1 - r (j - 1) / r j) / (1 - Real.exp (-α j)))
        = r j * ((1 - Real.exp (-α j)) / (1 - Real.exp (-α j))) *
            ((1 - r (j - 1) / r j) / (1 - r (j - 1) / r j)) := by ring
      _ = r j * 1 * 1 := by
          rw [div_self (ne_of_gt h1exp_pos), div_self (ne_of_gt hratio_pos)]
      _ = r j := by ring

private lemma L_mono {m : ℕ} {r α : ℕ → ℝ} (hα : IsBookingLimits m r α) :
    ∀ j₁ j₂, j₁ ≤ j₂ → j₂ ≤ m → L α j₁ ≤ L α j₂ := by
  intro j₁ j₂ h12 h2m
  unfold L Lsum
  apply sum_le_sum_of_subset_of_nonneg
  · intro x hx; rw [mem_Icc] at hx ⊢; exact ⟨hx.1, le_trans hx.2 h12⟩
  · intro x hx _; rw [mem_Icc] at hx; exact le_of_lt (hα.1 x hx.1 (le_trans hx.2 h2m))

private lemma filter_antitone_eq_Icc (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ j₁ j₂, 1 ≤ j₁ → j₁ ≤ j₂ → P j₂ → P j₁) :
    ∀ n, (Icc 1 n).filter P = Icc 1 ((Icc 1 n).filter P).card := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hIcc : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    by_cases hn1 : P (n + 1)
    · have hall : (Icc 1 (n + 1)).filter P = Icc 1 (n + 1) := by
        rw [filter_eq_self]
        intro x hx; rw [mem_Icc] at hx
        exact hP x (n + 1) hx.1 hx.2 hn1
      rw [hall, Nat.card_Icc]
      have : n + 1 + 1 - 1 = n + 1 := by omega
      rw [this]
    · rw [hIcc, filter_insert, if_neg hn1]
      exact ih

private lemma ell_bounds (m : ℕ) (hm : 1 ≤ m) (α : ℕ → ℝ) (w : ℝ) :
    1 ≤ ell m α w ∧ ell m α w ≤ m := by
  unfold ell
  have hsub : ((Icc 1 (m - 1)).filter (fun j => L α j ≤ w)).card ≤ (Icc 1 (m - 1)).card :=
    card_filter_le _ _
  rw [Nat.card_Icc] at hsub
  omega

private lemma L_ell_pred_le {m : ℕ} (hm : 1 ≤ m) {r α : ℕ → ℝ} (hα : IsBookingLimits m r α)
    {w : ℝ} (hw0 : 0 ≤ w) : L α (ell m α w - 1) ≤ w := by
  have hbds := ell_bounds m hm α w
  rcases eq_or_lt_of_le hbds.1 with heq | hlt
  · rw [← heq, Nat.sub_self]
    unfold L Lsum
    simp [hw0]
  · have hanti : ∀ j₁ j₂, 1 ≤ j₁ → j₁ ≤ j₂ → j₂ ≤ m - 1 → L α j₂ ≤ w → L α j₁ ≤ w := by
      intro j₁ j₂ _ h12 h2m h2
      exact le_trans (L_mono hα j₁ j₂ h12 (by omega)) h2
    -- Use filter_antitone_eq_Icc on bounded predicate
    let P (j : ℕ) : Prop := j ≤ m - 1 ∧ L α j ≤ w
    have hP_anti : ∀ j₁ j₂, 1 ≤ j₁ → j₁ ≤ j₂ → P j₂ → P j₁ := by
      intro j₁ j₂ hj1 h12 ⟨h2m, h2w⟩
      exact ⟨by omega, le_trans (L_mono hα j₁ j₂ h12 (by omega)) h2w⟩
    have hfilt_eq : (Icc 1 (m - 1)).filter (fun j => L α j ≤ w) = (Icc 1 (m - 1)).filter P := by
      apply filter_congr
      intro j hj
      rw [mem_Icc] at hj
      simp [P, hj.2]
    have hIcc := filter_antitone_eq_Icc P hP_anti (m - 1)
    rw [← hfilt_eq] at hIcc
    have hcard : ell m α w - 1 = ((Icc 1 (m - 1)).filter (fun j => L α j ≤ w)).card := by
      unfold ell; omega
    have hmem : ell m α w - 1 ∈ Icc 1 ((Icc 1 (m - 1)).filter (fun j => L α j ≤ w)).card := by
      rw [← hcard, mem_Icc]
      omega
    rw [← hIcc, mem_filter] at hmem
    exact hmem.2

private lemma pr_ell_pred_le_Phi {m : ℕ} {r α : ℕ → ℝ}
    (hr : MultiPriceOnline.Ranking.IsPriceSet m r) (hα : IsBookingLimits m r α)
    {w : ℝ} (hw0 : 0 ≤ w) :
    pr r (ell m α w - 1) ≤ Phi m r α w := by
  unfold Phi
  have hbds := ell_bounds m hr.1 α w
  have hL := L_ell_pred_le hr.1 hα hw0
  have hpr_pos : 0 ≤ r (ell m α w) - pr r (ell m α w - 1) :=
    le_of_lt (pr_diff_pos hr (ell m α w) hbds.1 hbds.2)
  have hexp_nonneg : 0 ≤ Real.exp (w - L α (ell m α w - 1)) - 1 := by
    rw [sub_nonneg, Real.one_le_exp_iff]
    linarith
  have hα_pos : 0 < Real.exp (α (ell m α w)) - 1 := by
    rw [sub_pos, Real.one_lt_exp_iff]
    exact hα.1 (ell m α w) hbds.1 hbds.2
  have hdiv_nonneg : 0 ≤ (r (ell m α w) - pr r (ell m α w - 1)) *
      (Real.exp (w - L α (ell m α w - 1)) - 1) / (Real.exp (α (ell m α w)) - 1) :=
    div_nonneg (mul_nonneg hpr_pos hexp_nonneg) (le_of_lt hα_pos)
  linarith

private lemma jt_le_m {n : ℕ} (m : Fin n → ℕ) (q : Fin n → ℕ → ℝ) (i : Fin n) :
    jt m q i ≤ m i := by
  unfold jt
  apply Finset.sup_le
  intro j hj
  rw [mem_Icc] at hj
  split_ifs
  · exact hj.2
  · exact Nat.zero_le _

theorem solution {n T : ℕ} (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (hr : ∀ i, MultiPriceOnline.Ranking.IsPriceSet (m i) (r i))
    (hα : ∀ i, IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) (_hp : IsDeterministic m p)
    (sel : Selector n T) (_hsel : IsArgmaxSelector sel)
    (W : Fin n → ℝ) (hW : ∀ i, W i ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin n) (t : Fin T) (hti : run2 m r α p sel Finset.univ W t = some i) :
    (1 - Real.exp (-α i 1)) *
        (Yi m r α p sel Finset.univ W i + Zt m r α p sel Finset.univ W t) ≤
      pr (r i) (jt m (p t) i) := by
  have hYi : Yi m r α p sel Finset.univ W i = PhiDeriv (m i) (r i) (α i) (W i) := by
    unfold Yi
    exact if_pos ⟨t, hti⟩
  have hZt : Zt m r α p sel Finset.univ W t = score m r α (p t) W i := by
    unfold Zt
    rw [hti]
  have hscore_pos : 0 < score m r α (p t) W i := by
    unfold run2 offer at hti
    split_ifs at hti with h1 h2
    injection hti with h_eq
    rw [← h_eq]
    exact h2
  rw [hYi, hZt]
  unfold score at hscore_pos ⊢
  set j := jt m (p t) i
  set ℓ := ell (m i) (α i) (W i)
  have hℓ_bds := ell_bounds (m i) (hr i).1 (α i) (W i)
  have hj_le_m : j ≤ m i := jt_le_m m (p t) i
  have hpr_ell_le_phi : pr (r i) (ℓ - 1) ≤ Phi (m i) (r i) (α i) (W i) :=
    pr_ell_pred_le_Phi (hr i) (hα i) (hW i).1
  have hpr_lt : pr (r i) (ℓ - 1) < pr (r i) j := by linarith
  have hℓ_le_j : ℓ ≤ j := by
    by_contra hgt
    have hj_le : j ≤ ℓ - 1 := by omega
    have hle := pr_mono (hr i) j (ℓ - 1) hj_le (by omega)
    linarith
  have hpr_ℓ_le_j : r i ℓ ≤ pr (r i) j := by
    have hle := pr_mono (hr i) ℓ j hℓ_le_j hj_le_m
    have hpr_ℓ : pr (r i) ℓ = r i ℓ := if_neg (by omega)
    rwa [hpr_ℓ] at hle
  have h_diff : PhiDeriv (m i) (r i) (α i) (W i) +
      (pr (r i) j - Phi (m i) (r i) (α i) (W i)) =
      ((r i ℓ - pr (r i) (ℓ - 1)) / (Real.exp (α i ℓ) - 1) + (r i ℓ - pr (r i) (ℓ - 1))) +
        (pr (r i) j - r i ℓ) := by
    unfold PhiDeriv Phi
    change (r i ℓ - pr (r i) (ℓ - 1)) * Real.exp (W i - L (α i) (ℓ - 1)) / (Real.exp (α i ℓ) - 1) +
        (pr (r i) j - (pr (r i) (ℓ - 1) +
          (r i ℓ - pr (r i) (ℓ - 1)) * (Real.exp (W i - L (α i) (ℓ - 1)) - 1) / (Real.exp (α i ℓ) - 1))) = _
    ring
  rw [h_diff, mul_add, booking_mul_identity (hr i) (hα i) hℓ_bds.1 hℓ_bds.2]
  have hF_le1 : 1 - Real.exp (-α i 1) ≤ 1 := by
    have : 0 < Real.exp (-α i 1) := Real.exp_pos _
    linarith
  nlinarith
