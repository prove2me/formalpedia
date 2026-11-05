-- Prove2me | solution 1 for MultiPriceOnline.Ranking.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T08:01:36.693514+00:00
-- url     : https://prove2.me/submissions/f031350e-ce2f-414d-9ae1-6a199f5b8f96

import Mathlib
import Definitions.Def_MultiPriceOnline_Ranking_LP
import Definitions.Def_MultiPriceOnline_Ranking_Setting
import Theorems.Thm_MultiPriceOnline_Ranking_dominance_claim
import Theorems.Thm_MultiPriceOnline_Ranking_monotonicity_claim

open MeasureTheory MultiPriceOnline.Ranking Finset

namespace MPR3Aux

local notation "prr" => MultiPriceOnline.Balance.pr

lemma pr_diff_pos {m : ℕ} {r : ℕ → ℝ} (hr : MultiPriceOnline.Ranking.IsPriceSet m r) :
    ∀ j, 1 ≤ j → j ≤ m → 0 < r j - prr r (j - 1) := by
  intro j hj1 hjm
  rcases eq_or_lt_of_le hj1 with h | h
  · rw [← h]
    change 0 < r 1 - MultiPriceOnline.Balance.pr r 0
    unfold MultiPriceOnline.Balance.pr
    simp [hr.2.1]
  · have hrj1 : MultiPriceOnline.Balance.pr r (j - 1) = r (j - 1) := if_neg (by omega)
    rw [hrj1]
    have hlt := hr.2.2 (j - 1) (by omega) (by omega)
    have heq : j - 1 + 1 = j := by omega
    rw [heq] at hlt
    linarith

lemma pr_mono {m : ℕ} {r : ℕ → ℝ} (hr : MultiPriceOnline.Ranking.IsPriceSet m r) :
    ∀ j₁ j₂, j₁ ≤ j₂ → j₂ ≤ m → prr r j₁ ≤ prr r j₂ := by
  intro j₁ j₂ h12 h2m
  induction j₂ with
  | zero =>
    have : j₁ = 0 := by omega
    subst this; exact le_rfl
  | succ k ih =>
    rcases eq_or_lt_of_le h12 with rfl | hlt
    · exact le_rfl
    · apply le_trans (ih (by omega) (by omega))
      have h1 := pr_diff_pos hr (k + 1) (by omega) h2m
      have h2 : prr r (k + 1) = r (k + 1) := if_neg (by omega)
      simp only [Nat.add_sub_cancel] at h1
      linarith

lemma pr_nonneg {m : ℕ} {r : ℕ → ℝ} (hr : MultiPriceOnline.Ranking.IsPriceSet m r) :
    ∀ j, j ≤ m → 0 ≤ prr r j := by
  intro j hj
  have := pr_mono hr 0 j (Nat.zero_le _) hj
  simpa [MultiPriceOnline.Balance.pr] using this

lemma ell_bounds (m : ℕ) (hm : 1 ≤ m) (α : ℕ → ℝ) (w : ℝ) :
    1 ≤ ell m α w ∧ ell m α w ≤ m := by
  unfold ell
  have hsub : ((Icc 1 (m - 1)).filter (fun j => L α j ≤ w)).card ≤ (Icc 1 (m - 1)).card :=
    card_filter_le _ _
  rw [Nat.card_Icc] at hsub
  omega

lemma L_mono {m : ℕ} {r α : ℕ → ℝ} (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) :
    ∀ j₁ j₂, j₁ ≤ j₂ → j₂ ≤ m → L α j₁ ≤ L α j₂ := by
  intro j₁ j₂ h12 h2m
  unfold L MultiPriceOnline.Balance.Lsum
  apply sum_le_sum_of_subset_of_nonneg
  · intro x hx; rw [mem_Icc] at hx ⊢; exact ⟨hx.1, le_trans hx.2 h12⟩
  · intro x hx _; rw [mem_Icc] at hx; exact le_of_lt (hα.1 x hx.1 (le_trans hx.2 h2m))

lemma L_zero (α : ℕ → ℝ) : L α 0 = 0 := by
  simp [L, MultiPriceOnline.Balance.Lsum]

lemma L_succ (α : ℕ → ℝ) (j : ℕ) : L α (j + 1) = L α j + α (j + 1) := by
  simp only [L, MultiPriceOnline.Balance.Lsum]
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma L_nonneg {m : ℕ} {r α : ℕ → ℝ} (hα : MultiPriceOnline.Balance.IsBookingLimits m r α)
    (j : ℕ) (hj : j ≤ m) : 0 ≤ L α j := by
  have := L_mono hα 0 j (Nat.zero_le _) hj
  rwa [L_zero] at this

lemma L_top {m : ℕ} {r α : ℕ → ℝ} (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) :
    L α m = 1 := hα.2.1

/-- `L^{(ℓ(w)-1)} ≤ w` for `w ≥ 0`. -/
lemma L_ell_pred_le {m : ℕ} (hm : 1 ≤ m) {r α : ℕ → ℝ}
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α)
    {w : ℝ} (hw0 : 0 ≤ w) : L α (ell m α w - 1) ≤ w := by
  set c := ((Icc 1 (m - 1)).filter (fun j => L α j ≤ w)).card with hc
  have hell : ell m α w - 1 = c := by unfold ell; omega
  rw [hell]
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · rw [h0, L_zero]; exact hw0
  · -- the filter is an initial segment; its largest element is `≥ c`
    by_contra hlt
    push Not at hlt
    -- every element `j` of the filter satisfies `j < c`
    have hsub : (Icc 1 (m - 1)).filter (fun j => L α j ≤ w) ⊆ Icc 1 (c - 1) := by
      intro j hj
      rw [mem_filter, mem_Icc] at hj
      rw [mem_Icc]
      refine ⟨hj.1.1, ?_⟩
      by_contra hjc
      push Not at hjc
      have hcm : c ≤ m - 1 := by
        have := card_filter_le (Icc 1 (m - 1)) (fun j => L α j ≤ w)
        rw [Nat.card_Icc] at this; omega
      have := L_mono hα c j (by omega) (by omega)
      linarith [hj.2]
    have := card_le_card hsub
    rw [Nat.card_Icc, ← hc] at this
    omega

/-- If `ℓ(w) < m` then `w < L^{(ℓ(w))}`. -/
lemma lt_L_ell {m : ℕ} {r α : ℕ → ℝ} (hα : MultiPriceOnline.Balance.IsBookingLimits m r α)
    {w : ℝ} (h : ell m α w < m) : w < L α (ell m α w) := by
  by_contra hle
  push Not at hle
  set c := ((Icc 1 (m - 1)).filter (fun j => L α j ≤ w)).card with hc
  have hell : ell m α w = 1 + c := rfl
  have hsub : Icc 1 (1 + c) ⊆ (Icc 1 (m - 1)).filter (fun j => L α j ≤ w) := by
    intro j hj
    rw [mem_Icc] at hj
    rw [mem_filter, mem_Icc]
    refine ⟨⟨hj.1, by omega⟩, ?_⟩
    have := L_mono hα j (1 + c) hj.2 (by omega)
    rw [← hell] at this
    linarith
  have := card_le_card hsub
  rw [Nat.card_Icc, ← hc] at this
  omega

/-- The branch of `Φ` on segment `k`. -/
noncomputable def G (r α : ℕ → ℝ) (k : ℕ) (w : ℝ) : ℝ :=
  prr r (k - 1) + (r k - prr r (k - 1)) * (Real.exp (w - L α (k - 1)) - 1) / (Real.exp (α k) - 1)

/-- The derivative of the branch `G k`. -/
noncomputable def G' (r α : ℕ → ℝ) (k : ℕ) (w : ℝ) : ℝ :=
  (r k - prr r (k - 1)) * Real.exp (w - L α (k - 1)) / (Real.exp (α k) - 1)

lemma Phi_eq_G (m : ℕ) (r α : ℕ → ℝ) (w : ℝ) : Phi m r α w = G r α (ell m α w) w := rfl

lemma PhiDeriv_eq_G' (m : ℕ) (r α : ℕ → ℝ) (w : ℝ) :
    PhiDeriv m r α w = G' r α (ell m α w) w := rfl

lemma hasDerivAt_G (r α : ℕ → ℝ) (k : ℕ) (w : ℝ) : HasDerivAt (G r α k) (G' r α k w) w := by
  unfold G G'
  have h1 : HasDerivAt (fun w => Real.exp (w - L α (k - 1))) (Real.exp (w - L α (k - 1)) * 1) w :=
    ((hasDerivAt_id w).sub_const _).exp
  have h2 := ((h1.sub_const 1).const_mul (r k - prr r (k - 1))).div_const (Real.exp (α k) - 1)
  have h3 := h2.const_add (prr r (k - 1))
  rw [mul_one] at h3
  exact h3

lemma continuous_G' (r α : ℕ → ℝ) (k : ℕ) : Continuous (G' r α k) := by
  unfold G'; fun_prop

lemma G_strictMono {m : ℕ} {r α : ℕ → ℝ} (hr : MultiPriceOnline.Ranking.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) {k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    StrictMono (G r α k) := by
  intro x y hxy
  unfold G
  have hb := pr_diff_pos hr k hk1 hkm
  have hd : 0 < Real.exp (α k) - 1 := by
    rw [sub_pos, Real.one_lt_exp_iff]; exact hα.1 _ hk1 hkm
  have he : Real.exp (x - L α (k - 1)) < Real.exp (y - L α (k - 1)) :=
    Real.exp_lt_exp.2 (by linarith)
  have : (r k - prr r (k - 1)) * (Real.exp (x - L α (k - 1)) - 1) <
      (r k - prr r (k - 1)) * (Real.exp (y - L α (k - 1)) - 1) :=
    mul_lt_mul_of_pos_left (by linarith) hb
  have := div_lt_div_of_pos_right this hd
  linarith

lemma G_left (r α : ℕ → ℝ) (k : ℕ) : G r α k (L α (k - 1)) = prr r (k - 1) := by
  unfold G; simp

lemma G_right {m : ℕ} {r α : ℕ → ℝ} (hα : MultiPriceOnline.Balance.IsBookingLimits m r α)
    {k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m) : G r α k (L α k) = r k := by
  unfold G
  have hd : 0 < Real.exp (α k) - 1 := by
    rw [sub_pos, Real.one_lt_exp_iff]; exact hα.1 _ hk1 hkm
  have hL : L α k - L α (k - 1) = α k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [L_succ]; simp
  rw [hL]
  field_simp
  ring

/-- On the segment `[L^{(k-1)}, L^{(k)})` (unbounded above for `k = m`), `ℓ = k`. -/
lemma ell_eq_of_mem {m : ℕ} (hm : 1 ≤ m) {r α : ℕ → ℝ}
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) {k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m)
    {x : ℝ} (hx1 : L α (k - 1) ≤ x) (hx2 : k < m → x < L α k) : ell m α x = k := by
  have hx0 : 0 ≤ x := le_trans (L_nonneg hα _ (by omega)) hx1
  have hb := ell_bounds m hm α x
  rcases lt_trichotomy (ell m α x) k with h | h | h
  · have h1 := lt_L_ell hα (show ell m α x < m by omega)
    have h2 := L_mono hα (ell m α x) (k - 1) (by omega) (by omega)
    linarith
  · exact h
  · have h1 := L_ell_pred_le hm hα hx0
    have h2 := L_mono hα k (ell m α x - 1) (by omega) (by omega)
    have h3 := hx2 (by omega)
    linarith

lemma ell_le_of_lt {m : ℕ} (hm : 1 ≤ m) {r α : ℕ → ℝ}
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) {k : ℕ} (hkm : k ≤ m)
    {x : ℝ} (hx0 : 0 ≤ x) (hx : x < L α k) : ell m α x ≤ k := by
  by_contra h
  push Not at h
  have hb := ell_bounds m hm α x
  have h1 := L_ell_pred_le hm hα hx0
  have h2 := L_mono hα k (ell m α x - 1) (by omega) (by omega)
  linarith

lemma Phi_meas (m : ℕ) (r α : ℕ → ℝ) : Measurable (Phi m r α) := by
  have hmono : Monotone (ell m α) := by
    intro w w' hww'
    unfold ell
    apply Nat.add_le_add_left
    apply card_le_card
    intro j hj
    simp only [mem_filter] at hj ⊢
    exact ⟨hj.1, le_trans hj.2 hww'⟩
  have h : Measurable (fun q : ℝ × ℕ => G r α q.2 q.1) := by
    apply measurable_from_prod_countable_left
    intro k
    unfold G
    fun_prop
  exact h.comp (measurable_id.prodMk hmono.measurable)

lemma PhiDeriv_meas (m : ℕ) (r α : ℕ → ℝ) : Measurable (PhiDeriv m r α) := by
  have hmono : Monotone (ell m α) := by
    intro w w' hww'
    unfold ell
    apply Nat.add_le_add_left
    apply card_le_card
    intro j hj
    simp only [mem_filter] at hj ⊢
    exact ⟨hj.1, le_trans hj.2 hww'⟩
  have h : Measurable (fun q : ℝ × ℕ => G' r α q.2 q.1) := by
    apply measurable_from_prod_countable_left
    intro k
    exact (continuous_G' r α k).measurable
  exact h.comp (measurable_id.prodMk hmono.measurable)

lemma PhiDeriv_nonneg {m : ℕ} {r α : ℕ → ℝ} (hr : MultiPriceOnline.Ranking.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) (w : ℝ) : 0 ≤ PhiDeriv m r α w := by
  unfold PhiDeriv
  have hb := ell_bounds m hr.1 α w
  have h1 := pr_diff_pos hr _ hb.1 hb.2
  have h2 : 0 < Real.exp (α (ell m α w)) - 1 := by
    rw [sub_pos, Real.one_lt_exp_iff]; exact hα.1 _ hb.1 hb.2
  positivity

/-- A bound for `Φ'` on `[0, 1]`. -/
noncomputable def DB (m : ℕ) (r α : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Icc 1 m, (r k - prr r (k - 1)) * Real.exp 1 / (Real.exp (α k) - 1)

lemma PhiDeriv_le {m : ℕ} {r α : ℕ → ℝ} (hr : MultiPriceOnline.Ranking.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    PhiDeriv m r α w ≤ DB m r α := by
  have hb := ell_bounds m hr.1 α w
  have hterm : ∀ k ∈ Icc 1 m, 0 ≤ (r k - prr r (k - 1)) * Real.exp 1 / (Real.exp (α k) - 1) := by
    intro k hk
    rw [mem_Icc] at hk
    have h1 := pr_diff_pos hr k hk.1 hk.2
    have h2 : 0 < Real.exp (α k) - 1 := by
      rw [sub_pos, Real.one_lt_exp_iff]; exact hα.1 _ hk.1 hk.2
    positivity
  refine le_trans ?_ (Finset.single_le_sum hterm (mem_Icc.2 hb))
  unfold PhiDeriv
  have h1 := pr_diff_pos hr _ hb.1 hb.2
  have h2 : 0 < Real.exp (α (ell m α w)) - 1 := by
    rw [sub_pos, Real.one_lt_exp_iff]; exact hα.1 _ hb.1 hb.2
  apply div_le_div_of_nonneg_right _ h2.le
  apply mul_le_mul_of_nonneg_left _ h1.le
  apply Real.exp_le_exp.2
  have := L_nonneg hα (ell m α w - 1) (by omega)
  linarith [hw.2]

lemma Phi_nonneg {m : ℕ} {r α : ℕ → ℝ} (hr : MultiPriceOnline.Ranking.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) {w : ℝ} (hw0 : 0 ≤ w) :
    0 ≤ Phi m r α w := by
  unfold Phi
  have hb := ell_bounds m hr.1 α w
  have hL := L_ell_pred_le hr.1 hα hw0
  have h0 := pr_nonneg hr (ell m α w - 1) (by omega)
  have h1 := pr_diff_pos hr _ hb.1 hb.2
  have h2 : 0 < Real.exp (α (ell m α w)) - 1 := by
    rw [sub_pos, Real.one_lt_exp_iff]; exact hα.1 _ hb.1 hb.2
  have h3 : 0 ≤ Real.exp (w - L α (ell m α w - 1)) - 1 := by
    rw [sub_nonneg, Real.one_le_exp_iff]; linarith
  have : 0 ≤ (r (ell m α w) - prr r (ell m α w - 1)) *
      (Real.exp (w - L α (ell m α w - 1)) - 1) / (Real.exp (α (ell m α w)) - 1) := by positivity
  linarith

/-! ### The integral of `Φ'` -/

/-- On a sub-interval of segment `k`, the integral of `Φ'` is the increment of `G k`. -/
lemma integral_PhiDeriv_seg {m : ℕ} {r α : ℕ → ℝ} (hr : MultiPriceOnline.Ranking.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) {k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m)
    {u v : ℝ} (hu : L α (k - 1) ≤ u) (huv : u ≤ v) (hv : v ≤ L α k) :
    IntervalIntegrable (PhiDeriv m r α) volume u v ∧
      ∫ x in u..v, PhiDeriv m r α x = G r α k v - G r α k u := by
  have heq : Set.EqOn (PhiDeriv m r α) (G' r α k) (Set.Ico u v) := by
    intro x hx
    rw [PhiDeriv_eq_G', ell_eq_of_mem hr.1 hα hk1 hkm (le_trans hu hx.1)
      (fun _ => lt_of_lt_of_le hx.2 hv)]
  have hint' : IntervalIntegrable (G' r α k) volume u v :=
    (continuous_G' r α k).intervalIntegrable u v
  have hset : ∫ x in u..v, PhiDeriv m r α x = ∫ x in u..v, G' r α k x := by
    rw [intervalIntegral.integral_of_le huv, intervalIntegral.integral_of_le huv,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
      ← integral_Ico_eq_integral_Ioo, ← integral_Ico_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ico heq
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le huv]
    have h2 := (intervalIntegrable_iff_integrableOn_Ioo_of_le huv).1 hint'
    exact h2.congr_fun (fun x hx => (heq ⟨hx.1.le, hx.2⟩).symm) measurableSet_Ioo
  · rw [hset, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_G r α k x) hint']

/-- `∫_0^{L^{(j)}} Φ' = r^{(j)}` (with `r^{(0)} = 0`). -/
lemma integral_PhiDeriv_L {m : ℕ} {r α : ℕ → ℝ} (hr : MultiPriceOnline.Ranking.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) :
    ∀ j, j ≤ m → IntervalIntegrable (PhiDeriv m r α) volume 0 (L α j) ∧
      ∫ x in (0 : ℝ)..(L α j), PhiDeriv m r α x = prr r j := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [L_zero]
    simp [MultiPriceOnline.Balance.pr]
  | succ j ih =>
    intro hj
    obtain ⟨hi1, he1⟩ := ih (by omega)
    have hseg := integral_PhiDeriv_seg hr hα (k := j + 1) (by omega) hj (u := L α j) (v := L α (j + 1))
      (by simp) (L_mono hα j (j + 1) (by omega) hj) le_rfl
    refine ⟨hi1.trans hseg.1, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hseg.1, he1, hseg.2,
      G_right hα (by omega) hj]
    have := G_left r α (j + 1)
    simp only [Nat.add_sub_cancel] at this
    rw [this]
    have h1 : prr r (j + 1) = r (j + 1) := if_neg (by omega)
    rw [h1]; ring

/-- The one-dimensional estimate behind Lemma 3: for `0 < a ≤ r^{(J)}`, `J ≤ m`,
`∫_{[0,1]} 1{Φ(x) < a} Φ'(x) dx ≥ a`. -/
lemma oneD {m : ℕ} {r α : ℕ → ℝ} (hr : MultiPriceOnline.Ranking.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) {J : ℕ} (hJ : J ≤ m)
    {a : ℝ} (ha : 0 < a) (haJ : a ≤ prr r J) :
    a ≤ ∫ x in Set.Icc (0 : ℝ) 1, (if Phi m r α x < a then PhiDeriv m r α x else 0) := by
  have hm := hr.1
  have hex : ∃ k, a ≤ prr r k ∧ k ≤ m := ⟨J, haJ, hJ⟩
  classical
  let k := Nat.find hex
  have hk : a ≤ prr r k ∧ k ≤ m := Nat.find_spec hex
  have hk1 : 1 ≤ k := by
    by_contra h0
    have : k = 0 := by omega
    have h := hk.1
    rw [this] at h
    simp [MultiPriceOnline.Balance.pr] at h
    linarith
  have hkm := hk.2
  have hprev : prr r (k - 1) < a := by
    by_contra hle
    push Not at hle
    have := Nat.find_min' hex ⟨hle, by omega⟩
    omega
  have hrk : prr r k = r k := if_neg (by omega)
  have hb := pr_diff_pos hr k hk1 hkm
  have hd : 0 < Real.exp (α k) - 1 := by
    rw [sub_pos, Real.one_lt_exp_iff]; exact hα.1 _ hk1 hkm
  set q := 1 + (a - prr r (k - 1)) * (Real.exp (α k) - 1) / (r k - prr r (k - 1)) with hq
  have hq1 : 1 ≤ q := by
    have : 0 ≤ (a - prr r (k - 1)) * (Real.exp (α k) - 1) / (r k - prr r (k - 1)) := by
      apply div_nonneg _ hb.le; apply mul_nonneg (by linarith) hd.le
    linarith
  have hqpos : 0 < q := by linarith
  have hqle : q ≤ Real.exp (α k) := by
    have : (a - prr r (k - 1)) * (Real.exp (α k) - 1) / (r k - prr r (k - 1)) ≤
        Real.exp (α k) - 1 := by
      rw [div_le_iff₀ hb]
      have : a - prr r (k - 1) ≤ r k - prr r (k - 1) := by linarith [hk.1, hrk]
      nlinarith
    linarith
  set w := L α (k - 1) + Real.log q with hw
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlogq : Real.log q ≤ α k := by
    rw [← Real.log_exp (α k)]; exact Real.log_le_log hqpos hqle
  have hLk : L α k = L α (k - 1) + α k := by
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hj, L_succ]; simp
  have hw1 : L α (k - 1) ≤ w := by linarith
  have hw2 : w ≤ L α k := by linarith
  have hw0 : 0 ≤ w := le_trans (L_nonneg hα _ (by omega)) hw1
  have hw3 : w ≤ 1 := by
    have := L_mono hα k m hkm le_rfl
    rw [L_top hα] at this; linarith
  have hGw : G r α k w = a := by
    unfold G
    have : w - L α (k - 1) = Real.log q := by rw [hw]; ring
    rw [this, Real.exp_log hqpos, hq]
    field_simp
    ring
  -- the integral up to `w`
  have hseg := integral_PhiDeriv_seg hr hα hk1 hkm hw1 le_rfl hw2
  have hseg' := integral_PhiDeriv_seg hr hα hk1 hkm (le_refl _) hw1 hw2
  obtain ⟨hI1, hE1⟩ := integral_PhiDeriv_L hr hα (k - 1) (by omega)
  have hint0w : ∫ x in (0 : ℝ)..w, PhiDeriv m r α x = a := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hseg'.1, hE1, hseg'.2, hGw,
      G_left]; ring
  -- the integrand
  set f : ℝ → ℝ := fun x => if Phi m r α x < a then PhiDeriv m r α x else 0 with hf
  have hfmeas : Measurable f :=
    Measurable.ite (measurableSet_lt (Phi_meas m r α) measurable_const) (PhiDeriv_meas m r α)
      measurable_const
  have hfnn : ∀ x, 0 ≤ f x := by
    intro x; simp only [hf]; split_ifs
    · exact PhiDeriv_nonneg hr hα x
    · exact le_rfl
  have hfint : IntegrableOn f (Set.Icc (0 : ℝ) 1) := by
    refine Measure.integrableOn_of_bounded (M := DB m r α) (by simp) hfmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hfnn x)]
    simp only [hf]; split_ifs
    · exact PhiDeriv_le hr hα hx
    · have := PhiDeriv_le hr hα hx
      have := PhiDeriv_nonneg hr hα x
      linarith
  have hEq : Set.EqOn f (PhiDeriv m r α) (Set.Ico 0 w) := by
    intro x hx
    simp only [hf]
    rw [if_pos]
    have hx0 := hx.1
    have hl := ell_le_of_lt hm hα hkm hx0 (lt_of_lt_of_le hx.2 hw2)
    have hb' := ell_bounds m hm α x
    rcases eq_or_lt_of_le hl with hl | hl
    · rw [Phi_eq_G, hl, ← hGw]
      exact G_strictMono hr hα hk1 hkm hx.2
    · rw [Phi_eq_G]
      have hlt := lt_L_ell hα (show ell m α x < m by omega)
      have h1 := G_strictMono hr hα hb'.1 hb'.2 hlt
      rw [G_right hα hb'.1 hb'.2] at h1
      have h2 := pr_mono hr (ell m α x) (k - 1) (by omega) (by omega)
      have h3 : prr r (ell m α x) = r (ell m α x) := if_neg (by omega)
      linarith
  calc a = ∫ x in (0 : ℝ)..w, PhiDeriv m r α x := hint0w.symm
    _ = ∫ x in Set.Ico 0 w, f x := by
        rw [intervalIntegral.integral_of_le hw0, integral_Ioc_eq_integral_Ioo,
          ← integral_Ico_eq_integral_Ioo]
        exact (setIntegral_congr_fun measurableSet_Ico hEq).symm
    _ ≤ ∫ x in Set.Icc (0 : ℝ) 1, f x := by
        apply setIntegral_mono_set hfint
        · exact Filter.Eventually.of_forall hfnn
        · exact Filter.Eventually.of_forall fun x hx => ⟨hx.1, le_trans hx.2.le hw3⟩

/-- Level sets of `Φ` are Lebesgue-null. -/
lemma Phi_level_null {m : ℕ} {r α : ℕ → ℝ} (hr : MultiPriceOnline.Ranking.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) (c : ℝ) :
    (volume : Measure ℝ) {w | Phi m r α w = c} = 0 := by
  have hsub : {w | Phi m r α w = c} ⊆ ⋃ k : ℕ, {w | 1 ≤ k ∧ k ≤ m ∧ G r α k w = c} := by
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw
    have hb := ell_bounds m hr.1 α w
    exact Set.mem_iUnion.2 ⟨ell m α w, hb.1, hb.2, hw⟩
  refine measure_mono_null hsub (measure_iUnion_null_iff.2 fun k => ?_)
  apply Set.Subsingleton.measure_zero
  rintro w1 ⟨hk1, hkm, h1⟩ w2 ⟨-, -, h2⟩
  have hb := pr_diff_pos hr k hk1 hkm
  have hd : 0 < Real.exp (α k) - 1 := by
    rw [sub_pos, Real.one_lt_exp_iff]; exact hα.1 _ hk1 hkm
  unfold G at h1 h2
  have he : Real.exp (w1 - L α (k - 1)) = Real.exp (w2 - L α (k - 1)) := by
    have h3 : (r k - MultiPriceOnline.Balance.pr r (k - 1)) *
        (Real.exp (w1 - L α (k - 1)) - 1) / (Real.exp (α k) - 1) =
        (r k - MultiPriceOnline.Balance.pr r (k - 1)) *
        (Real.exp (w2 - L α (k - 1)) - 1) / (Real.exp (α k) - 1) := by linarith
    rw [div_left_inj' hd.ne', mul_right_inj' hb.ne'] at h3
    linarith
  have := Real.exp_injective he
  linarith

/-! ### A two-coordinate null-set lemma for product measures -/

lemma null_pair {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)] {i i' : Fin n}
    (h : i ≠ i') {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hslice : ∀ c, μ i {x | f x = c} = 0) :
    Measure.pi μ {W | f (W i) = g (W i')} = 0 := by
  cases n with
  | zero => exact i.elim0
  | succ k =>
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (x := i') (y := i) (Ne.symm h)
    have hmp := measurePreserving_piFinSuccAbove μ i
    set S : Set (ℝ × (Fin k → ℝ)) := {q | f q.1 = g (q.2 j)} with hSdef
    have hS : MeasurableSet S :=
      measurableSet_eq_fun (hf.comp measurable_fst)
        (hg.comp ((measurable_pi_apply j).comp measurable_snd))
    have hpre : {W : Fin (k + 1) → ℝ | f (W i) = g (W i')} =
        (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i) ⁻¹' S := by
      ext W
      simp [S, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.removeNth, hj]
    rw [hpre, hmp.measure_preimage hS.nullMeasurableSet, Measure.prod_apply_symm hS]
    simp [S, hslice]

/-! ### Measurability -/

variable {n T : ℕ}

lemma score_meas (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (q : Fin n → ℕ → ℝ) (i : Fin n) :
    Measurable (fun W : Fin n → ℝ => score m r α q W i) := by
  unfold score
  exact measurable_const.sub ((Phi_meas _ _ _).comp (measurable_pi_apply i))

lemma scorevec_meas (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (q : Fin n → ℕ → ℝ) :
    Measurable (fun W : Fin n → ℝ => score m r α q W) :=
  measurable_pi_lambda _ fun i => score_meas m r α q i

/-- An explicit argmax rule: the smallest maximizer. -/
noncomputable def amax (C : Finset (Fin n)) (hC : C.Nonempty) (s : Fin n → ℝ) : Fin n :=
  (C.filter (fun i => ∀ j ∈ C, s j ≤ s i)).min' (by
    obtain ⟨i, hi, hmax⟩ := C.exists_max_image s hC
    exact ⟨i, mem_filter.2 ⟨hi, hmax⟩⟩)

lemma amax_spec (C : Finset (Fin n)) (hC : C.Nonempty) (s : Fin n → ℝ) :
    amax C hC s ∈ C ∧ ∀ j ∈ C, s j ≤ s (amax C hC s) := by
  have := min'_mem (C.filter (fun i => ∀ j ∈ C, s j ≤ s i)) (by
    obtain ⟨i, hi, hmax⟩ := C.exists_max_image s hC
    exact ⟨i, mem_filter.2 ⟨hi, hmax⟩⟩)
  exact mem_filter.1 this

lemma amax_meas (C : Finset (Fin n)) (hC : C.Nonempty) :
    Measurable (fun s : Fin n → ℝ => amax C hC s) := by
  apply measurable_to_countable'
  intro i
  have hset : (fun s : Fin n → ℝ => amax C hC s) ⁻¹' {i} =
      {s | (i ∈ C ∧ ∀ j ∈ C, s j ≤ s i) ∧
        ∀ b, (b ∈ C ∧ ∀ j ∈ C, s j ≤ s b) → i ≤ b} := by
    ext s
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, amax,
      min'_eq_iff, mem_filter]
  rw [hset]
  have hle : ∀ a b : Fin n, Measurable (fun s : Fin n → ℝ => s a ≤ s b) := fun a b =>
    measurableSet_setOfPred.1 (measurableSet_le (measurable_pi_apply a) (measurable_pi_apply b))
  apply measurableSet_setOfPred.2
  apply Measurable.and
  · apply Measurable.and measurable_const
    exact Measurable.forall fun j => Measurable.imp measurable_const (hle j i)
  · exact Measurable.forall fun b => Measurable.imp
      (Measurable.and measurable_const
        (Measurable.forall fun j => Measurable.imp measurable_const (hle j b)))
      measurable_const

/-- The selector `amax`. -/
noncomputable def sel0 : Selector n T := fun _ C hC s => amax C hC s

lemma sel0_argmax : IsArgmaxSelector (sel0 : Selector n T) := fun _ C hC s => amax_spec C hC s

lemma offer_meas {γ : Type*} [MeasurableSpace γ] (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (t : Fin T) (q : Fin n → ℕ → ℝ) (A : Finset (Fin n)) (φ : Option (Fin n) → γ) :
    Measurable (fun W => φ (offer m r α (sel0 : Selector n T) t q W A)) := by
  by_cases h : A.Nonempty
  · have hfun : (fun W => φ (offer m r α (sel0 : Selector n T) t q W A)) =
        fun W => (fun x : (Fin n → ℝ) × Fin n =>
          if 0 < score m r α q x.1 x.2 then φ (some x.2) else φ none)
          (W, amax A h (score m r α q W)) := by
      funext W
      simp only [offer, dif_pos h, sel0]
      by_cases hh : 0 < score m r α q W (amax A h (score m r α q W)) <;> simp only [hh, if_true, if_false]
    rw [hfun]
    have hg : Measurable (fun x : (Fin n → ℝ) × Fin n =>
          if 0 < score m r α q x.1 x.2 then φ (some x.2) else φ none) := by
      apply measurable_from_prod_countable_left
      intro i
      dsimp only
      exact Measurable.ite (measurableSet_lt measurable_const (score_meas m r α q i))
        measurable_const measurable_const
    exact hg.comp (measurable_id.prodMk ((amax_meas A h).comp (scorevec_meas m r α q)))
  · simp only [offer, dif_neg h]
    exact measurable_const

lemma avail_meas (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (present : Finset (Fin n)) :
    ∀ s, Measurable (fun W => availBefore m r α p (sel0 : Selector n T) present W s) := by
  intro s
  induction s with
  | zero => simp only [availBefore]; exact measurable_const
  | succ s ih =>
    by_cases hs : s < T
    · simp only [availBefore, dif_pos hs]
      have hstep : Measurable (fun x : (Fin n → ℝ) × Finset (Fin n) =>
          match offer m r α (sel0 : Selector n T) ⟨s, hs⟩ (p ⟨s, hs⟩) x.1 x.2 with
          | some i => x.2.erase i
          | none => x.2) := by
        apply measurable_from_prod_countable_left
        intro A
        exact offer_meas m r α ⟨s, hs⟩ (p ⟨s, hs⟩) A (fun o => match o with
          | some i => A.erase i
          | none => A)
      exact hstep.comp (measurable_id.prodMk ih)
    · simp only [availBefore, dif_neg hs]
      exact ih

lemma rev2_meas (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (present : Finset (Fin n)) :
    Measurable (fun W => rev2 m r α p (sel0 : Selector n T) present W) := by
  unfold rev2
  apply Finset.measurable_sum
  intro t _
  have hstep : Measurable (fun x : (Fin n → ℝ) × Finset (Fin n) =>
      match offer m r α (sel0 : Selector n T) t (p t) x.1 x.2 with
      | some i => MultiPriceOnline.Balance.pr (r i) (jt m (p t) i)
      | none => 0) := by
    apply measurable_from_prod_countable_left
    intro A
    exact offer_meas m r α t (p t) A (fun o => match o with
      | some i => MultiPriceOnline.Balance.pr (r i) (jt m (p t) i)
      | none => 0)
  exact hstep.comp (measurable_id.prodMk (avail_meas m r α p present t.val))

/-! ### Agreement of argmax selectors when there are no ties -/

/-- No ties at all among distinct items. -/
def Good (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ) (W : Fin n → ℝ) :
    Prop :=
  ∀ t (i i' : Fin n), i ≠ i' → score m r α (p t) W i ≠ score m r α (p t) W i'

lemma offer_congr (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (sel sel' : Selector n T) (hs : IsArgmaxSelector sel) (hs' : IsArgmaxSelector sel')
    (W : Fin n → ℝ) (hG : Good m r α p W) (t : Fin T) (A : Finset (Fin n)) :
    offer m r α sel t (p t) W A = offer m r α sel' t (p t) W A := by
  unfold offer
  by_cases h : A.Nonempty
  · simp only [dif_pos h]
    set s := score m r α (p t) W
    obtain ⟨ha, hamax⟩ := hs t A h s
    obtain ⟨hb, hbmax⟩ := hs' t A h s
    have heq : s (sel t A h s) = s (sel' t A h s) :=
      le_antisymm (hbmax _ ha) (hamax _ hb)
    have hab : sel t A h s = sel' t A h s := by
      by_contra hne
      exact hG t _ _ hne heq
    rw [hab]
  · simp only [dif_neg h]

lemma avail_congr (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (sel sel' : Selector n T) (hs : IsArgmaxSelector sel) (hs' : IsArgmaxSelector sel')
    (present : Finset (Fin n)) (W : Fin n → ℝ) (hG : Good m r α p W) :
    ∀ s, availBefore m r α p sel present W s = availBefore m r α p sel' present W s := by
  intro s
  induction s with
  | zero => simp only [availBefore]
  | succ s ih =>
    by_cases hT : s < T
    · simp only [availBefore, dif_pos hT]
      rw [ih, offer_congr m r α p sel sel' hs hs' W hG ⟨s, hT⟩]
    · simp only [availBefore, dif_neg hT]
      exact ih

lemma rev2_congr (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (sel sel' : Selector n T) (hs : IsArgmaxSelector sel) (hs' : IsArgmaxSelector sel')
    (present : Finset (Fin n)) (W : Fin n → ℝ) (hG : Good m r α p W) :
    rev2 m r α p sel present W = rev2 m r α p sel' present W := by
  unfold rev2 run2
  apply Finset.sum_congr rfl
  intro t _
  rw [avail_congr m r α p sel sel' hs hs' present W hG,
    offer_congr m r α p sel sel' hs hs' W hG]

/-- Almost every seed vector has no ties. -/
lemma ae_good (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (hr : ∀ i, MultiPriceOnline.Ranking.IsPriceSet (m i) (r i))
    (hα : ∀ i, MultiPriceOnline.Balance.IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) :
    ∀ᵐ W ∂(seedMeasure n), Good m r α p W := by
  unfold Good
  rw [ae_all_iff]; intro t
  rw [ae_all_iff]; intro i
  rw [ae_all_iff]; intro i'
  by_cases hii : i = i'
  · exact Filter.Eventually.of_forall fun _ h => absurd hii h
  · rw [ae_iff]
    set ci := MultiPriceOnline.Balance.pr (r i) (jt m (p t) i)
    set ci' := MultiPriceOnline.Balance.pr (r i') (jt m (p t) i')
    have hset : {W : Fin n → ℝ | ¬(i ≠ i' → score m r α (p t) W i ≠ score m r α (p t) W i')} =
        {W | Phi (m i) (r i) (α i) (W i) =
          (fun y => Phi (m i') (r i') (α i') y + (ci - ci')) (W i')} := by
      ext W
      simp only [Set.mem_ofPred_eq, score, ne_eq, Classical.not_imp, not_not]
      constructor
      · rintro ⟨-, h⟩; linarith
      · intro h; exact ⟨hii, by linarith⟩
    rw [hset]
    unfold seedMeasure
    apply null_pair _ hii (Phi_meas _ _ _) ((Phi_meas _ _ _).add measurable_const)
    intro c
    exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans
      (le_of_eq (Phi_level_null (hr i) (hα i) c)))

lemma ae_Icc (n : ℕ) : ∀ᵐ W ∂(seedMeasure n), ∀ i, W i ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro i
  unfold seedMeasure
  exact (Measure.tendsto_eval_ae_ae (i := i)).eventually (ae_restrict_mem measurableSet_Icc)

instance seed_finite (n : ℕ) : IsFiniteMeasure (seedMeasure n) := by
  unfold seedMeasure; infer_instance

lemma rev2_integrable (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (hr : ∀ i, MultiPriceOnline.Ranking.IsPriceSet (m i) (r i))
    (hα : ∀ i, MultiPriceOnline.Balance.IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) (sel : Selector n T) (hsel : IsArgmaxSelector sel) :
    Integrable (fun W => rev2 m r α p sel Finset.univ W) (seedMeasure n) := by
  have hae : (fun W => rev2 m r α p (sel0 : Selector n T) Finset.univ W) =ᵐ[seedMeasure n]
      (fun W => rev2 m r α p sel Finset.univ W) := by
    filter_upwards [ae_good m r α hr hα p] with W hW
    exact rev2_congr m r α p sel0 sel sel0_argmax hsel _ W hW
  refine Integrable.of_bound
    (((rev2_meas m r α p Finset.univ).aestronglyMeasurable).congr hae)
    (∑ t : Fin T, ∑ i : Fin n, |MultiPriceOnline.Balance.pr (r i) (jt m (p t) i)|)
    (Filter.Eventually.of_forall fun W => ?_)
  unfold rev2
  rw [Real.norm_eq_abs]
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
  rcases run2 m r α p sel Finset.univ W t with _ | i
  · simp only [abs_zero]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  · exact Finset.single_le_sum (f := fun i => |MultiPriceOnline.Balance.pr (r i) (jt m (p t) i)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-! ### Structure of a run -/

lemma offer_some {m : Fin n → ℕ} {r α : Fin n → ℕ → ℝ} {sel : Selector n T}
    (hsel : IsArgmaxSelector sel) {t : Fin T} {q : Fin n → ℕ → ℝ} {W : Fin n → ℝ}
    {A : Finset (Fin n)} {i : Fin n} (h : offer m r α sel t q W A = some i) :
    i ∈ A ∧ 0 < score m r α q W i := by
  unfold offer at h
  split_ifs at h with h1 h2
  have h' := Option.some.inj h
  subst h'
  exact ⟨(hsel t A h1 _).1, h2⟩

lemma avail_succ_sub (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (sel : Selector n T) (present : Finset (Fin n)) (W : Fin n → ℝ) (s : ℕ) :
    availBefore m r α p sel present W (s + 1) ⊆ availBefore m r α p sel present W s := by
  simp only [availBefore]
  split_ifs with hs
  · split
    · exact Finset.erase_subset _ _
    · exact subset_refl _
  · exact subset_refl _

lemma avail_anti (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (sel : Selector n T) (present : Finset (Fin n)) (W : Fin n → ℝ) (s : ℕ) :
    ∀ k, availBefore m r α p sel present W (s + k) ⊆ availBefore m r α p sel present W s := by
  intro k
  induction k with
  | zero => exact subset_refl _
  | succ k ih => exact (avail_succ_sub m r α p sel present W (s + k)).trans ih

lemma run2_not_mem_succ {m : Fin n → ℕ} {r α : Fin n → ℕ → ℝ} {p : Fin T → Fin n → ℕ → ℝ}
    {sel : Selector n T} {present : Finset (Fin n)} {W : Fin n → ℝ} {s : Fin T} {i : Fin n}
    (h : run2 m r α p sel present W s = some i) :
    i ∉ availBefore m r α p sel present W (s.val + 1) := by
  unfold run2 at h
  simp only [availBefore, dif_pos s.isLt, Fin.eta, h]
  exact Finset.notMem_erase _ _

lemma run2_unique {m : Fin n → ℕ} {r α : Fin n → ℕ → ℝ} {p : Fin T → Fin n → ℕ → ℝ}
    {sel : Selector n T} (hsel : IsArgmaxSelector sel) {present : Finset (Fin n)}
    {W : Fin n → ℝ} {s t : Fin T} {i : Fin n}
    (hs : run2 m r α p sel present W s = some i) (ht : run2 m r α p sel present W t = some i) :
    s = t := by
  have key : ∀ s t : Fin T, s < t → run2 m r α p sel present W s = some i →
      run2 m r α p sel present W t = some i → False := by
    intro s t hlt hs ht
    have hmem := (offer_some hsel ht).1
    have hsub := avail_anti m r α p sel present W (s.val + 1) (t.val - (s.val + 1))
    have heq : s.val + 1 + (t.val - (s.val + 1)) = t.val := by
      have : s.val < t.val := hlt
      omega
    rw [heq] at hsub
    exact run2_not_mem_succ hs (hsub hmem)
  rcases lt_trichotomy s t with h | h | h
  · exact (key s t h hs ht).elim
  · exact h
  · exact (key t s h ht hs).elim

lemma sumY_eq (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (sel : Selector n T) (hsel : IsArgmaxSelector sel) (W : Fin n → ℝ) :
    ∑ i, Yi m r α p sel Finset.univ W i =
      ∑ t, (match run2 m r α p sel Finset.univ W t with
        | some i => Yi m r α p sel Finset.univ W i
        | none => 0) := by
  have h1 : ∀ t, (match run2 m r α p sel Finset.univ W t with
        | some i => Yi m r α p sel Finset.univ W i
        | none => 0) = ∑ i, if run2 m r α p sel Finset.univ W t = some i then
          Yi m r α p sel Finset.univ W i else 0 := by
    intro t
    rcases run2 m r α p sel Finset.univ W t with _ | i0
    · simp
    · simp
  rw [Finset.sum_congr rfl fun t _ => h1 t, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hex : ∃ t, run2 m r α p sel Finset.univ W t = some i
  · obtain ⟨t0, ht0⟩ := hex
    rw [Finset.sum_eq_single t0]
    · simp [ht0]
    · intro b _ hb
      rw [if_neg]
      intro hb'
      exact hb (run2_unique hsel hb' ht0)
    · intro h; exact absurd (Finset.mem_univ _) h
  · push Not at hex
    simp [hex, Yi]

lemma Yi_nonneg (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (hr : ∀ i, MultiPriceOnline.Ranking.IsPriceSet (m i) (r i))
    (hα : ∀ i, MultiPriceOnline.Balance.IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) (sel : Selector n T) (W : Fin n → ℝ) (i : Fin n) :
    0 ≤ Yi m r α p sel Finset.univ W i := by
  unfold Yi
  split_ifs
  · exact PhiDeriv_nonneg (hr i) (hα i) _
  · exact le_rfl

lemma Zt_nonneg (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (p : Fin T → Fin n → ℕ → ℝ) (sel : Selector n T) (hsel : IsArgmaxSelector sel)
    (W : Fin n → ℝ) (t : Fin T) :
    0 ≤ Zt m r α p sel Finset.univ W t := by
  unfold Zt
  rcases h : run2 m r α p sel Finset.univ W t with _ | i
  · exact le_rfl
  · unfold run2 at h
    exact (offer_some hsel h).2.le


/-! ### Lemma 3: further measurability and integrability -/

lemma fa_integrable {m : ℕ} {r α : ℕ → ℝ} (hr : MultiPriceOnline.Ranking.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) (a : ℝ) :
    Integrable (fun x => if Phi m r α x < a then PhiDeriv m r α x else 0)
      ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)) := by
  have hfmeas : Measurable (fun x => if Phi m r α x < a then PhiDeriv m r α x else 0) :=
    Measurable.ite (measurableSet_lt (Phi_meas m r α) measurable_const) (PhiDeriv_meas m r α)
      measurable_const
  refine Measure.integrableOn_of_bounded (M := DB m r α) (by simp) hfmeas.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall fun x hx => ?_
  have h0 := PhiDeriv_nonneg hr hα x
  have h1 := PhiDeriv_le hr hα hx
  split_ifs
  · rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  · simp only [norm_zero]; linarith

lemma offer_meas' {γ : Type*} [MeasurableSpace γ] (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (t : Fin T) (q : Fin n → ℕ → ℝ) (A : Finset (Fin n))
    (φ : Option (Fin n) → (Fin n → ℝ) → γ) (hφ : ∀ o, Measurable (φ o)) :
    Measurable (fun W => φ (offer m r α (sel0 : Selector n T) t q W A) W) := by
  by_cases h : A.Nonempty
  · have hfun : (fun W => φ (offer m r α (sel0 : Selector n T) t q W A) W) =
        fun W => (fun x : (Fin n → ℝ) × Fin n =>
          if 0 < score m r α q x.1 x.2 then φ (some x.2) x.1 else φ none x.1)
          (W, amax A h (score m r α q W)) := by
      funext W
      simp only [offer, dif_pos h, sel0]
      by_cases hh : 0 < score m r α q W (amax A h (score m r α q W)) <;>
        simp only [hh, if_true, if_false]
    rw [hfun]
    have hg : Measurable (fun x : (Fin n → ℝ) × Fin n =>
          if 0 < score m r α q x.1 x.2 then φ (some x.2) x.1 else φ none x.1) := by
      apply measurable_from_prod_countable_left
      intro i
      dsimp only
      exact Measurable.ite (measurableSet_lt measurable_const (score_meas m r α q i))
        (hφ _) (hφ _)
    exact hg.comp (measurable_id.prodMk ((amax_meas A h).comp (scorevec_meas m r α q)))
  · simp only [offer, dif_neg h]
    exact hφ none

lemma Zt_meas (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (present : Finset (Fin n)) (t : Fin T) :
    Measurable (fun W => Zt m r α p (sel0 : Selector n T) present W t) := by
  unfold Zt run2
  have hstep : Measurable (fun x : (Fin n → ℝ) × Finset (Fin n) =>
      match offer m r α (sel0 : Selector n T) t (p t) x.1 x.2 with
      | some j => score m r α (p t) x.1 j
      | none => 0) := by
    apply measurable_from_prod_countable_left
    intro A
    exact offer_meas' m r α t (p t) A (fun o W => match o with
      | some j => score m r α (p t) W j
      | none => 0) (fun o => by
        rcases o with _ | j
        · exact measurable_const
        · exact score_meas m r α (p t) j)
  exact hstep.comp (measurable_id.prodMk (avail_meas m r α p present t.val))

lemma Yi_meas (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (present : Finset (Fin n)) (i : Fin n) :
    Measurable (fun W => Yi m r α p (sel0 : Selector n T) present W i) := by
  unfold Yi
  have hset : MeasurableSet {W : Fin n → ℝ |
      ∃ t, run2 m r α p (sel0 : Selector n T) present W t = some i} := by
    apply measurableSet_setOfPred.2
    apply Measurable.exists
    intro t
    unfold run2
    have hstep : Measurable (fun x : (Fin n → ℝ) × Finset (Fin n) =>
        offer m r α (sel0 : Selector n T) t (p t) x.1 x.2 = some i) := by
      apply measurable_from_prod_countable_left
      intro A
      exact offer_meas' m r α t (p t) A (fun o _ => o = some i) (fun _ => measurable_const)
    exact hstep.comp (measurable_id.prodMk (avail_meas m r α p present t.val))
  exact Measurable.ite hset ((PhiDeriv_meas _ _ _).comp (measurable_pi_apply i)) measurable_const

lemma run2_congr (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (sel sel' : Selector n T) (hs : IsArgmaxSelector sel) (hs' : IsArgmaxSelector sel')
    (present : Finset (Fin n)) (W : Fin n → ℝ) (hG : Good m r α p W) (t : Fin T) :
    run2 m r α p sel present W t = run2 m r α p sel' present W t := by
  unfold run2
  rw [avail_congr m r α p sel sel' hs hs' present W hG, offer_congr m r α p sel sel' hs hs' W hG]

lemma Zt_congr (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (sel sel' : Selector n T) (hs : IsArgmaxSelector sel) (hs' : IsArgmaxSelector sel')
    (present : Finset (Fin n)) (W : Fin n → ℝ) (hG : Good m r α p W) (t : Fin T) :
    Zt m r α p sel present W t = Zt m r α p sel' present W t := by
  unfold Zt
  rw [run2_congr m r α p sel sel' hs hs' present W hG]

lemma Yi_congr (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (sel sel' : Selector n T) (hs : IsArgmaxSelector sel) (hs' : IsArgmaxSelector sel')
    (present : Finset (Fin n)) (W : Fin n → ℝ) (hG : Good m r α p W) (i : Fin n) :
    Yi m r α p sel present W i = Yi m r α p sel' present W i := by
  unfold Yi
  simp only [run2_congr m r α p sel sel' hs hs' present W hG]

lemma Zt_nonneg' (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (p : Fin T → Fin n → ℕ → ℝ) (sel : Selector n T) (hsel : IsArgmaxSelector sel)
    (present : Finset (Fin n)) (W : Fin n → ℝ) (t : Fin T) :
    0 ≤ Zt m r α p sel present W t := by
  unfold Zt
  rcases h : run2 m r α p sel present W t with _ | i
  · exact le_rfl
  · unfold run2 at h
    exact (offer_some hsel h).2.le

/-- A bound for `Z_t` on `[0, 1]ⁿ`. -/
noncomputable def ZB (m : Fin n → ℕ) (r : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (t : Fin T) : ℝ :=
  ∑ j : Fin n, |MultiPriceOnline.Balance.pr (r j) (jt m (p t) j)|

lemma Zt_le (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (hr : ∀ i, MultiPriceOnline.Ranking.IsPriceSet (m i) (r i))
    (hα : ∀ i, MultiPriceOnline.Balance.IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) (sel : Selector n T)
    (present : Finset (Fin n)) (W : Fin n → ℝ) (hW : ∀ i, W i ∈ Set.Icc (0 : ℝ) 1) (t : Fin T) :
    Zt m r α p sel present W t ≤ ZB m r p t := by
  unfold Zt
  have hZB0 : 0 ≤ ZB m r p t := Finset.sum_nonneg fun _ _ => abs_nonneg _
  rcases h : run2 m r α p sel present W t with _ | j
  · exact hZB0
  · unfold score
    have h1 := Phi_nonneg (hr j) (hα j) (hW j).1
    have h2 : MultiPriceOnline.Balance.pr (r j) (jt m (p t) j) ≤ ZB m r p t :=
      (le_abs_self _).trans (Finset.single_le_sum
        (f := fun j => |MultiPriceOnline.Balance.pr (r j) (jt m (p t) j)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ j))
    linarith

lemma Zt_integrable (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (hr : ∀ i, MultiPriceOnline.Ranking.IsPriceSet (m i) (r i))
    (hα : ∀ i, MultiPriceOnline.Balance.IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) (sel : Selector n T) (hsel : IsArgmaxSelector sel)
    (present : Finset (Fin n)) (t : Fin T) :
    Integrable (fun W => Zt m r α p sel present W t) (seedMeasure n) := by
  have hae : (fun W => Zt m r α p (sel0 : Selector n T) present W t) =ᵐ[seedMeasure n]
      (fun W => Zt m r α p sel present W t) := by
    filter_upwards [ae_good m r α hr hα p] with W hW
    exact Zt_congr m r α p sel0 sel sel0_argmax hsel present W hW t
  refine Integrable.of_bound (((Zt_meas m r α p present t).aestronglyMeasurable).congr hae)
    (ZB m r p t) ?_
  filter_upwards [ae_Icc n] with W hW
  rw [Real.norm_eq_abs, abs_of_nonneg (Zt_nonneg' m r α p sel hsel present W t)]
  exact Zt_le m r α hr hα p sel present W hW t

lemma Yi_integrable (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (hr : ∀ i, MultiPriceOnline.Ranking.IsPriceSet (m i) (r i))
    (hα : ∀ i, MultiPriceOnline.Balance.IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) (sel : Selector n T) (hsel : IsArgmaxSelector sel)
    (present : Finset (Fin n)) (i : Fin n) :
    Integrable (fun W => Yi m r α p sel present W i) (seedMeasure n) := by
  have hae : (fun W => Yi m r α p (sel0 : Selector n T) present W i) =ᵐ[seedMeasure n]
      (fun W => Yi m r α p sel present W i) := by
    filter_upwards [ae_good m r α hr hα p] with W hW
    exact Yi_congr m r α p sel0 sel sel0_argmax hsel present W hW i
  refine Integrable.of_bound (((Yi_meas m r α p present i).aestronglyMeasurable).congr hae)
    (DB (m i) (r i) (α i)) ?_
  filter_upwards [ae_Icc n] with W hW
  have h0 := PhiDeriv_nonneg (hr i) (hα i) (W i)
  have h1 := PhiDeriv_le (hr i) (hα i) (hW i)
  unfold Yi
  split_ifs
  · rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  · simp only [norm_zero]; linarith

/-! ### `Z^crit` does not depend on `W_i` -/

lemma amax_congr (C : Finset (Fin n)) (hC : C.Nonempty) (s s' : Fin n → ℝ)
    (h : ∀ j ∈ C, s j = s' j) : amax C hC s = amax C hC s' := by
  have hf : C.filter (fun i => ∀ j ∈ C, s j ≤ s i) = C.filter (fun i => ∀ j ∈ C, s' j ≤ s' i) := by
    apply Finset.filter_congr
    intro x hx
    constructor
    · intro hh j hj; rw [← h j hj, ← h x hx]; exact hh j hj
    · intro hh j hj; rw [h j hj, h x hx]; exact hh j hj
  unfold amax
  congr 1

lemma avail_sub_present (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (sel : Selector n T) (present : Finset (Fin n)) (W : Fin n → ℝ) (s : ℕ) :
    availBefore m r α p sel present W s ⊆ present := by
  have := avail_anti m r α p sel present W 0 s
  rw [Nat.zero_add] at this
  simpa [availBefore] using this

lemma offer_indep (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (t : Fin T) (q : Fin n → ℕ → ℝ)
    (i : Fin n) (W W' : Fin n → ℝ) (hWW : ∀ j, j ≠ i → W j = W' j)
    (A : Finset (Fin n)) (hA : i ∉ A) :
    offer m r α (sel0 : Selector n T) t q W A = offer m r α (sel0 : Selector n T) t q W' A := by
  have hs : ∀ j ∈ A, score m r α q W j = score m r α q W' j := by
    intro j hj
    have hji : j ≠ i := fun h => hA (h ▸ hj)
    simp only [score, hWW j hji]
  unfold offer
  by_cases h : A.Nonempty
  · simp only [dif_pos h, sel0]
    have e1 := amax_congr A h _ _ hs
    have e2 := hs _ (amax_spec A h (score m r α q W')).1
    simp only [e1, e2]
    by_cases hh : 0 < score m r α q W' (amax A h (score m r α q W')) <;> simp [hh]
  · simp only [dif_neg h]

lemma avail_indep (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (i : Fin n) (W W' : Fin n → ℝ) (hWW : ∀ j, j ≠ i → W j = W' j) :
    ∀ s, availBefore m r α p (sel0 : Selector n T) (Finset.univ.erase i) W s =
      availBefore m r α p (sel0 : Selector n T) (Finset.univ.erase i) W' s := by
  intro s
  induction s with
  | zero => simp only [availBefore]
  | succ s ih =>
    by_cases hT : s < T
    · simp only [availBefore, dif_pos hT]
      have hA : i ∉ availBefore m r α p (sel0 : Selector n T) (Finset.univ.erase i) W' s :=
        fun h => Finset.notMem_erase i _ (avail_sub_present m r α p _ _ W' s h)
      rw [ih, offer_indep m r α ⟨s, hT⟩ (p ⟨s, hT⟩) i W W' hWW _ hA]
    · simp only [availBefore, dif_neg hT]
      exact ih

lemma Zcrit_indep (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (i : Fin n) (W W' : Fin n → ℝ) (hWW : ∀ j, j ≠ i → W j = W' j) (t : Fin T) :
    Zt m r α p (sel0 : Selector n T) (Finset.univ.erase i) W t =
      Zt m r α p (sel0 : Selector n T) (Finset.univ.erase i) W' t := by
  have hA : i ∉ availBefore m r α p (sel0 : Selector n T) (Finset.univ.erase i) W' t.val :=
    fun h => Finset.notMem_erase i _ (avail_sub_present m r α p _ _ W' t.val h)
  have hrun : run2 m r α p (sel0 : Selector n T) (Finset.univ.erase i) W t =
      run2 m r α p (sel0 : Selector n T) (Finset.univ.erase i) W' t := by
    unfold run2
    rw [avail_indep m r α p i W W' hWW, offer_indep m r α t (p t) i W W' hWW _ hA]
  unfold Zt
  rw [hrun]
  rcases h : run2 m r α p (sel0 : Selector n T) (Finset.univ.erase i) W' t with _ | j
  · rfl
  · have hj := (offer_some (sel0_argmax (T := T)) (show offer m r α (sel0 : Selector n T) t (p t) W'
      (availBefore m r α p sel0 (Finset.univ.erase i) W' t.val) = some j from h)).1
    have hji : j ≠ i := fun e => hA (e ▸ hj)
    simp only [score, hWW j hji]

lemma jt_le_m (m : Fin n → ℕ) (q : Fin n → ℕ → ℝ) (i : Fin n) : jt m q i ≤ m i := by
  unfold jt
  apply Finset.sup_le
  intro j hj
  rw [mem_Icc] at hj
  split_ifs
  · exact hj.2
  · exact Nat.zero_le _

/-! ### The key estimate `E[Y_i + Z_t] ≥ r_i^{(j_{t,i})}` -/

lemma key (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (hr : ∀ i, MultiPriceOnline.Ranking.IsPriceSet (m i) (r i))
    (hα : ∀ i, MultiPriceOnline.Balance.IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) (hp : IsDeterministic m p)
    (sel : Selector n T) (hsel : IsArgmaxSelector sel) (t : Fin T) (i : Fin n)
    (hJ : 1 ≤ jt m (p t) i) :
    MultiPriceOnline.Balance.pr (r i) (jt m (p t) i) ≤
      ∫ W, Yi m r α p sel Finset.univ W i ∂(seedMeasure n) +
        ∫ W, Zt m r α p sel Finset.univ W t ∂(seedMeasure n) := by
  set c := MultiPriceOnline.Balance.pr (r i) (jt m (p t) i) with hc
  set Zc : (Fin n → ℝ) → ℝ := fun W => Zt m r α p (sel0 : Selector n T) (Finset.univ.erase i) W t
    with hZc
  set f : ℝ → ℝ → ℝ := fun a x =>
    if Phi (m i) (r i) (α i) x < a then PhiDeriv (m i) (r i) (α i) x else 0 with hf
  set hlow : (Fin n → ℝ) → ℝ := fun W => f (c - Zc W) (W i) + Zc W with hhlow
  have hZcm : Measurable Zc := Zt_meas m r α p _ t
  have hlow_meas : Measurable hlow := by
    have h1 : Measurable (fun W : Fin n → ℝ => f (c - Zc W) (W i)) := by
      simp only [hf]
      exact Measurable.ite (measurableSet_lt ((Phi_meas _ _ _).comp (measurable_pi_apply i))
        (measurable_const.sub hZcm)) ((PhiDeriv_meas _ _ _).comp (measurable_pi_apply i))
        measurable_const
    exact h1.add hZcm
  have hfb : ∀ a x, x ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ f a x ∧ f a x ≤ DB (m i) (r i) (α i) := by
    intro a x hx
    have h0 := PhiDeriv_nonneg (hr i) (hα i) x
    have h1 := PhiDeriv_le (hr i) (hα i) hx
    simp only [hf]
    split_ifs
    · exact ⟨h0, h1⟩
    · exact ⟨le_rfl, by linarith⟩
  have hZc0 : ∀ W, 0 ≤ Zc W := fun W => Zt_nonneg' m r α p _ sel0_argmax _ W t
  have hlow_int : Integrable hlow (seedMeasure n) := by
    refine Integrable.of_bound hlow_meas.aestronglyMeasurable
      (DB (m i) (r i) (α i) + ZB m r p t) ?_
    filter_upwards [ae_Icc n] with W hW
    have h1 := hfb (c - Zc W) (W i) (hW i)
    have h2 := Zt_le m r α hr hα p (sel0 : Selector n T) (Finset.univ.erase i) W hW t
    have h3 := hZc0 W
    rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [hhlow]; linarith)]
    simp only [hhlow]
    linarith
  -- pointwise lower bound
  have hle : hlow ≤ᵐ[seedMeasure n]
      (fun W => Yi m r α p sel Finset.univ W i + Zt m r α p sel Finset.univ W t) := by
    filter_upwards [ae_good m r α hr hα p, ae_Icc n] with W hG hW
    have hNT : NoTies m r α p W := fun t i i' h _ => hG t i i' h
    have hZe : Zc W = Zt m r α p sel (Finset.univ.erase i) W t :=
      Zt_congr m r α p sel0 sel sel0_argmax hsel _ W hG t
    have hmono := MultiPriceOnline.Ranking.monotonicity_claim m r α hr hα p hp sel hsel W hW hNT t i
    have hY0 := Yi_nonneg m r α hr hα p sel W i
    simp only [hhlow, hf]
    split_ifs with hlt
    · rw [hZe] at hlt
      obtain ⟨s, -, hs⟩ := MultiPriceOnline.Ranking.dominance_claim m r α hr hα p hp sel hsel W hW
        hNT t i hJ hlt
      have hY : Yi m r α p sel Finset.univ W i = PhiDeriv (m i) (r i) (α i) (W i) := by
        unfold Yi; exact if_pos ⟨s, hs⟩
      rw [hY]; linarith
    · linarith
  -- Fubini
  have hc_le : c ≤ ∫ W, hlow W ∂(seedMeasure n) := by
    cases n with
    | zero => exact i.elim0
    | succ k =>
      set μ0 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1) with hμ0
      haveI : IsProbabilityMeasure μ0 := ⟨by simp [hμ0]⟩
      set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) i with he
      have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ0) i
      have hmps := MeasurePreserving.symm e hmp
      have hS : seedMeasure (k + 1) = Measure.pi (fun _ : Fin (k + 1) => μ0) := rfl
      rw [hS] at hlow_int ⊢
      have h1 : ∫ W, hlow W ∂(Measure.pi fun _ : Fin (k + 1) => μ0) =
          ∫ z, hlow (e.symm z) ∂(μ0.prod (Measure.pi fun _ : Fin k => μ0)) :=
        (hmps.integral_comp e.symm.measurableEmbedding hlow).symm
      have hint2 : Integrable (fun z => hlow (e.symm z)) (μ0.prod (Measure.pi fun _ : Fin k => μ0)) :=
        (hmps.integrable_comp_emb e.symm.measurableEmbedding).2 hlow_int
      rw [h1, integral_prod_symm _ hint2]
      have hinner : ∀ y : Fin k → ℝ, c ≤ ∫ x, hlow (e.symm (x, y)) ∂μ0 := by
        intro y
        set z := Zc (Fin.insertNth i 0 y) with hz
        have hsymm : ∀ x, e.symm (x, y) = Fin.insertNth i x y := by
          intro x
          simp [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
        have hZx : ∀ x, Zc (Fin.insertNth i x y) = z := by
          intro x
          apply Zcrit_indep
          intro j hj
          obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
          simp [Fin.insertNth_apply_succAbove]
        have hfun : (fun x => hlow (e.symm (x, y))) = fun x => f (c - z) x + z := by
          funext x
          simp only [hhlow, hsymm, hZx, Fin.insertNth_apply_same]
        rw [hfun, integral_add (fa_integrable (hr i) (hα i) (c - z)) (integrable_const z)]
        simp only [integral_const, probReal_univ, one_smul]
        have hz0 : 0 ≤ z := hZc0 _
        by_cases hpos : 0 < c - z
        · have := oneD (hr i) (hα i) (jt_le_m m (p t) i) hpos (by linarith)
          have hfe : ∫ x, f (c - z) x ∂μ0 = ∫ x in Set.Icc (0 : ℝ) 1,
              (if Phi (m i) (r i) (α i) x < c - z then PhiDeriv (m i) (r i) (α i) x else 0) := rfl
          linarith
        · have : 0 ≤ ∫ x, f (c - z) x ∂μ0 := by
            apply integral_nonneg_of_ae
            rw [Filter.EventuallyLE, hμ0, ae_restrict_iff' measurableSet_Icc]
            exact Filter.Eventually.of_forall fun x hx => (hfb _ x hx).1
          linarith
      calc c = ∫ y, c ∂(Measure.pi fun _ : Fin k => μ0) := by simp
        _ ≤ _ := integral_mono (integrable_const c) hint2.integral_prod_right hinner
  calc c ≤ ∫ W, hlow W ∂(seedMeasure n) := hc_le
    _ ≤ ∫ W, (Yi m r α p sel Finset.univ W i + Zt m r α p sel Finset.univ W t) ∂(seedMeasure n) :=
        integral_mono_ae hlow_int ((Yi_integrable m r α hr hα p sel hsel _ i).add
          (Zt_integrable m r α hr hα p sel hsel _ t)) hle
    _ = _ := integral_add (Yi_integrable m r α hr hα p sel hsel _ i)
          (Zt_integrable m r α hr hα p sel hsel _ t)

end MPR3Aux

open MPR3Aux in
theorem solution {n T : ℕ} (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (hr : ∀ i, MultiPriceOnline.Ranking.IsPriceSet (m i) (r i))
    (hα : ∀ i, MultiPriceOnline.Balance.IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) (hp : IsDeterministic m p)
    (sel : Selector n T) (hsel : IsArgmaxSelector sel) :
    DualFeasible m r p
      (fun i => ∫ W, Yi m r α p sel Finset.univ W i ∂(seedMeasure n))
      (fun t => ∫ W, Zt m r α p sel Finset.univ W t ∂(seedMeasure n)) := by
  have hZ0 : ∀ t, 0 ≤ ∫ W, Zt m r α p sel Finset.univ W t ∂(seedMeasure n) := fun t =>
    integral_nonneg fun W => Zt_nonneg' m r α p sel hsel _ W t
  have hY0 : ∀ i, 0 ≤ ∫ W, Yi m r α p sel Finset.univ W i ∂(seedMeasure n) := fun i =>
    integral_nonneg fun W => Yi_nonneg m r α hr hα p sel W i
  refine ⟨?_, hY0, hZ0⟩
  intro t i j hj1 hjm
  rcases hp t i j hj1 hjm with h | h
  · rw [h]; simp only [zero_mul, zero_add]; exact hZ0 t
  · rw [h]
    simp only [one_mul]
    have hjJ : j ≤ jt m (p t) i := by
      have := Finset.le_sup (f := fun j => if p t i j = 1 then j else 0) (mem_Icc.2 ⟨hj1, hjm⟩)
      simp only [h, if_true] at this
      exact this
    have hJ : 1 ≤ jt m (p t) i := le_trans hj1 hjJ
    have hk := key m r α hr hα p hp sel hsel t i hJ
    have hmono := pr_mono (hr i) j (jt m (p t) i) hjJ (jt_le_m m (p t) i)
    have hrj : MultiPriceOnline.Balance.pr (r i) j = r i j := if_neg (by omega)
    linarith
