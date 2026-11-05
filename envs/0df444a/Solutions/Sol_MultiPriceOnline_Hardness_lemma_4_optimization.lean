-- Prove2me | solution 1 for MultiPriceOnline.Hardness.lemma_4_optimization
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T08:02:16.954655+00:00
-- url     : https://prove2.me/submissions/04c34bc9-88e5-4e73-8f73-6fe16fac1840

import Mathlib
import Definitions.Def_MultiPriceOnline_Hardness_PriceSet
import Definitions.Def_MultiPriceOnline_Hardness_Instance
import Theorems.Thm_MultiPriceOnline_Hardness_eq_35

open Finset MultiPriceOnline.Hardness


lemma harmH (r c Y : ℝ) (R : ℕ) (hr : 0 < r) (hc : 0 < c) (hcY : c / r ≤ Y)
    (hR1 : Y ≤ R + 1) (hR2 : (R : ℝ) ≤ Y + 1) :
    ∑ u ∈ Icc 1 R, max (r - c / u) 0 ≤ r * (Y - c / r) - c * Real.log (r * Y / c) + 3 * r := by
  set L := ⌊c / r⌋₊ with hL
  have hcr : 0 < c / r := div_pos hc hr
  have hY : 0 < Y := lt_of_lt_of_le hcr hcY
  have hLle : (L : ℝ) ≤ c / r := Nat.floor_le hcr.le
  have hLgt : c / r < L + 1 := Nat.lt_floor_add_one _
  -- terms with u ≤ L vanish
  have hzero : ∀ u : ℕ, 1 ≤ u → u ≤ L → max (r - c / u) 0 = 0 := by
    intro u hu1 huL
    apply max_eq_right
    have hu : (0 : ℝ) < u := by exact_mod_cast hu1
    have : (u : ℝ) ≤ c / r := le_trans (by exact_mod_cast huL) hLle
    rw [sub_nonpos, le_div_iff₀ hu]
    rw [le_div_iff₀ hr] at this
    linarith
  have hF0 : ∀ R' : ℕ, R' ≤ L → ∑ u ∈ Icc 1 R', max (r - c / u) 0 = 0 := by
    intro R' hR'
    apply Finset.sum_eq_zero
    intro u hu
    simp only [Finset.mem_Icc] at hu
    exact hzero u hu.1 (by omega)
  have hind : ∀ R' : ℕ, L ≤ R' → ∑ u ∈ Icc 1 R', max (r - c / u) 0 ≤
      r * ((R' : ℝ) - L) - c * (Real.log (R' + 1) - Real.log (L + 1)) := by
    intro R' hR'
    induction R', hR' using Nat.le_induction with
    | base => rw [hF0 L le_rfl]; simp
    | succ R' hLR ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hpos : (0 : ℝ) < (R' : ℝ) + 1 := by positivity
      have hgt : c / r < (R' : ℝ) + 1 := by
        have : (L : ℝ) ≤ R' := by exact_mod_cast hLR
        linarith
      have hterm : max (r - c / ((R' + 1 : ℕ) : ℝ)) 0 = r - c / ((R' : ℝ) + 1) := by
        push_cast
        apply max_eq_left
        rw [sub_nonneg, div_le_iff₀ hpos]
        rw [div_lt_iff₀ hr] at hgt
        linarith
      rw [hterm]
      have hlog : Real.log ((R' : ℝ) + 1 + 1) - Real.log ((R' : ℝ) + 1) ≤ 1 / ((R' : ℝ) + 1) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((R' : ℝ) + 1 + 1) / ((R' : ℝ) + 1) by positivity)
        have h2 : ((R' : ℝ) + 1 + 1) / ((R' : ℝ) + 1) - 1 = 1 / ((R' : ℝ) + 1) := by
          field_simp; ring
        linarith
      push_cast
      have : c / ((R' : ℝ) + 1) = c * (1 / ((R' : ℝ) + 1)) := by ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left hlog hc.le]
  have hxlog : Real.log (r * Y / c) ≤ r * Y / c - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hbase : 0 ≤ r * (Y - c / r) - c * Real.log (r * Y / c) := by
    have h1 : r * (Y - c / r) = c * (r * Y / c - 1) := by field_simp
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_left hxlog hc.le]
  rcases le_or_gt R L with hRL | hRL
  · rw [hF0 R hRL]; linarith
  · have h := hind R hRL.le
    have hlogR : Real.log Y ≤ Real.log ((R : ℝ) + 1) := Real.log_le_log hY hR1
    have hlogL : Real.log ((L : ℝ) + 1) ≤ Real.log (c / r + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have hsplit : Real.log (c / r + 1) = Real.log (c / r) + Real.log (1 + r / c) := by
      rw [← Real.log_mul hcr.ne' (by positivity)]
      congr 1; field_simp
    have hlog1 : Real.log (1 + r / c) ≤ r / c := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + r / c by positivity)
      linarith
    have hYc : Real.log (r * Y / c) = Real.log Y - Real.log (c / r) := by
      rw [← Real.log_div hY.ne' hcr.ne']
      congr 1; field_simp
    have hcrc : c * (r / c) = r := by field_simp
    have hRL' : ((R : ℝ) - L) ≤ Y - c / r + 2 := by linarith
    have : c * (Real.log ((R : ℝ) + 1) - Real.log ((L : ℝ) + 1)) ≥ c * Real.log (r * Y / c) - r := by
      rw [hYc]
      have : Real.log ((R : ℝ) + 1) - Real.log ((L : ℝ) + 1) ≥
          Real.log Y - Real.log (c / r) - r / c := by linarith
      nlinarith [mul_le_mul_of_nonneg_left this hc.le]
    nlinarith [mul_le_mul_of_nonneg_left hRL' hr.le]

theorem solution {m : ℕ} {r α B : ℕ → ℝ} (hm : 1 ≤ m) (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) (hB : IsPhaseB m r α B) (k : ℕ) (hk : 1 ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ q : ℕ → ℝ, (∀ t < n, 0 ≤ q t) → (∑ t ∈ range n, q t) ≤ k →
      (∀ t < n, ((n : ℝ) - t) * q t ≤ k) →
      ∑ t ∈ range n, r (phaseOf n m B t) * ((n : ℝ) - t) * q t
        ≤ sSup {v : ℝ | ∃ lam : ℕ → ℝ, (∀ j ∈ Icc 1 m, 0 ≤ lam j) ∧
                (∀ j ∈ Icc 1 (m - 1), lam j ≤ Real.log (B j / B (j + 1))) ∧
                (∑ j ∈ Icc 1 m, lam j) ≤ 1 ∧
                v = ∑ j ∈ Icc 1 m, r j * B j * n * (1 - Real.exp (-lam j)) * k}
            + ε * n * k := by
  -- prices
  have hrmono : ∀ d j : ℕ, 1 ≤ j → j + d ≤ m → r j ≤ r (j + d) := by
    intro d
    induction d with
    | zero => intro j _ _; simp
    | succ d ih =>
      intro j hj hjd
      have h1 := ih j hj (by omega)
      have h2 := hr.2 (j + d) (by omega) (by omega)
      rw [show j + (d + 1) = j + d + 1 by omega]; linarith
  have hrpos : ∀ j, 1 ≤ j → j ≤ m → 0 < r j := by
    intro j hj hjm
    have h1 := hrmono (j - 1) 1 le_rfl (by omega)
    rw [show 1 + (j - 1) = j by omega] at h1
    exact lt_of_lt_of_le hr.1 h1
  set θ := r 1 * Real.exp (-α 1) with hθdef
  have hθ : 0 < θ := mul_pos hr.1 (Real.exp_pos _)
  have hBj : ∀ j, 1 ≤ j → j ≤ m → B j * r j * Real.exp (-α j) = θ := by
    intro j hj hjm
    rcases eq_or_lt_of_le hj with h | h
    · subst h; rw [hB.1]; ring
    · exact hB.2 j h hjm
  have hBpos : ∀ j, 1 ≤ j → j ≤ m → 0 < B j := by
    intro j hj hjm
    have h := hBj j hj hjm
    have hP : 0 < r j * Real.exp (-α j) := mul_pos (hrpos j hj hjm) (Real.exp_pos _)
    by_contra hc; push_neg at hc
    have : B j * (r j * Real.exp (-α j)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hP.le
    rw [← mul_assoc] at this
    linarith
  have h35 := eq_35 hr hα
  have hBstep : ∀ j, 1 ≤ j → j < m → B (j + 1) * Real.exp (α j) ≤ B j := by
    intro j hj hjm
    have h1 := hBj j hj hjm.le
    have h2 := hBj (j + 1) (by omega) hjm
    have h3 := h35 (j + 1) (by omega) hjm
    simp only [Nat.add_sub_cancel] at h3
    rw [div_le_iff₀ (hrpos (j + 1) (by omega) hjm)] at h3
    have hb1 := hBpos (j + 1) (by omega) hjm
    have h4 : B (j + 1) * r j ≤ θ := by
      rw [← h2]
      have := mul_le_mul_of_nonneg_left h3 hb1.le
      linarith
    have hP : 0 < r j * Real.exp (-α j) := mul_pos (hrpos j hj hjm.le) (Real.exp_pos _)
    have h5 : B (j + 1) * Real.exp (α j) * (r j * Real.exp (-α j)) = B (j + 1) * r j := by
      have : Real.exp (α j) * Real.exp (-α j) = 1 := by rw [← Real.exp_add]; simp
      calc _ = B (j + 1) * r j * (Real.exp (α j) * Real.exp (-α j)) := by ring
        _ = _ := by rw [this, mul_one]
    have h6 : B (j + 1) * Real.exp (α j) * (r j * Real.exp (-α j)) ≤ B j * (r j * Real.exp (-α j)) := by
      rw [h5, ← mul_assoc, h1]; exact h4
    exact le_of_mul_le_mul_right h6 hP
  have hBdec : ∀ j, 1 ≤ j → j < m → B (j + 1) ≤ B j := by
    intro j hj hjm
    have := hBstep j hj hjm
    have he : 1 ≤ Real.exp (α j) := Real.one_le_exp (hα.1 j hj hjm.le).le
    have hb1 := hBpos (j + 1) (by omega) hjm
    nlinarith
  have hBanti : ∀ d j, 1 ≤ j → j + d ≤ m → B (j + d) ≤ B j := by
    intro d
    induction d with
    | zero => intro j _ _; simp
    | succ d ih =>
      intro j hj hjd
      have h1 := ih j hj (by omega)
      have h2 := hBdec (j + d) (by omega) (by omega)
      rw [show j + (d + 1) = j + d + 1 by omega]; linarith
  have hBle1 : ∀ j, 1 ≤ j → j ≤ m → B j ≤ 1 := by
    intro j hj hjm
    have := hBanti (j - 1) 1 le_rfl (by omega)
    rw [show 1 + (j - 1) = j by omega, hB.1] at this
    exact this
  -- the value at λ = α is at most the supremum
  have hMS : ∀ n : ℕ, ∑ j ∈ Icc 1 m, r j * B j * n * (1 - Real.exp (-α j)) * k ≤
      sSup {v : ℝ | ∃ lam : ℕ → ℝ, (∀ j ∈ Icc 1 m, 0 ≤ lam j) ∧
                (∀ j ∈ Icc 1 (m - 1), lam j ≤ Real.log (B j / B (j + 1))) ∧
                (∑ j ∈ Icc 1 m, lam j) ≤ 1 ∧
                v = ∑ j ∈ Icc 1 m, r j * B j * n * (1 - Real.exp (-lam j)) * k} := by
    intro n
    apply le_csSup
    · refine ⟨∑ j ∈ Icc 1 m, r j * B j * n * k, ?_⟩
      rintro v ⟨lam, -, -, -, rfl⟩
      apply sum_le_sum
      intro j hj
      simp only [mem_Icc] at hj
      have h0 : 0 ≤ r j * B j * n * k := by
        have := hrpos j hj.1 hj.2; have := hBpos j hj.1 hj.2; positivity
      have h1 : 1 - Real.exp (-lam j) ≤ 1 := by linarith [Real.exp_pos (-lam j)]
      have : r j * B j * n * (1 - Real.exp (-lam j)) * k = (r j * B j * n * k) * (1 - Real.exp (-lam j)) := by ring
      rw [this]
      nlinarith
    · refine ⟨α, fun j hj => ?_, ?_, hα.2.1.le, rfl⟩
      · simp only [mem_Icc] at hj; exact (hα.1 j hj.1 hj.2).le
      · intro j hj
        simp only [mem_Icc] at hj
        have hb1 := hBpos (j + 1) (by omega) (by omega)
        rw [Real.le_log_iff_exp_le (div_pos (hBpos j hj.1 (by omega)) hb1), le_div_iff₀ hb1]
        have := hBstep j hj.1 (by omega)
        linarith
  -- choice of N₀
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge (3 * (∑ j ∈ Icc 1 m, r j) / ε)
  refine ⟨max N₁ 1, ?_⟩
  intro n hn q hq0 hqs hqt
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnN : 3 * (∑ j ∈ Icc 1 m, r j) ≤ ε * n := by
    have h1 : (N₁ : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left _ _) hn
    have h2 := le_trans hN₁ h1
    rw [div_le_iff₀ hε] at h2
    linarith
  -- phase facts
  have hph : ∀ g, 1 ≤ phaseOf n m B g ∧ phaseOf n m B g ≤ m := by
    intro g
    unfold phaseOf
    refine ⟨by omega, ?_⟩
    have := Finset.card_filter_le (Icc 2 m) (fun j => ⌊(1 - B j) * (n : ℝ)⌋₊ ≤ g)
    simp at this
    omega
  have hphlow : ∀ g j, phaseOf n m B g = j → ⌊(1 - B j) * n⌋₊ ≤ g := by
    intro g j hj
    have hjm := (hph g).2
    rw [hj] at hjm
    have hj1 := (hph g).1
    rw [hj] at hj1
    rcases eq_or_lt_of_le hj1 with h | h
    · subst h; rw [hB.1]; simp
    by_contra hlt; push_neg at hlt
    have hsub : (Icc 2 m).filter (fun j' => ⌊(1 - B j') * (n : ℝ)⌋₊ ≤ g) ⊆ Icc 2 (j - 1) := by
      intro j' hj'
      simp only [mem_filter, mem_Icc] at hj' ⊢
      refine ⟨hj'.1.1, ?_⟩
      by_contra hc; push_neg at hc
      have h1 : B j' ≤ B j := by
        have := hBanti (j' - j) j (by omega) (by omega)
        rwa [show j + (j' - j) = j' by omega] at this
      have h2 : ⌊(1 - B j) * (n : ℝ)⌋₊ ≤ ⌊(1 - B j') * (n : ℝ)⌋₊ :=
        Nat.floor_le_floor (mul_le_mul_of_nonneg_right (by linarith) hnR.le)
      omega
    have := card_le_card hsub
    simp only [Nat.card_Icc] at this
    unfold phaseOf at hj
    omega
  -- duality
  set f : ℕ → ℝ := fun t => max (r (phaseOf n m B t) - θ * n / ((n : ℝ) - t)) 0 with hf
  have hdual : ∑ t ∈ range n, r (phaseOf n m B t) * ((n : ℝ) - t) * q t ≤
      k * (θ * n + ∑ t ∈ range n, f t) := by
    have hterm : ∀ t ∈ range n, r (phaseOf n m B t) * ((n : ℝ) - t) * q t ≤
        θ * n * q t + k * f t := by
      intro t ht
      have htn : t < n := mem_range.1 ht
      have htn' : (t : ℝ) < n := by exact_mod_cast htn
      have hpos : 0 < (n : ℝ) - t := by linarith
      have e1 : r (phaseOf n m B t) * ((n : ℝ) - t) * q t - θ * n * q t =
          ((n : ℝ) - t) * q t * (r (phaseOf n m B t) - θ * n / ((n : ℝ) - t)) := by
        field_simp
      have e2 : ((n : ℝ) - t) * q t * (r (phaseOf n m B t) - θ * n / ((n : ℝ) - t)) ≤
          ((n : ℝ) - t) * q t * f t :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (mul_nonneg hpos.le (hq0 t htn))
      have e3 : ((n : ℝ) - t) * q t * f t ≤ k * f t :=
        mul_le_mul_of_nonneg_right (hqt t htn) (le_max_right _ _)
      linarith
    calc _ ≤ ∑ t ∈ range n, (θ * n * q t + k * f t) := sum_le_sum hterm
      _ = θ * n * ∑ t ∈ range n, q t + k * ∑ t ∈ range n, f t := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      _ ≤ θ * n * k + k * ∑ t ∈ range n, f t := by
        have : 0 ≤ θ * n := by positivity
        nlinarith
      _ = _ := by ring
  -- per-phase bound
  have hphase : ∀ j ∈ Icc 1 m, ∑ t ∈ (range n).filter (fun t => phaseOf n m B t = j), f t ≤
      r j * B j * n * (1 - Real.exp (-α j)) - θ * n * α j + 3 * r j := by
    intro j hj
    simp only [mem_Icc] at hj
    set R : ℕ := n - ⌊(1 - B j) * n⌋₊ with hR
    have hfl_le : ⌊(1 - B j) * (n : ℝ)⌋₊ ≤ n := by
      apply Nat.floor_le_of_le
      have := hBpos j hj.1 hj.2
      nlinarith
    have hle : ∑ t ∈ (range n).filter (fun t => phaseOf n m B t = j), f t ≤
        ∑ u ∈ Icc 1 R, max (r j - θ * n / u) 0 := by
      have himg : ∑ t ∈ (range n).filter (fun t => phaseOf n m B t = j), f t =
          ∑ u ∈ ((range n).filter (fun t => phaseOf n m B t = j)).image (fun t => n - t),
            max (r j - θ * n / u) 0 := by
        rw [sum_image]
        · apply sum_congr rfl
          intro t ht
          simp only [mem_filter, mem_range] at ht
          simp only [hf, ht.2]
          rw [Nat.cast_sub ht.1.le]
        · intro x hx y hy hxy
          simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hx hy
          simp only at hxy
          omega
      rw [himg]
      apply sum_le_sum_of_subset_of_nonneg
      · intro u hu
        simp only [mem_image, mem_filter, mem_range] at hu
        obtain ⟨t, ⟨htn, hpt⟩, rfl⟩ := hu
        have := hphlow t j hpt
        simp only [mem_Icc]
        omega
      · intros; exact le_max_right _ _
    apply le_trans hle
    have hrj := hrpos j hj.1 hj.2
    have hbj := hBpos j hj.1 hj.2
    have hc : 0 < θ * n := by positivity
    have hθj := hBj j hj.1 hj.2
    have hcr : θ * n / r j = B j * Real.exp (-α j) * n := by
      rw [← hθj]; field_simp
    have hcY : θ * n / r j ≤ B j * n := by
      rw [hcr]
      have : Real.exp (-α j) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hα.1 j hj.1 hj.2])
      have : 0 ≤ B j * n := by positivity
      nlinarith
    have hRcast : (R : ℝ) = n - (⌊(1 - B j) * (n : ℝ)⌋₊ : ℝ) := by
      rw [hR, Nat.cast_sub hfl_le]
    have hfl1 : (⌊(1 - B j) * (n : ℝ)⌋₊ : ℝ) ≤ (1 - B j) * n :=
      Nat.floor_le (by have := hBle1 j hj.1 hj.2; nlinarith)
    have hfl2 : (1 - B j) * n < (⌊(1 - B j) * (n : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have H := harmH (r j) (θ * n) (B j * n) R hrj hc hcY (by rw [hRcast]; linarith)
      (by rw [hRcast]; linarith)
    have hlogv : Real.log (r j * (B j * n) / (θ * n)) = α j := by
      have : r j * (B j * n) / (θ * n) = Real.exp (α j) := by
        rw [div_eq_iff hc.ne', ← hθj]
        have : Real.exp (α j) * Real.exp (-α j) = 1 := by rw [← Real.exp_add]; simp
        calc r j * (B j * n) = r j * (B j * n) * (Real.exp (α j) * Real.exp (-α j)) := by
              rw [this, mul_one]
          _ = _ := by ring
      rw [this, Real.log_exp]
    rw [hlogv] at H
    have hexp : r j * (B j * n - θ * n / r j) = r j * B j * n * (1 - Real.exp (-α j)) := by
      rw [hcr]; ring
    linarith
  -- assemble
  have hfib : ∑ t ∈ range n, f t =
      ∑ j ∈ Icc 1 m, ∑ t ∈ (range n).filter (fun t => phaseOf n m B t = j), f t :=
    (Finset.sum_fiberwise_of_maps_to (fun t _ => mem_Icc.2 (hph t)) f).symm
  have hsumf : ∑ t ∈ range n, f t ≤
      ∑ j ∈ Icc 1 m, r j * B j * n * (1 - Real.exp (-α j)) - θ * n + 3 * ∑ j ∈ Icc 1 m, r j := by
    rw [hfib]
    calc _ ≤ ∑ j ∈ Icc 1 m, (r j * B j * n * (1 - Real.exp (-α j)) - θ * n * α j + 3 * r j) :=
          sum_le_sum hphase
      _ = ∑ j ∈ Icc 1 m, r j * B j * n * (1 - Real.exp (-α j)) - θ * n * ∑ j ∈ Icc 1 m, α j +
            3 * ∑ j ∈ Icc 1 m, r j := by
          rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
      _ = _ := by rw [hα.2.1, mul_one]
  have hM := hMS n
  have hMk : ∑ j ∈ Icc 1 m, r j * B j * n * (1 - Real.exp (-α j)) * k =
      k * ∑ j ∈ Icc 1 m, r j * B j * n * (1 - Real.exp (-α j)) := by
    rw [mul_sum]; apply sum_congr rfl; intros; ring
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have h3 : (k : ℝ) * (3 * ∑ j ∈ Icc 1 m, r j) ≤ ε * n * k := by nlinarith
  nlinarith
