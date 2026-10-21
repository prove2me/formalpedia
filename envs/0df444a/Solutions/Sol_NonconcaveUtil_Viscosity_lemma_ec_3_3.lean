-- Prove2me | solution 1 for NonconcaveUtil.Viscosity.lemma_ec_3_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:39:52.373101+00:00
-- url     : https://prove2.me/submissions/591b9d30-e880-49e4-8384-8f699d316994

import Mathlib

set_option autoImplicit false

open Filter Topology

namespace Ec33Aux

lemma supergrad (B : ℝ) (f : ℝ → ℝ) (hconc : ConcaveOn ℝ (Set.Ioi B) f)
    (hmono : MonotoneOn f (Set.Ioi B)) (w₀ : ℝ) (hw₀ : B < w₀) :
    ∃ σ : ℝ, 0 ≤ σ ∧ ∀ w > B, f w ≤ f w₀ + σ * (w - w₀) := by
  set S : Set ℝ := {s | ∃ y, w₀ < y ∧ s = (f y - f w₀) / (y - w₀)} with hS
  have hmem : ∀ y, w₀ < y → (f y - f w₀) / (y - w₀) ∈ S := fun y hy => ⟨y, hy, rfl⟩
  have hne : S.Nonempty := ⟨_, hmem (w₀ + 1) (by linarith)⟩
  have hx : (B + w₀) / 2 ∈ Set.Ioi B := by simp only [Set.mem_Ioi]; linarith
  have hw : w₀ ∈ Set.Ioi B := hw₀
  have hbdd : BddAbove S := by
    refine ⟨(f w₀ - f ((B + w₀) / 2)) / (w₀ - (B + w₀) / 2), ?_⟩
    rintro s ⟨y, hy, rfl⟩
    exact hconc.slope_anti_adjacent hx (show y ∈ Set.Ioi B by simp only [Set.mem_Ioi]; linarith)
      (by linarith) hy
  refine ⟨sSup S, ?_, ?_⟩
  · have h1 := le_csSup hbdd (hmem (w₀ + 1) (by linarith))
    have h2 : 0 ≤ (f (w₀ + 1) - f w₀) / (w₀ + 1 - w₀) := by
      apply div_nonneg
      · have := hmono hw (show w₀ + 1 ∈ Set.Ioi B by simp only [Set.mem_Ioi]; linarith)
          (by linarith)
        linarith
      · linarith
    linarith
  · intro w hw'
    rcases lt_trichotomy w w₀ with h | h | h
    · have : sSup S ≤ (f w₀ - f w) / (w₀ - w) := by
        apply csSup_le hne
        rintro s ⟨y, hy, rfl⟩
        exact hconc.slope_anti_adjacent (show w ∈ Set.Ioi B from hw') (show y ∈ Set.Ioi B by
          simp only [Set.mem_Ioi]; linarith) h hy
      rw [le_div_iff₀ (by linarith)] at this
      nlinarith
    · subst h; simp
    · have := le_csSup hbdd (hmem w h)
      rw [div_le_iff₀ (by linarith)] at this
      nlinarith

lemma interp (q C₁ C₂ a b B W : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hC : 0 ≤ C₁) (hB : 0 ≤ B)
    (hBW : B ≤ W) (h1 : a + b * B ≤ C₁ * B ^ q + C₂) (h2 : a + b * W ≤ C₁ * W ^ q + C₂)
    (w : ℝ) (hw1 : B ≤ w) (hw2 : w ≤ W) : a + b * w ≤ C₁ * w ^ q + C₂ := by
  have hc := Real.strictConcaveOn_rpow hq0 hq1
  rcases eq_or_lt_of_le hBW with h | h
  · have : w = B := le_antisymm (h ▸ hw2) hw1
    subst this; exact h1
  · set t : ℝ := (W - w) / (W - B) with ht
    have hWB : 0 < W - B := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hWB.le
    have ht1 : 0 ≤ 1 - t := by
      rw [ht, sub_nonneg, div_le_one hWB]; linarith
    have hw : w = t * B + (1 - t) * W := by
      rw [ht]; field_simp; ring
    have key := hc.concaveOn.2 (show B ∈ Set.Ici (0:ℝ) from hB)
      (show W ∈ Set.Ici (0:ℝ) from hB.trans hBW) ht0 ht1 (by ring)
    simp only [smul_eq_mul] at key
    rw [← hw] at key
    have e1 : a + b * w = t * (a + b * B) + (1 - t) * (a + b * W) := by rw [hw]; ring
    rw [e1]
    nlinarith [mul_le_mul_of_nonneg_left h1 ht0, mul_le_mul_of_nonneg_left h2 ht1,
      mul_le_mul_of_nonneg_left key hC]

lemma tail (p q C₁ C₂ W : ℝ) (hp : 0 < p) (hpq : p ≤ q) (hq1 : q < 1) (hW : 0 < W)
    (hC : 0 ≤ C₁) (h1 : W ^ p ≤ C₁ * W ^ q + C₂) (h2 : p * W ^ p ≤ C₁ * q * W ^ q)
    (w : ℝ) (hw : W ≤ w) : w ^ p ≤ C₁ * w ^ q + C₂ := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  set t := w / W with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hW]; linarith
  have hwt : w = W * t := by rw [ht]; field_simp
  have hwp : w ^ p = W ^ p * t ^ p := by rw [hwt, Real.mul_rpow hW.le (by linarith)]
  have hwq : w ^ q = W ^ q * t ^ q := by rw [hwt, Real.mul_rpow hW.le (by linarith)]
  have htq : 1 ≤ t ^ q := Real.one_le_rpow ht1 hq.le
  have htp : t ^ p = (t ^ q) ^ (p / q) := by
    rw [← Real.rpow_mul (by linarith)]; congr 1; field_simp
  have bern := rpow_one_add_le_one_add_mul_self (s := t ^ q - 1) (by linarith)
    (show 0 ≤ p / q from div_nonneg hp.le hq.le) (show p / q ≤ 1 by rw [div_le_one hq]; exact hpq)
  rw [add_sub_cancel] at bern
  rw [← htp] at bern
  have hWp : 0 < W ^ p := Real.rpow_pos_of_pos hW p
  have hWq : 0 < W ^ q := Real.rpow_pos_of_pos hW q
  have h4 : W ^ p * t ^ p ≤ W ^ p + W ^ p * (p / q) * (t ^ q - 1) := by nlinarith
  rw [hwp, hwq]
  have : W ^ p * (p / q) = p / q * W ^ p := by ring
  have h5 : p / q * W ^ p ≤ C₁ * W ^ q := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hq]; nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h5 (show 0 ≤ t ^ q - 1 by linarith)]

end Ec33Aux

theorem solution (B : ℝ) (hB : 0 ≤ B) (f : ℝ → ℝ)
    (hconc : ConcaveOn ℝ (Set.Ioi B) f)
    (hmono : MonotoneOn f (Set.Ioi B))
    (p : ℝ) (hp : 0 < p ∧ p < 1)
    (hsmall : Tendsto (fun w : ℝ => f w / w ^ p) atTop (𝓝 0))
    (w₀ ε : ℝ) (hw₀ : B < w₀) (hε : 0 < ε) :
    ∃ C₁ C₂ q : ℝ, p ≤ q ∧ q < 1 ∧
      (∀ w > B, f w ≤ C₁ * w ^ q + C₂) ∧
      C₁ * w₀ ^ q + C₂ ≤ f w₀ + ε := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨σ, hσ0, hσ⟩ := Ec33Aux.supergrad B f hconc hmono w₀ hw₀
  have hwB : 0 < w₀ - B := by linarith
  set N : ℝ := ε + σ * (w₀ - B) with hN
  have hNpos : 0 < N := by positivity
  set a : ℝ := N / (w₀ - B) with ha
  have hapos : 0 < a := div_pos hNpos hwB
  have haσ : σ < a := by
    rw [ha, lt_div_iff₀ hwB, hN]; nlinarith
  -- W₀
  have hev1 : ∀ᶠ w in atTop, f w / w ^ p < 1 := hsmall.eventually (gt_mem_nhds one_pos)
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.1 hev1
  have hev2 : ∀ᶠ W : ℝ in atTop, W ^ (-(1 - p)) < min (a / 2) (a / (2 * p)) :=
    (tendsto_rpow_neg_atTop (show 0 < 1 - p by linarith)).eventually
      (gt_mem_nhds (lt_min (by positivity) (by positivity)))
  set K : ℝ := 2 * (a * w₀ - f w₀ - ε) / a with hK
  obtain ⟨W, hWa, hWb, hWc, hWd, hWe⟩ :
      ∃ W : ℝ, W₀ ≤ W ∧ w₀ < W ∧ K < W ∧ 0 < W ∧ W ^ (-(1 - p)) < min (a / 2) (a / (2 * p)) :=
    ((eventually_ge_atTop W₀).and ((eventually_gt_atTop w₀).and ((eventually_gt_atTop K).and
      ((eventually_gt_atTop 0).and hev2)))).exists
  have hWp : W ^ p = W ^ (-(1 - p)) * W := by
    have : W ^ p = W ^ (-(1 - p) + 1) := by congr 1; ring
    rw [this, Real.rpow_add hWd, Real.rpow_one]
  have hWp1 : W ^ p ≤ a / 2 * W := by
    rw [hWp]; exact mul_le_mul_of_nonneg_right (hWe.le.trans (min_le_left _ _)) hWd.le
  have hWp2 : p * W ^ p < a * W := by
    have h := hWe.trans_le (min_le_right _ _)
    rw [hWp]
    rw [lt_div_iff₀ (by positivity)] at h
    nlinarith
  have hKW : a * w₀ - f w₀ - ε < a / 2 * W := by
    have : K * a = 2 * (a * w₀ - f w₀ - ε) := by rw [hK]; field_simp
    nlinarith
  -- q-dependent quantities
  set D : ℝ → ℝ := fun q => w₀ ^ q - B ^ q with hD
  set C : ℝ → ℝ := fun q => N / D q with hCdef
  set E : ℝ → ℝ := fun q => f w₀ + ε + C q * (W ^ q - w₀ ^ q) with hE
  have hcB : ∀ x : ℝ, ContinuousAt (fun q : ℝ => x ^ q) 1 := fun x => Real.continuousAt_const_rpow' one_ne_zero
  have hD1 : D 1 = w₀ - B := by simp [hD]
  have hDc : ContinuousAt D 1 := (hcB w₀).sub (hcB B)
  have hCc : ContinuousAt C 1 := continuousAt_const.div hDc (by rw [hD1]; exact hwB.ne')
  have hC1 : C 1 = a := by simp [hCdef, hD1, ha]
  have hEc : ContinuousAt E 1 := continuousAt_const.add (hCc.mul ((hcB W).sub (hcB w₀)))
  have hE1 : E 1 = f w₀ + ε + a * (W - w₀) := by simp [hE, hC1]
  have hCq : ContinuousAt (fun q => C q * q * W ^ q) 1 := (hCc.mul continuousAt_id).mul (hcB W)
  have hCq1 : (fun q => C q * q * W ^ q) 1 = a * W := by simp [hC1]
  have hP1 : ∀ᶠ q in 𝓝 (1:ℝ), f w₀ + σ * (W - w₀) < E q := by
    apply continuousAt_const.eventually_lt hEc
    rw [hE1]
    have : 0 < (a - σ) * (W - w₀) := mul_pos (by linarith) (by linarith)
    nlinarith
  have hP2 : ∀ᶠ q in 𝓝 (1:ℝ), W ^ p < E q := by
    apply continuousAt_const.eventually_lt hEc
    rw [hE1]; nlinarith
  have hP3 : ∀ᶠ q in 𝓝 (1:ℝ), p * W ^ p < C q * q * W ^ q := by
    apply continuousAt_const.eventually_lt hCq
    show p * W ^ p < C 1 * 1 * W ^ (1:ℝ)
    rw [hC1, mul_one, Real.rpow_one]; exact hWp2
  have hP4 : ∀ᶠ q in 𝓝 (1:ℝ), 0 < D q := by
    apply continuousAt_const.eventually_lt hDc
    rw [hD1]; exact hwB
  obtain ⟨q, ⟨hq1, hq2, hq3, hq4⟩, hq5⟩ :
      ∃ q : ℝ, ((f w₀ + σ * (W - w₀) < E q) ∧ (W ^ p < E q) ∧ (p * W ^ p < C q * q * W ^ q) ∧
        0 < D q) ∧ q ∈ Set.Ioo p 1 :=
    (((hP1.and (hP2.and (hP3.and hP4))).filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsLT hp1)).exists |>.imp fun q hq => ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.1, hq.1.2.2.2⟩, hq.2⟩
  obtain ⟨hpq, hq1'⟩ := hq5
  have hq0 : 0 < q := hp0.trans hpq
  have hCpos : 0 ≤ C q := (div_pos hNpos hq4).le
  have hCD : C q * D q = N := by simp only [hCdef]; field_simp
  refine ⟨C q, f w₀ + ε - C q * w₀ ^ q, q, hpq.le, hq1', ?_, by linarith⟩
  intro w hw
  rcases le_total w W with hwW | hwW
  · have hL := hσ w hw
    have key := Ec33Aux.interp q (C q) (f w₀ + ε - C q * w₀ ^ q) (f w₀ - σ * w₀) σ B W hq0 hq1' hCpos hB
      (by linarith) ?_ ?_ w hw.le hwW
    · linarith
    · have : C q * (w₀ ^ q - B ^ q) = N := hCD
      rw [hN] at this
      linarith [mul_sub (C q) (w₀ ^ q) (B ^ q)]
    · simp only [hE] at hq1
      linarith [mul_sub (C q) (W ^ q) (w₀ ^ q)]
  · have := Ec33Aux.tail p q (C q) (f w₀ + ε - C q * w₀ ^ q) W hp0 hpq.le hq1' hWd hCpos ?_ ?_ w hwW
    · have h2 := hW₀ w (hWa.trans hwW)
      have hwpos : 0 < w ^ p := Real.rpow_pos_of_pos (by linarith) p
      rw [div_lt_one hwpos] at h2
      linarith
    · simp only [hE] at hq2; linarith [mul_sub (C q) (W ^ q) (w₀ ^ q)]
    · linarith
