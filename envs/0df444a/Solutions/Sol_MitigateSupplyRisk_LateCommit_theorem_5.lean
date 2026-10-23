-- Prove2me | solution 1 for MitigateSupplyRisk.LateCommit.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T12:59:47.979465+00:00
-- url     : https://prove2.me/submissions/ed9aaf0a-199b-4808-a435-e98b29776120

import Mathlib
import Definitions.Def_MitigateSupplyRisk_LateCommit_Model

set_option autoImplicit false

open MeasureTheory

namespace A4d70963

open MitigateSupplyRisk.LateCommit

lemma delivered_nonneg {K q ξ : ℝ} (hq : 0 ≤ q) : 0 ≤ delivered K q ξ :=
  le_min hq (le_max_right _ _)

lemma delivered_le_q (K q ξ : ℝ) : delivered K q ξ ≤ q := min_le_left _ _

lemma delivered_le_K {K q ξ : ℝ} (hK : 0 ≤ K) (hξ : 0 ≤ ξ) : delivered K q ξ ≤ K :=
  (min_le_right _ _).trans (max_le (by linarith) hK)

lemma realized_le (M : Market) (S : Supplier) {c q ξ x : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q)
    (hξ : 0 ≤ ξ) (hx : 0 ≤ x) :
    realizedProfit M S c q ξ x ≤ (M.r + |M.v|) * S.K := by
  unfold realizedProfit
  have hy0 : 0 ≤ delivered S.K q ξ := delivered_nonneg hq
  have hyK : delivered S.K q ξ ≤ S.K := delivered_le_K S.K_pos.le hξ
  set y := delivered S.K q ξ
  have h1 : 0 ≤ (S.η * q + (1 - S.η) * y) * c :=
    mul_nonneg (add_nonneg (mul_nonneg S.η_nonneg hq)
      (mul_nonneg (by linarith [S.η_le_one]) hy0)) hc
  have h2 : M.r * min x y ≤ M.r * S.K :=
    mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hyK) M.r_nonneg
  have h3a : M.v * max (y - x) 0 ≤ |M.v| * max (y - x) 0 :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (le_max_right _ _)
  have h3b : |M.v| * max (y - x) 0 ≤ |M.v| * S.K :=
    mul_le_mul_of_nonneg_left (max_le (by linarith) S.K_pos.le) (abs_nonneg _)
  have h4 : 0 ≤ M.p * max (x - y) 0 := mul_nonneg M.p_nonneg (le_max_right _ _)
  have e : -(S.η * q + (1 - S.η) * y) * c = -((S.η * q + (1 - S.η) * y) * c) := by ring
  rw [e]
  nlinarith

lemma ae_nonneg (M : Market) (S : Supplier) (a : ℝ) :
    ∀ᵐ w ∂((S.ν a).prod M.μ), 0 ≤ w.1 ∧ 0 ≤ w.2 := by
  have := S.ν_prob a
  have := M.μ_prob
  have h1 : ((S.ν a).prod M.μ) {w : ℝ × ℝ | w.1 < 0} = 0 := by
    have : {w : ℝ × ℝ | w.1 < 0} = Set.Iio 0 ×ˢ Set.univ := by ext w; simp
    rw [this, Measure.prod_prod, S.loss_nonneg a, zero_mul]
  have h2 : ((S.ν a).prod M.μ) {w : ℝ × ℝ | w.2 < 0} = 0 := by
    have : {w : ℝ × ℝ | w.2 < 0} = Set.univ ×ˢ Set.Iio 0 := by ext w; simp
    rw [this, Measure.prod_prod, M.demand_nonneg, mul_zero]
  have e1 : ∀ᵐ w ∂((S.ν a).prod M.μ), 0 ≤ w.1 := by
    rw [ae_iff]; simpa only [not_le] using h1
  have e2 : ∀ᵐ w ∂((S.ν a).prod M.μ), 0 ≤ w.2 := by
    rw [ae_iff]; simpa only [not_le] using h2
  filter_upwards [e1, e2] with w hw1 hw2 using ⟨hw1, hw2⟩

lemma C_nonneg (M : Market) (S : Supplier) : 0 ≤ (M.r + |M.v|) * S.K :=
  mul_nonneg (add_nonneg M.r_nonneg (abs_nonneg _)) S.K_pos.le

lemma ssp_le (M : Market) (S : Supplier) {c q : ℝ} (a : ℝ) (hc : 0 ≤ c) (hq : 0 ≤ q) :
    secondStageProfit M S c q a ≤ (M.r + |M.v|) * S.K := by
  have := S.ν_prob a
  have := M.μ_prob
  unfold secondStageProfit
  by_cases hi : Integrable (fun w : ℝ × ℝ => realizedProfit M S c q w.1 w.2) ((S.ν a).prod M.μ)
  · calc _ ≤ ∫ _w, (M.r + |M.v|) * S.K ∂((S.ν a).prod M.μ) :=
          integral_mono_ae hi (integrable_const _)
            (by filter_upwards [ae_nonneg M S a] with w hw
                exact realized_le M S hc hq hw.1 hw.2)
      _ = _ := by simp
  · rw [integral_undef hi]; exact C_nonneg M S

lemma opt_le (M : Market) (S : Supplier) {c : ℝ} (a : ℝ) (hc : 0 ≤ c) :
    optValue M S c a ≤ (M.r + |M.v|) * S.K :=
  Real.sSup_le (by rintro _ ⟨q, hq, rfl⟩; exact ssp_le M S a hc hq) (C_nonneg M S)

lemma ssp_mono (M : Market) (S : Supplier) {c₁ c₂ q : ℝ} (a : ℝ) (h12 : c₁ ≤ c₂)
    (hq : 0 ≤ q) : secondStageProfit M S c₂ q a ≤ secondStageProfit M S c₁ q a := by
  have := S.ν_prob a
  have := M.μ_prob
  set B : ℝ × ℝ → ℝ := fun w => S.η * q + (1 - S.η) * delivered S.K q w.1 with hBdef
  have hB0 : ∀ w, 0 ≤ B w := fun w =>
    add_nonneg (mul_nonneg S.η_nonneg hq)
      (mul_nonneg (by linarith [S.η_le_one]) (delivered_nonneg hq))
  have hBq : ∀ w, B w ≤ q := fun w => by
    have := delivered_le_q S.K q w.1
    have h1 : (1 - S.η) * delivered S.K q w.1 ≤ (1 - S.η) * q :=
      mul_le_mul_of_nonneg_left this (by linarith [S.η_le_one])
    simp only [hBdef]; nlinarith
  have hBc : Continuous B := by
    simp only [hBdef, delivered]; fun_prop
  have hB : Integrable B ((S.ν a).prod M.μ) :=
    Integrable.mono' (integrable_const q) hBc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [hB0 w, hBq w], hBq w⟩)
  have hdiff : ∀ w : ℝ × ℝ, realizedProfit M S c₂ q w.1 w.2
      = realizedProfit M S c₁ q w.1 w.2 - (c₂ - c₁) * B w := by
    intro w; simp only [realizedProfit, hBdef]; ring
  have hle : ∀ w : ℝ × ℝ, realizedProfit M S c₂ q w.1 w.2 ≤ realizedProfit M S c₁ q w.1 w.2 := by
    intro w; rw [hdiff]
    have := mul_nonneg (sub_nonneg.2 h12) (hB0 w)
    linarith
  unfold secondStageProfit
  by_cases hi : Integrable (fun w : ℝ × ℝ => realizedProfit M S c₁ q w.1 w.2) ((S.ν a).prod M.μ)
  · have hi2 : Integrable (fun w : ℝ × ℝ => realizedProfit M S c₂ q w.1 w.2)
        ((S.ν a).prod M.μ) := by
      have e : (fun w : ℝ × ℝ => realizedProfit M S c₂ q w.1 w.2)
          = fun w => realizedProfit M S c₁ q w.1 w.2 - (c₂ - c₁) * B w := funext hdiff
      rw [e]; exact hi.sub (hB.const_mul _)
    exact integral_mono hi2 hi hle
  · have hi2 : ¬ Integrable (fun w : ℝ × ℝ => realizedProfit M S c₂ q w.1 w.2)
        ((S.ν a).prod M.μ) := by
      intro h2; apply hi
      have e : (fun w : ℝ × ℝ => realizedProfit M S c₁ q w.1 w.2)
          = fun w => realizedProfit M S c₂ q w.1 w.2 + (c₂ - c₁) * B w := by
        funext w; rw [hdiff]; ring
      rw [e]; exact h2.add (hB.const_mul _)
    rw [integral_undef hi, integral_undef hi2]

lemma opt_mono (M : Market) (S : Supplier) {c₁ c₂ : ℝ} (a : ℝ) (hc₁ : 0 ≤ c₁) (h12 : c₁ ≤ c₂) :
    optValue M S c₂ a ≤ optValue M S c₁ a := by
  have hbdd : BddAbove ((fun q => secondStageProfit M S c₁ q a) '' Set.Ici 0) :=
    ⟨(M.r + |M.v|) * S.K, by rintro _ ⟨q, hq, rfl⟩; exact ssp_le M S a hc₁ hq⟩
  unfold optValue
  refine csSup_le ⟨_, 0, (Set.mem_Ici.2 le_rfl), rfl⟩ ?_
  rintro _ ⟨q, hq, rfl⟩
  exact (ssp_mono M S a h12 hq).trans (le_csSup hbdd ⟨q, hq, rfl⟩)

lemma core (M : Market) (S : Supplier) (c₁ c₂ : ℝ) (I : Improvement) (hc₁ : 0 ≤ c₁)
    (hc : c₁ ≤ c₂) (hθ₀ : 0 < I.θ) (hθ₁ : I.θ < 1) {a : ℝ} (ha : I.a0 ≤ a)
    (hmax : ∀ a', a' ∈ Set.Ici I.a0 → earlyProfit M S c₂ I a' ≤ earlyProfit M S c₂ I a)
    (hgain : I.m * I.z a / (I.θ * (1 - I.θ))
      < max (optValue M S c₂ a - optValue M S c₁ I.a0) 0) :
    max (sSup (earlyProfit M S c₁ I '' Set.Ici I.a0)) (sSup (earlyProfit M S c₂ I '' Set.Ici I.a0))
      < sSup ((fun b : ℝ × ℝ =>
          -(I.m * I.z b.1) - I.m * I.z b.2
            + I.θ * I.θ * max (optValue M S c₁ b.1) (optValue M S c₂ b.2)
            + I.θ * (1 - I.θ) * max (optValue M S c₁ b.1) (optValue M S c₂ I.a0)
            + (1 - I.θ) * I.θ * max (optValue M S c₁ I.a0) (optValue M S c₂ b.2)
            + (1 - I.θ) * (1 - I.θ) * max (optValue M S c₁ I.a0) (optValue M S c₂ I.a0))
          '' {b : ℝ × ℝ | I.a0 ≤ b.1 ∧ I.a0 ≤ b.2}) := by
  set θ := I.θ with hθdef
  set P₁ : ℝ → ℝ := fun t => optValue M S c₁ t with hP₁
  set P₂ : ℝ → ℝ := fun t => optValue M S c₂ t with hP₂
  set C := (M.r + |M.v|) * S.K with hCdef
  have hC1 : ∀ t, P₁ t ≤ C := fun t => opt_le M S t hc₁
  have hC2 : ∀ t, P₂ t ≤ C := fun t => opt_le M S t (hc₁.trans hc)
  have h21 : ∀ t, P₂ t ≤ P₁ t := fun t => opt_mono M S t hc₁ hc
  have hz : ∀ t, I.a0 ≤ t → 0 ≤ I.z t := fun t ht => by
    have := I.z_mono ((Set.mem_Ici.2 le_rfl)) (Set.mem_Ici.2 ht) ht
    rwa [I.z_a0] at this
  have hw : 0 < θ * (1 - θ) := mul_pos hθ₀ (by linarith)
  have hm := I.m_nonneg
  set L : ℝ × ℝ → ℝ := fun b =>
          -(I.m * I.z b.1) - I.m * I.z b.2
            + θ * θ * max (P₁ b.1) (P₂ b.2)
            + θ * (1 - θ) * max (P₁ b.1) (P₂ I.a0)
            + (1 - θ) * θ * max (P₁ I.a0) (P₂ b.2)
            + (1 - θ) * (1 - θ) * max (P₁ I.a0) (P₂ I.a0) with hL
  -- the late set is bounded above by C
  have hbdd : BddAbove (L '' {b : ℝ × ℝ | I.a0 ≤ b.1 ∧ I.a0 ≤ b.2}) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨b, ⟨hb1, hb2⟩, rfl⟩
    have z1 := mul_nonneg hm (hz _ hb1)
    have z2 := mul_nonneg hm (hz _ hb2)
    have w1 : 0 ≤ θ * θ := mul_nonneg hθ₀.le hθ₀.le
    have w2 : 0 ≤ θ * (1 - θ) := hw.le
    have w3 : 0 ≤ (1 - θ) * θ := by rw [mul_comm]; exact hw.le
    have w4 : 0 ≤ (1 - θ) * (1 - θ) := mul_nonneg (by linarith) (by linarith)
    have m1 := mul_le_mul_of_nonneg_left (max_le (hC1 b.1) (hC2 b.2)) w1
    have m2 := mul_le_mul_of_nonneg_left (max_le (hC1 b.1) (hC2 I.a0)) w2
    have m3 := mul_le_mul_of_nonneg_left (max_le (hC1 I.a0) (hC2 b.2)) w3
    have m4 := mul_le_mul_of_nonneg_left (max_le (hC1 I.a0) (hC2 I.a0)) w4
    have e : θ * θ * C + θ * (1 - θ) * C + (1 - θ) * θ * C + (1 - θ) * (1 - θ) * C = C := by ring
    simp only [hL]
    linarith
  -- the gain
  set ε := θ * (1 - θ) * max (P₂ a - P₁ I.a0) 0 - I.m * I.z a with hε
  have hεpos : 0 < ε := by
    have := (div_lt_iff₀ hw).1 hgain
    simp only [hε]; linarith
  -- key bound: early₁ a' + ε ≤ L (a', a)
  have key : ∀ a', I.a0 ≤ a' → earlyProfit M S c₁ I a' + ε ≤ L (a', a) := by
    intro a' ha'
    have w1 : 0 ≤ θ * θ := mul_nonneg hθ₀.le hθ₀.le
    have w4 : 0 ≤ (1 - θ) * (1 - θ) := mul_nonneg (by linarith) (by linarith)
    have m1 := mul_le_mul_of_nonneg_left (le_max_left (P₁ a') (P₂ a)) w1
    have m2 := mul_le_mul_of_nonneg_left (le_max_left (P₁ a') (P₂ I.a0)) hw.le
    have m4 := mul_le_mul_of_nonneg_left (le_max_left (P₁ I.a0) (P₂ I.a0)) w4
    have e3 : max (P₁ I.a0) (P₂ a) = P₁ I.a0 + max (P₂ a - P₁ I.a0) 0 := by
      rcases le_total (P₁ I.a0) (P₂ a) with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    simp only [hL, earlyProfit, hε, e3]
    simp only [hP₁, hP₂] at m1 m2 m4 ⊢
    nlinarith
  have hLle : ∀ a', I.a0 ≤ a' → L (a', a) ≤ sSup (L '' {b : ℝ × ℝ | I.a0 ≤ b.1 ∧ I.a0 ≤ b.2}) :=
    fun a' ha' => le_csSup hbdd ⟨(a', a), ⟨ha', ha⟩, rfl⟩
  have hE1 : sSup (earlyProfit M S c₁ I '' Set.Ici I.a0)
      ≤ sSup (L '' {b : ℝ × ℝ | I.a0 ≤ b.1 ∧ I.a0 ≤ b.2}) - ε := by
    refine csSup_le ⟨_, I.a0, (Set.mem_Ici.2 le_rfl), rfl⟩ ?_
    rintro _ ⟨a', ha', rfl⟩
    have := key a' ha'
    have := hLle a' ha'
    linarith
  have hE2 : sSup (earlyProfit M S c₂ I '' Set.Ici I.a0) ≤ earlyProfit M S c₂ I a := by
    refine csSup_le ⟨_, I.a0, (Set.mem_Ici.2 le_rfl), rfl⟩ ?_
    rintro _ ⟨a', ha', rfl⟩
    exact hmax a' ha'
  have h21e : earlyProfit M S c₂ I a ≤ earlyProfit M S c₁ I a := by
    unfold earlyProfit
    have := mul_le_mul_of_nonneg_left (h21 a) hθ₀.le
    have := mul_le_mul_of_nonneg_left (h21 I.a0) (show (0:ℝ) ≤ 1 - θ by linarith)
    simp only [hP₁, hP₂] at *
    linarith
  have hk := key a ha
  have hl := hLle a ha
  exact max_lt (by linarith) (by linarith)

end A4d70963

open MitigateSupplyRisk.LateCommit in
theorem solution (X : Setting) (hid : X.IdenticalExceptCost) (hc : X.c₁ ≤ X.c₂)
    (hθ₀ : 0 < X.I₂.θ) (hθ₁ : X.I₂.θ < 1)
    {a₂E : ℝ} (ha₂E : X.I₂.a0 ≤ a₂E) (hmax : IsMaxOn X.early₂ (Set.Ici X.I₂.a0) a₂E)
    (hgain : X.I₂.m * X.I₂.z a₂E / (X.I₂.θ * (1 - X.I₂.θ)) < max (X.P₂ a₂E - X.P₁ X.I₁.a0) 0) :
    X.earlyValue < X.lateValue := by
  obtain ⟨M, S, S', c₁, c₂, I, I', hc₁, hc₂⟩ := X
  obtain ⟨rfl, rfl⟩ : S = S' ∧ I = I' := hid
  exact A4d70963.core M S c₁ c₂ I hc₁ hc hθ₀ hθ₁ ha₂E
    (fun a' ha' => isMaxOn_iff.mp hmax a' ha') hgain
