-- Prove2me | solution 1 for MarketplaceLeakage.Communication.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T10:53:45.841064+00:00
-- url     : https://prove2.me/submissions/11c8a814-1e1f-4cec-8711-755a66685d4e

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_Setting

set_option autoImplicit false

namespace MLP3Aux

open MarketplaceLeakage.Communication MarketplaceLeakage.Baseline

/-! ## The ban game -/

lemma low_sub_high (v c q η f : ℝ) :
    lowPay v c q η f - highPay v c q η f
      = ((1 - η + η * q) * (q * v - c) - η * q * (v - c)) - (1 - η) * f := by
  unfold lowPay highPay; ring

/-- The indifference fee of the seller (low and high options pay the same). -/
noncomputable def fhat (v c q η : ℝ) : ℝ :=
  ((1 - η + η * q) * (q * v - c) - η * q * (v - c)) / (1 - η)

lemma fhat_mul (v c q η : ℝ) (h : η < 1) :
    (1 - η) * fhat v c q η = (1 - η + η * q) * (q * v - c) - η * q * (v - c) := by
  have h1 : (1:ℝ) - η ≠ 0 := ne_of_gt (by linarith)
  unfold fhat
  field_simp

lemma fhat_mulA (v c q η : ℝ) (h : η < 1) :
    fhat v c q η * (1 - η + η * q) = PiL v c q η := by
  have h1 : (1:ℝ) - η ≠ 0 := ne_of_gt (by linarith)
  unfold fhat PiL
  field_simp
  ring

lemma banRev_le (v c q η M : ℝ) (hM0 : 0 ≤ M)
    (hH : (v - c) * (η * q) ≤ M)
    (hL : ∀ f, ¬ lowPay v c q η f < highPay v c q η f → 0 ≤ lowPay v c q η f →
      f * (1 - η + η * q) ≤ M)
    (f : ℝ) : banRev v c q η f ≤ M := by
  unfold banRev
  split_ifs with h1 h2 h3
  · have h2' : 0 ≤ η * q * (v - c - f) := h2
    have e : (v - c) * (η * q) - f * (η * q) = η * q * (v - c - f) := by ring
    linarith
  · exact hM0
  · exact hL f h1 h3
  · exact hM0

lemma banRev_vc (v c q η : ℝ) (hvc : c < v) (hq : 0 ≤ q) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (v - c) * (η * q) ≤ banRev v c q η (v - c) := by
  have hz : highPay v c q η (v - c) = 0 := by unfold highPay; ring
  unfold banRev
  rw [hz]
  by_cases h1 : lowPay v c q η (v - c) < 0
  · rw [if_pos h1, if_pos le_rfl]
  · rw [if_neg h1, if_pos (not_lt.1 h1)]
    nlinarith [mul_nonneg (sub_nonneg.2 hvc.le) (sub_nonneg.2 hη1)]

lemma banRev_L (v c q η f : ℝ) (hq0 : 0 < q) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (h1 : ¬ lowPay v c q η f < highPay v c q η f) (h2 : 0 ≤ lowPay v c q η f) :
    f * (1 - η + η * q) ≤ max (banRev v c q η (q * v - c)) (banRev v c q η (fhat v c q η)) := by
  have hA : 0 < 1 - η + η * q := by
    rcases lt_or_eq_of_le hη1 with h | h
    · nlinarith [mul_nonneg hη0 hq0.le]
    · rw [h]; linarith
  have h2' : 0 ≤ (1 - η + η * q) * (q * v - c - f) := h2
  have hf : f ≤ q * v - c := by
    by_contra hcon
    push_neg at hcon
    have : (1 - η + η * q) * (q * v - c - f) < 0 := mul_neg_of_pos_of_neg hA (by linarith)
    linarith
  have hd := low_sub_high v c q η f
  have hd2 := low_sub_high v c q η (q * v - c)
  push_neg at h1
  by_cases hc : lowPay v c q η (q * v - c) < highPay v c q η (q * v - c)
  · have hη : η < 1 := by
      rcases lt_or_eq_of_le hη1 with h | h
      · exact h
      · exfalso
        subst h
        simp only [sub_self, zero_mul, sub_zero] at hd hd2
        linarith
    have hfm := fhat_mul v c q η hη
    have h1η : 0 < 1 - η := by linarith
    have hfh : f ≤ fhat v c q η := by
      have : (1 - η) * f ≤ (1 - η) * fhat v c q η := by linarith
      exact le_of_mul_le_mul_left this h1η
    have hfh2 : fhat v c q η < q * v - c := by
      have hl0 : lowPay v c q η (q * v - c) = 0 := by unfold lowPay; ring
      have : (1 - η) * fhat v c q η < (1 - η) * (q * v - c) := by linarith
      exact lt_of_mul_lt_mul_left this h1η.le
    have e := low_sub_high v c q η (fhat v c q η)
    have hn : ¬ lowPay v c q η (fhat v c q η) < highPay v c q η (fhat v c q η) := by
      rw [not_lt]; linarith
    have hp : 0 ≤ lowPay v c q η (fhat v c q η) := by
      show 0 ≤ (1 - η + η * q) * (q * v - c - fhat v c q η)
      exact mul_nonneg hA.le (by linarith)
    have key : banRev v c q η (fhat v c q η) = fhat v c q η * (1 - η + η * q) := by
      unfold banRev
      rw [if_neg hn, if_pos hp]
    calc f * (1 - η + η * q) ≤ fhat v c q η * (1 - η + η * q) :=
          mul_le_mul_of_nonneg_right hfh hA.le
      _ = banRev v c q η (fhat v c q η) := key.symm
      _ ≤ _ := le_max_right _ _
  · have hp : 0 ≤ lowPay v c q η (q * v - c) := by
      show 0 ≤ (1 - η + η * q) * (q * v - c - (q * v - c))
      simp
    have key : banRev v c q η (q * v - c) = (q * v - c) * (1 - η + η * q) := by
      unfold banRev
      rw [if_neg hc, if_pos hp]
    calc f * (1 - η + η * q) ≤ (q * v - c) * (1 - η + η * q) :=
          mul_le_mul_of_nonneg_right hf hA.le
      _ = banRev v c q η (q * v - c) := key.symm
      _ ≤ _ := le_max_left _ _

lemma exists_banValue (v c q η : ℝ) (hvc : c < v) (hq0 : 0 < q) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    ∃ V, IsBanValue v c q η V := by
  refine ⟨max (banRev v c q η (v - c))
    (max (banRev v c q η (q * v - c)) (banRev v c q η (fhat v c q η))), ?_, ?_⟩
  · rcases max_choice (banRev v c q η (v - c))
      (max (banRev v c q η (q * v - c)) (banRev v c q η (fhat v c q η))) with h | h <;> rw [h]
    · exact ⟨_, rfl⟩
    · rcases max_choice (banRev v c q η (q * v - c)) (banRev v c q η (fhat v c q η)) with h' | h' <;>
        rw [h'] <;> exact ⟨_, rfl⟩
  · rintro _ ⟨f, rfl⟩
    have hvc' := banRev_vc v c q η hvc hq0.le hη0 hη1
    have h0 : 0 ≤ (v - c) * (η * q) := mul_nonneg (by linarith) (mul_nonneg hη0 hq0.le)
    apply banRev_le
    · exact le_max_of_le_left (le_trans h0 hvc')
    · exact le_max_of_le_left hvc'
    · intro g h1 h2
      exact le_max_of_le_right (banRev_L v c q η g hq0 hη0 hη1 h1 h2)

lemma prefersBan_of (v c q η P f : ℝ) (hvc : c < v) (hq0 : 0 < q) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (h : q * P < banRev v c q η f) : PrefersBan v c q η P := by
  obtain ⟨V, hV⟩ := exists_banValue v c q η hvc hq0 hη0 hη1
  exact ⟨V, hV, lt_of_lt_of_le h (hV.2 ⟨f, rfl⟩)⟩

lemma banRev_fhat (v c q η : ℝ) (hv : 0 ≤ v) (hq0 : 0 < q) (hq1 : q < 1) (hη0 : 0 ≤ η)
    (h : η < 1) : banRev v c q η (fhat v c q η) = fhat v c q η * (1 - η + η * q) := by
  have hA : 0 < 1 - η + η * q := by nlinarith
  have hfm := fhat_mul v c q η h
  have e := low_sub_high v c q η (fhat v c q η)
  have hle : fhat v c q η ≤ q * v - c := by
    have h3 : 0 ≤ η * q * ((1 - q) * v) :=
      mul_nonneg (mul_nonneg hη0 hq0.le) (mul_nonneg (by linarith) hv)
    have : (1 - η) * fhat v c q η ≤ (1 - η) * (q * v - c) := by nlinarith
    exact le_of_mul_le_mul_left this (by linarith)
  have hn : ¬ lowPay v c q η (fhat v c q η) < highPay v c q η (fhat v c q η) := by
    rw [not_lt]; linarith
  have hp : 0 ≤ lowPay v c q η (fhat v c q η) := by
    show 0 ≤ (1 - η + η * q) * (q * v - c - fhat v c q η)
    exact mul_nonneg hA.le (by linarith)
  unfold banRev
  rw [if_neg hn, if_pos hp]

/-! ## Shape of `Π_L` -/

lemma PiL_t (v c q η : ℝ) (h : η < 1) :
    PiL v c q η = (q * (q * v * (2 - q) - c) - q * (1 - q) ^ 2 * v)
      + (1 - q) * (q * v * (2 - q) - c) * (1 - η) - q ^ 2 * (1 - q) * v / (1 - η) := by
  have h1 : (1:ℝ) - η ≠ 0 := ne_of_gt (by linarith)
  unfold PiL
  field_simp
  ring

lemma conc (α β γ L s u : ℝ) (hγ : 0 < γ) (hs : 0 < s) (hsu : s < u) (hu : u ≤ 1)
    (h1 : L < α + β - γ) (hsL : α + β * s - γ / s = L) : L < α + β * u - γ / u := by
  have hu0 : 0 < u := by linarith
  have h1s : 0 < 1 - s := by linarith
  have hs' : s ≠ 0 := hs.ne'
  have hu' : u ≠ 0 := hu0.ne'
  have hX : 0 < s * (β * (1 - s) + γ / s - γ) := mul_pos hs (by linarith)
  have e1 : s * (β * (1 - s) + γ / s - γ) = (1 - s) * (β * s + γ) := by field_simp; ring
  have hb : 0 < β * s + γ := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have e2 : s * u * (β * (u - s) + γ / s - γ / u)
      = (u - s) * (u * (β * s + γ) + γ * (1 - u)) := by
    field_simp; ring
  have hpos : 0 < (u - s) * (u * (β * s + γ) + γ * (1 - u)) := by
    apply mul_pos (by linarith)
    have : 0 ≤ γ * (1 - u) := mul_nonneg hγ.le (by linarith)
    nlinarith [mul_pos hu0 hb]
  have hY : 0 < β * (u - s) + γ / s - γ / u := by
    rw [← e2] at hpos
    by_contra hc
    push_neg at hc
    nlinarith [mul_le_mul_of_nonneg_left hc (mul_pos hs hu0).le]
  linarith

lemma PiL_above (v c q ηa ηb L : ℝ) (hv : 0 < v) (hq0 : 0 < q) (hq1 : q < 1)
    (ha0 : 0 ≤ ηa) (hab : ηa < ηb) (hb : ηb < 1) (h0 : L < q * v - c)
    (hbL : PiL v c q ηb = L) : L < PiL v c q ηa := by
  rw [PiL_t v c q ηb hb] at hbL
  rw [PiL_t v c q ηa (by linarith)]
  refine conc _ _ _ L (1 - ηb) (1 - ηa) ?_ (by linarith) (by linarith) (by linarith) ?_ hbL
  · exact mul_pos (mul_pos (pow_pos hq0 2) (by linarith)) hv
  · have : (q * (q * v * (2 - q) - c) - q * (1 - q) ^ 2 * v) + (1 - q) * (q * v * (2 - q) - c)
        - q ^ 2 * (1 - q) * v = q * v - c := by ring
    linarith

lemma small_t (α β γ L : ℝ) (hγ : 0 < γ) : ∃ t, 0 < t ∧ t < 1 ∧ α + β * t - γ / t < L := by
  obtain ⟨N, hN⟩ : ∃ N, N = |α| + |β| + |L| + γ + 1 := ⟨_, rfl⟩
  have hN0 : 0 < N := by rw [hN]; linarith [abs_nonneg α, abs_nonneg β, abs_nonneg L]
  have ht0 : 0 < γ / N := div_pos hγ hN0
  have ht1 : γ / N < 1 := by
    rw [div_lt_one hN0]; rw [hN]; linarith [abs_nonneg α, abs_nonneg β, abs_nonneg L]
  refine ⟨γ / N, ht0, ht1, ?_⟩
  have ht : γ / (γ / N) = N := by
    have : γ ≠ 0 := hγ.ne'
    have : N ≠ 0 := hN0.ne'
    field_simp
  rw [ht]
  have : β * (γ / N) ≤ |β| := by
    calc β * (γ / N) ≤ |β| * (γ / N) := mul_le_mul_of_nonneg_right (le_abs_self β) ht0.le
      _ ≤ |β| * 1 := mul_le_mul_of_nonneg_left ht1.le (abs_nonneg β)
      _ = |β| := mul_one _
  linarith [le_abs_self α, neg_abs_le L]

lemma PiL_zero (v c q : ℝ) : PiL v c q 0 = q * v - c := by
  unfold PiL; simp

lemma cond_ii (v c q PiStar : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hP0 : 0 < PiStar)
    (hP1 : PiStar < v - c) (hcq : c / (v - PiStar) < q) :
    0 < v ∧ q * PiStar < q * v - c := by
  rcases lt_trichotomy (v - PiStar) 0 with h | h | h
  · exfalso
    have : 1 < c / (v - PiStar) := by rw [lt_div_iff_of_neg h]; linarith
    linarith
  · have hv : v = PiStar := by linarith
    refine ⟨by linarith, ?_⟩
    rw [hv]; linarith
  · rw [div_lt_iff₀ h] at hcq
    refine ⟨by linarith, ?_⟩
    nlinarith

/-! ## The uniform baseline -/

lemma G_nonneg (μ s : ℝ) : 0 ≤ G μ s := by
  unfold G; exact le_min (le_max_right _ _) zero_le_one

lemma G_self (μ : ℝ) (hμ : 0 < μ) : G μ μ = 1 := by
  unfold G; rw [div_self hμ.ne']; norm_num

lemma G_mid (μ x : ℝ) (hμ : 0 < μ) (hx0 : 0 ≤ x) (hx1 : x ≤ μ) : G μ x = x / μ := by
  unfold G
  rw [max_eq_left (div_nonneg hx0 hμ.le), min_eq_left ((div_le_one hμ).2 hx1)]

lemma baseline_le (v c μ P : ℝ) (hμ : 0 < μ) (h : IsBaselineValue v c μ P) : P ≤ μ := by
  obtain ⟨f, pd, ⟨hf, ⟨hpd, hopt⟩, -⟩, rfl⟩ := h
  have h1 := hopt (v - μ) (by linarith)
  unfold sProfit at h1
  rw [show v - (v - μ) = μ by ring, G_self μ hμ] at h1
  unfold MProfit
  have hg := G_nonneg μ (v - pd)
  nlinarith [mul_nonneg (sub_nonneg.2 hpd) hg]

lemma sopt_mid (v c μ : ℝ) (hvc : c < v) (hμ : 0 < μ) (h2 : v - c ≤ 2 * μ) :
    IsSOpt v c μ (v - c) (v - (v - c) / 2) := by
  refine ⟨by linarith, fun p hp => ?_⟩
  unfold sProfit
  rw [show v - (v - (v - c) / 2) = (v - c) / 2 by ring,
      G_mid μ ((v - c) / 2) hμ (by linarith) (by linarith)]
  simp only [sub_self, zero_mul, add_zero]
  have hz : (v - c) / 2 / μ * μ = (v - c) / 2 := div_mul_cancel₀ _ hμ.ne'
  have e2 : (v - (v - c) / 2 - c) * ((v - c) / 2 / μ) * μ
      = (v - (v - c) / 2 - c) * ((v - c) / 2) := by rw [mul_assoc, hz]
  rcases le_total (v - p) μ with hx | hx
  · rw [G_mid μ (v - p) hμ (by linarith) hx]
    have hy : (v - p) / μ * μ = v - p := div_mul_cancel₀ _ hμ.ne'
    refine le_of_mul_le_mul_right ?_ hμ
    have e1 : (p - c) * ((v - p) / μ) * μ = (p - c) * (v - p) := by rw [mul_assoc, hy]
    rw [e1, e2]
    nlinarith [sq_nonneg (v - c - 2 * (v - p))]
  · have hG1 : G μ (v - p) = 1 := by
      unfold G
      rw [max_eq_left (div_nonneg (by linarith) hμ.le), min_eq_right ((one_le_div hμ).2 hx)]
    rw [hG1]
    refine le_of_mul_le_mul_right ?_ hμ
    rw [e2]
    nlinarith [sq_nonneg (v - c - 2 * μ), mul_nonneg (sub_nonneg.2 hx) hμ.le]

lemma baseline_ge (v c μ P : ℝ) (hvc : c < v) (hμ : 0 < μ) (h2 : v - c ≤ 2 * μ)
    (h : IsBaselineValue v c μ P) : (v - c) - (v - c) ^ 2 / (2 * μ) ≤ P := by
  obtain ⟨f, pd, ⟨hf, hS, hmax⟩, rfl⟩ := h
  have h1 := hmax (v - c) (v - (v - c) / 2) le_rfl (sopt_mid v c μ hvc hμ h2)
  unfold MProfit at h1
  rw [show v - (v - (v - c) / 2) = (v - c) / 2 by ring,
    G_mid μ ((v - c) / 2) hμ (by linarith) (by linarith)] at h1
  have hμ' : μ ≠ 0 := hμ.ne'
  have e : (v - c) * (1 - (v - c) / 2 / μ) = (v - c) - (v - c) ^ 2 / (2 * μ) := by
    field_simp
  rw [e] at h1
  exact h1

theorem main (v c : ℝ) (hvc : c < v) :
    -- (i) ban for every η > Π*/(v − c), η ≤ 1
    (∀ q PiStar η : ℝ, 0 < q → q < 1 → 0 < PiStar → PiStar < v - c →
      PiStar / (v - c) < η → η ≤ 1 → PrefersBan v c q η PiStar) ∧
    -- (ii) if q > c/(v − Π*): η_L ∈ [0, 1) with Π_L(η_L) = qΠ* exists and is unique ...
    (∀ q PiStar : ℝ, 0 < q → q < 1 → 0 < PiStar → PiStar < v - c → c / (v - PiStar) < q →
      ∃! ηL : ℝ, 0 ≤ ηL ∧ ηL < 1 ∧ PiL v c q ηL = q * PiStar) ∧
    -- ... it is positive, and the marketplace bans for every η ∈ [0, η_L)
    (∀ q PiStar ηL η : ℝ, 0 < q → q < 1 → 0 < PiStar → PiStar < v - c →
      c / (v - PiStar) < q → 0 ≤ ηL → ηL < 1 → PiL v c q ηL = q * PiStar →
      0 < ηL ∧ (0 ≤ η → η < ηL → PrefersBan v c q η PiStar)) ∧
    -- (iii) for q close enough to one, ban for every η ∈ [0, 1]
    (∀ PiStar : ℝ, 0 < PiStar → PiStar < v - c →
      ∃ q₀ < 1, ∀ q η : ℝ, q₀ < q → q < 1 → 0 ≤ η → η ≤ 1 → PrefersBan v c q η PiStar) ∧
    -- (iv) uniform MarketplaceLeakage.Baseline.G, for each fixed η ∈ (0, 1), with the disclosed addition c ≥ 0
    (0 ≤ c → ∀ q η : ℝ, 0 < q → q < 1 → 0 < η → η < 1 →
      (∃ μ₀ > 0, ∀ μ P : ℝ, 0 < μ → μ < μ₀ → IsBaselineValue v c μ P → PrefersBan v c q η P) ∧
      (∃ μ₁ : ℝ, ∀ μ P : ℝ, μ₁ < μ → IsBaselineValue v c μ P → PrefersAllow v c q η P)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (i)
    intro q PiStar η hq0 hq1 hP0 hP1 hη hη1
    have hvc' : 0 < v - c := by linarith
    have hη' : PiStar < η * (v - c) := (div_lt_iff₀ hvc').1 hη
    have hη0 : 0 ≤ η := by
      by_contra hcon; push_neg at hcon; nlinarith
    apply prefersBan_of v c q η PiStar (v - c) hvc hq0 hη0 hη1
    have := banRev_vc v c q η hvc hq0.le hη0 hη1
    nlinarith [mul_pos hq0 (sub_pos.2 hη')]
  · -- (ii) existence and uniqueness
    intro q PiStar hq0 hq1 hP0 hP1 hcq
    obtain ⟨hv, h0⟩ := cond_ii v c q PiStar hq0 hq1 hP0 hP1 hcq
    have hγ : 0 < q ^ 2 * (1 - q) * v := mul_pos (mul_pos (pow_pos hq0 2) (by linarith)) hv
    obtain ⟨t, ht0, ht1, htL⟩ := small_t (q * (q * v * (2 - q) - c) - q * (1 - q) ^ 2 * v)
      ((1 - q) * (q * v * (2 - q) - c)) (q ^ 2 * (1 - q) * v) (q * PiStar) hγ
    have hPt : PiL v c q (1 - t) < q * PiStar := by
      have := PiL_t v c q (1 - t) (by linarith)
      rw [sub_sub_cancel] at this
      rw [this]; exact htL
    have hcont : ContinuousOn (fun η => PiL v c q η) (Set.Icc 0 (1 - t)) := by
      unfold PiL
      apply ContinuousOn.mul (by fun_prop)
      apply ContinuousOn.sub _ continuousOn_const
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro x hx
      exact ne_of_gt (by linarith [hx.2])
    have hP0' : q * PiStar < PiL v c q 0 := by rw [PiL_zero]; exact h0
    obtain ⟨η, hη, hηL⟩ := intermediate_value_Icc' (by linarith : (0:ℝ) ≤ 1 - t) hcont
      ⟨le_of_lt hPt, le_of_lt hP0'⟩
    have hηL' : PiL v c q η = q * PiStar := hηL
    have hη1 : η < 1 := by linarith [hη.2]
    refine ⟨η, ⟨hη.1, hη1, hηL'⟩, ?_⟩
    rintro y ⟨hy0, hy1, hyL⟩
    rcases lt_trichotomy y η with h | h | h
    · exfalso
      have := PiL_above v c q y η (q * PiStar) hv hq0 hq1 hy0 h hη1 h0 hηL'
      linarith
    · exact h
    · exfalso
      have := PiL_above v c q η y (q * PiStar) hv hq0 hq1 hη.1 h hy1 h0 hyL
      linarith
  · -- (ii) positivity and ban below η_L
    intro q PiStar ηL η hq0 hq1 hP0 hP1 hcq hL0 hL1 hLe
    obtain ⟨hv, h0⟩ := cond_ii v c q PiStar hq0 hq1 hP0 hP1 hcq
    refine ⟨?_, fun hη0 hηlt => ?_⟩
    · rcases lt_or_eq_of_le hL0 with h | h
      · exact h
      · exfalso
        rw [← h, PiL_zero] at hLe
        linarith
    · have hab := PiL_above v c q η ηL (q * PiStar) hv hq0 hq1 hη0 hηlt hL1 h0 hLe
      apply prefersBan_of v c q η PiStar (fhat v c q η) hvc hq0 hη0 (by linarith)
      rw [banRev_fhat v c q η hv.le hq0 hq1 hη0 (by linarith), fhat_mulA v c q η (by linarith)]
      exact hab
  · -- (iii)
    intro PiStar hP0 hP1
    by_cases hv : 0 < v
    · have hD : 0 < v - c - PiStar := by linarith
      have hvc' : 0 < v - c := by linarith
      have hr : 0 < (v - c - PiStar) ^ 2 / (v * (v - c)) :=
        div_pos (pow_pos hD 2) (mul_pos hv hvc')
      refine ⟨max (1/2) (1 - (v - c - PiStar) ^ 2 / (v * (v - c))),
        max_lt (by norm_num) (by linarith), ?_⟩
      intro q η hq hq1 hη0 hη1
      have hq0 : 0 < q := by
        have := le_max_left (1/2:ℝ) (1 - (v - c - PiStar) ^ 2 / (v * (v - c))); linarith
      have hq' : (1 - q) * (v * (v - c)) < (v - c - PiStar) ^ 2 := by
        have h2 : 1 - (v - c - PiStar) ^ 2 / (v * (v - c)) < q :=
          lt_of_le_of_lt (le_max_right _ _) hq
        have h3 : 1 - q < (v - c - PiStar) ^ 2 / (v * (v - c)) := by linarith
        rwa [lt_div_iff₀ (mul_pos hv hvc')] at h3
      by_cases hη : PiStar < η * (v - c)
      · apply prefersBan_of v c q η PiStar (v - c) hvc hq0 hη0 hη1
        have := banRev_vc v c q η hvc hq0.le hη0 hη1
        nlinarith [mul_pos hq0 (sub_pos.2 hη)]
      · push_neg at hη
        have hηlt : η < 1 := by
          by_contra hcon; push_neg at hcon
          nlinarith
        apply prefersBan_of v c q η PiStar (fhat v c q η) hvc hq0 hη0 hη1
        rw [banRev_fhat v c q η hv.le hq0 hq1 hη0 hηlt]
        have hfm := fhat_mul v c q η hηlt
        have h4 : (v - c - PiStar) ≤ (1 - η) * (v - c) := by linarith
        have h5 : (1 - q) * v < (1 - η) * (v - c - PiStar) := by
          have : (1 - q) * v * (v - c) < (1 - η) * (v - c - PiStar) * (v - c) := by
            nlinarith [mul_le_mul_of_nonneg_left h4 hD.le]
          exact lt_of_mul_lt_mul_right this hvc'.le
        have h6 : PiStar * (1 - η) < (1 - η) * fhat v c q η := by
          rw [hfm]
          have : 0 ≤ (1 - q) * v * (η * (1 - q)) :=
            mul_nonneg (mul_nonneg (by linarith) hv.le) (mul_nonneg hη0 (by linarith))
          nlinarith
        have hfp : PiStar < fhat v c q η := by
          have : (1 - η) * PiStar < (1 - η) * fhat v c q η := by linarith
          exact lt_of_mul_lt_mul_left this (by linarith)
        have hAq : q ≤ 1 - η + η * q := by
          nlinarith [mul_nonneg (sub_nonneg.2 hη1) (sub_nonneg.2 hq1.le)]
        nlinarith [mul_le_mul_of_nonneg_left hAq (by linarith : (0:ℝ) ≤ fhat v c q η),
          mul_lt_mul_of_pos_right hfp hq0]
    · push_neg at hv
      refine ⟨1/2, by norm_num, ?_⟩
      intro q η hq hq1 hη0 hη1
      have hq0 : 0 < q := by linarith
      have hA : q ≤ 1 - η + η * q := by
        nlinarith [mul_nonneg (sub_nonneg.2 hη1) (sub_nonneg.2 hq1.le)]
      apply prefersBan_of v c q η PiStar (q * v - c) hvc hq0 hη0 hη1
      have hn : ¬ lowPay v c q η (q * v - c) < highPay v c q η (q * v - c) := by
        rw [not_lt]
        show η * q * (v - c - (q * v - c)) ≤ (1 - η + η * q) * (q * v - c - (q * v - c))
        have : 0 ≤ η * q * ((1 - q) * (-v)) :=
          mul_nonneg (mul_nonneg hη0 hq0.le) (mul_nonneg (by linarith) (by linarith))
        nlinarith
      have hp : 0 ≤ lowPay v c q η (q * v - c) := by
        show 0 ≤ (1 - η + η * q) * (q * v - c - (q * v - c))
        simp
      have hb : banRev v c q η (q * v - c) = (q * v - c) * (1 - η + η * q) := by
        unfold banRev; rw [if_neg hn, if_pos hp]
      rw [hb]
      have h1 : PiStar < q * v - c := by
        nlinarith [mul_nonneg (sub_nonneg.2 hq1.le) (by linarith : (0:ℝ) ≤ -v)]
      nlinarith [mul_le_mul_of_nonneg_left hA (by linarith : (0:ℝ) ≤ q * v - c),
        mul_lt_mul_of_pos_right h1 hq0]
  · -- (iv)
    intro hc0 q η hq0 hq1 hη0 hη1
    have hv : 0 < v := by linarith
    have hvc' : 0 < v - c := by linarith
    constructor
    · refine ⟨η * (v - c), mul_pos hη0 hvc', ?_⟩
      intro μ P hμ hμ0 hP
      have hPle := baseline_le v c μ P hμ hP
      apply prefersBan_of v c q η P (v - c) hvc hq0 hη0.le hη1.le
      have := banRev_vc v c q η hvc hq0.le hη0.le hη1.le
      nlinarith [mul_le_mul_of_nonneg_left hPle hq0.le, mul_lt_mul_of_pos_left hμ0 hq0]
    · have hfm := fhat_mul v c q η hη1
      have hA0 : 0 < 1 - η + η * q := by nlinarith
      have hA1 : 1 - η + η * q < 1 := by nlinarith [mul_pos hη0 (sub_pos.2 hq1)]
      have hfl : fhat v c q η < q * v - c := by
        have : 0 < η * q * ((1 - q) * v) := mul_pos (mul_pos hη0 hq0) (mul_pos (by linarith) hv)
        have h' : (1 - η) * fhat v c q η < (1 - η) * (q * v - c) := by nlinarith
        exact lt_of_mul_lt_mul_left h' (by linarith)
      have hPiL : PiL v c q η < q * (v - c) := by
        rw [← fhat_mulA v c q η hη1]
        rcases le_or_gt (fhat v c q η) 0 with h | h
        · nlinarith [mul_nonpos_iff.2 (Or.inr ⟨h, hA0.le⟩), mul_pos hq0 hvc']
        · nlinarith [mul_lt_mul_of_pos_left hA1 h, mul_nonneg hq0.le hc0]
      obtain ⟨M, hM⟩ : ∃ M, M = max (η * q * (v - c)) (PiL v c q η) := ⟨_, rfl⟩
      have hM1 : η * q * (v - c) ≤ M := by rw [hM]; exact le_max_left _ _
      have hM2 : PiL v c q η ≤ M := by rw [hM]; exact le_max_right _ _
      have hMlt : M < q * (v - c) := by
        rw [hM]
        exact max_lt (by nlinarith [mul_lt_mul_of_pos_right hη1 (mul_pos hq0 hvc')]) hPiL
      have hbound : ∀ f, banRev v c q η f ≤ M := by
        intro f
        apply banRev_le
        · exact le_trans (mul_nonneg (mul_nonneg hη0.le hq0.le) hvc'.le) hM1
        · exact le_trans (le_of_eq (by ring)) hM1
        · intro g h1 h2
          have hd := low_sub_high v c q η g
          push_neg at h1
          have hg : g ≤ fhat v c q η := by
            have : (1 - η) * g ≤ (1 - η) * fhat v c q η := by linarith
            exact le_of_mul_le_mul_left this (by linarith)
          calc g * (1 - η + η * q) ≤ fhat v c q η * (1 - η + η * q) :=
                mul_le_mul_of_nonneg_right hg hA0.le
            _ = PiL v c q η := fhat_mulA v c q η hη1
            _ ≤ M := hM2
      obtain ⟨ε, hε⟩ : ∃ ε, ε = q * (v - c) - M := ⟨_, rfl⟩
      have hε0 : 0 < ε := by linarith
      refine ⟨max (v - c) (q * (v - c) ^ 2 / (2 * ε)), ?_⟩
      intro μ P hμ hP
      have hμ1 : v - c < μ := lt_of_le_of_lt (le_max_left _ _) hμ
      have hμ2 : q * (v - c) ^ 2 / (2 * ε) < μ := lt_of_le_of_lt (le_max_right _ _) hμ
      have hμ0 : 0 < μ := by linarith
      have hPge := baseline_ge v c μ P hvc hμ0 (by linarith) hP
      obtain ⟨V, hV⟩ := exists_banValue v c q η hvc hq0 hη0.le hη1.le
      refine ⟨V, hV, ?_⟩
      obtain ⟨f0, hf0⟩ := hV.1
      have hVM : V ≤ M := by rw [← hf0]; exact hbound f0
      have h7 : q * (v - c) ^ 2 < μ * (2 * ε) := by
        rwa [div_lt_iff₀ (by linarith)] at hμ2
      have h8 : q * ((v - c) ^ 2 / (2 * μ)) < ε := by
        rw [← mul_div_assoc, div_lt_iff₀ (by linarith)]; linarith
      nlinarith [mul_le_mul_of_nonneg_left hPge hq0.le]

end MLP3Aux

open MarketplaceLeakage.Communication in
theorem solution (v c : ℝ) (hvc : c < v) :
    -- (i) ban for every η > Π*/(v − c), η ≤ 1
    (∀ q PiStar η : ℝ, 0 < q → q < 1 → 0 < PiStar → PiStar < v - c →
      PiStar / (v - c) < η → η ≤ 1 → PrefersBan v c q η PiStar) ∧
    -- (ii) if q > c/(v − Π*): η_L ∈ [0, 1) with Π_L(η_L) = qΠ* exists and is unique ...
    (∀ q PiStar : ℝ, 0 < q → q < 1 → 0 < PiStar → PiStar < v - c → c / (v - PiStar) < q →
      ∃! ηL : ℝ, 0 ≤ ηL ∧ ηL < 1 ∧ PiL v c q ηL = q * PiStar) ∧
    -- ... it is positive, and the marketplace bans for every η ∈ [0, η_L)
    (∀ q PiStar ηL η : ℝ, 0 < q → q < 1 → 0 < PiStar → PiStar < v - c →
      c / (v - PiStar) < q → 0 ≤ ηL → ηL < 1 → PiL v c q ηL = q * PiStar →
      0 < ηL ∧ (0 ≤ η → η < ηL → PrefersBan v c q η PiStar)) ∧
    -- (iii) for q close enough to one, ban for every η ∈ [0, 1]
    (∀ PiStar : ℝ, 0 < PiStar → PiStar < v - c →
      ∃ q₀ < 1, ∀ q η : ℝ, q₀ < q → q < 1 → 0 ≤ η → η ≤ 1 → PrefersBan v c q η PiStar) ∧
    -- (iv) uniform MarketplaceLeakage.Baseline.G, for each fixed η ∈ (0, 1), with the disclosed addition c ≥ 0
    (0 ≤ c → ∀ q η : ℝ, 0 < q → q < 1 → 0 < η → η < 1 →
      (∃ μ₀ > 0, ∀ μ P : ℝ, 0 < μ → μ < μ₀ → IsBaselineValue v c μ P → PrefersBan v c q η P) ∧
      (∃ μ₁ : ℝ, ∀ μ P : ℝ, μ₁ < μ → IsBaselineValue v c μ P → PrefersAllow v c q η P)) := by
  exact MLP3Aux.main v c hvc
