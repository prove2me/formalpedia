-- Prove2me | solution 1 for LoanInsurance.Liquid.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T14:36:42.391066+00:00
-- url     : https://prove2.me/submissions/b219d481-7201-4b2c-8f9d-0db6f8edbf81

import Mathlib
import Definitions.Def_LoanInsurance_Liquid_Model

set_option autoImplicit false

namespace LoanInsurance.Liquid.Prop2Aux

lemma quad (μ ν l : ℝ) (hμ : 0 < μ) (hν : 0 < ν) (hμ1 : μ < 1) (hν1 : ν < 1)
    (h : 1 / (2 * μ) + Real.sqrt (1 / (4 * μ ^ 2) + (1 - μ) * (1 - ν) / (μ * ν)) ≤ l) :
    ν * l + (1 - ν) * (1 - μ) ≤ ν * μ * l ^ 2 := by
  have harg : 0 ≤ 1 / (4 * μ ^ 2) + (1 - μ) * (1 - ν) / (μ * ν) :=
    add_nonneg (by positivity)
      (div_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_pos hμ hν).le)
  have hs0 := Real.sqrt_nonneg (1 / (4 * μ ^ 2) + (1 - μ) * (1 - ν) / (μ * ν))
  have hss := Real.sq_sqrt harg
  have h2 : Real.sqrt (1 / (4 * μ ^ 2) + (1 - μ) * (1 - ν) / (μ * ν)) ≤ l - 1 / (2 * μ) := by
    linarith
  have h3 := pow_le_pow_left₀ hs0 h2 2
  rw [hss] at h3
  have hμ0 : μ ≠ 0 := hμ.ne'
  have e1 : (l - 1 / (2 * μ)) ^ 2 = l ^ 2 - l / μ + 1 / (4 * μ ^ 2) := by
    field_simp
    ring
  rw [e1] at h3
  have h4 : (1 - μ) * (1 - ν) / (μ * ν) ≤ l ^ 2 - l / μ := by linarith
  rw [div_le_iff₀ (mul_pos hμ hν)] at h4
  have e2 : (l ^ 2 - l / μ) * (μ * ν) = ν * μ * l ^ 2 - ν * l := by
    field_simp
  rw [e2] at h4
  linarith

lemma d0_pos (μ ψ ν f : ℝ) (hν : 0 < ν) (hν1 : ν < 1) (hμ1 : μ < 1) (hψ1 : ψ < 1)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    0 < ν + (1 - ν) * ((1 - ψ) * f + (1 - μ) * (1 - f)) := by
  have h1 : 0 ≤ (1 - ψ) * f + (1 - μ) * (1 - f) :=
    add_nonneg (mul_nonneg (by linarith) hf0) (mul_nonneg (by linarith) (by linarith))
  have h2 := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - ν) h1
  linarith

lemma dp_pos (μ ν l : ℝ) (hν : 0 < ν) (hν1 : ν < 1) (hμ1 : μ < 1) (hl : 1 < l) :
    0 < ν * l + (1 - ν) * (1 - μ) := by
  have h1 := mul_pos hν (by linarith : (0:ℝ) < l)
  have h2 := mul_pos (by linarith : (0:ℝ) < 1 - ν) (by linarith : (0:ℝ) < 1 - μ)
  linarith

lemma ident (A μ ψ ν l f : ℝ) :
    ν * l * μ * A * (ν + (1 - ν) * ((1 - ψ) * f + (1 - μ) * (1 - f))) -
      ν * A * (ψ * f + μ * (1 - f)) * (ν * l + (1 - ν) * (1 - μ)) =
    A * (ν * (μ * (l - 1) * (1 - ν) * (1 - μ) * (1 - f) -
      ((ν * l + 1 - ν) * (1 - μ) * ψ - (1 - ψ) * l * μ) * f)) := by
  ring

lemma cond_imp (μ ψ ν l f : ℝ) (hν : 0 < ν) (hν1 : ν < 1) (hμ1 : μ < 1) (hψ1 : ψ < 1)
    (hl : 1 < l) (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (h : ν * (ψ * f + μ * (1 - f)) / (ν + (1 - ν) * ((1 - ψ) * f + (1 - μ) * (1 - f))) <
      ν * l * μ / (ν * l + (1 - ν) * (1 - μ))) :
    ((ν * l + 1 - ν) * (1 - μ) * ψ - (1 - ψ) * l * μ) * f <
      μ * (l - 1) * (1 - ν) * (1 - μ) * (1 - f) := by
  have hD0 := d0_pos μ ψ ν f hν hν1 hμ1 hψ1 hf0 hf1
  have hDp := dp_pos μ ν l hν hν1 hμ1 hl
  rw [div_lt_div_iff₀ hD0 hDp] at h
  have hi := ident 1 μ ψ ν l f
  by_contra hc0
  have hc := not_lt.1 hc0
  have h3 := mul_nonneg hν.le (sub_nonneg.2 hc)
  nlinarith

lemma price_lt (A μ ψ ν l f : ℝ) (hA : 0 < A) (hν : 0 < ν) (hν1 : ν < 1) (hμ1 : μ < 1)
    (hψ1 : ψ < 1) (hl : 1 < l) (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (h : ((ν * l + 1 - ν) * (1 - μ) * ψ - (1 - ψ) * l * μ) * f <
      μ * (l - 1) * (1 - ν) * (1 - μ) * (1 - f)) :
    ν * A * (ψ * f + μ * (1 - f)) / (ν + (1 - ν) * ((1 - ψ) * f + (1 - μ) * (1 - f))) <
      ν * l * μ * A / (ν * l + (1 - ν) * (1 - μ)) := by
  have hD0 := d0_pos μ ψ ν f hν hν1 hμ1 hψ1 hf0 hf1
  have hDp := dp_pos μ ν l hν hν1 hμ1 hl
  rw [div_lt_div_iff₀ hD0 hDp]
  have hi := ident A μ ψ ν l f
  have h1 := mul_pos hA (mul_pos hν (sub_pos.2 h))
  linarith

end LoanInsurance.Liquid.Prop2Aux

open LoanInsurance.Liquid in
theorem solution (P : Params) (hP : P.Standing) (hψ : P.psiUnder < P.ψ)
    (hlam : P.lamTildeL ≤ P.lam) (h35 : P.Cond35) :
    (∃ e : Profile, P.LiquidEq e ∧ 0 < e.m ∧ e.m < 1 ∧ e.mL = 0 ∧
        e.eta = P.etaStar ∧ e.pU = P.pUStar ∧ e.m = P.mStar ∧
        e.k = (1 - P.μ) * P.A ∧ e.pI = P.μ * P.A) ∧
      P.A / P.lam ≤ P.pUStar ∧ P.pUStar < P.μ * P.A ∧
      ∀ η₀ p₀ : ℝ, P.BenchmarkFP η₀ p₀ → p₀ < P.pUStar ∧ P.etaStar < η₀ := by
  obtain ⟨hA, hμ, hμψ, hψ1, hν, hν1, hl, hEb, hF0, hF1, hmono, -, -, hFtop⟩ := hP
  have hμ1 : P.μ < 1 := hμψ.trans hψ1
  have hl0 : 0 < P.lam := by linarith
  have hDpe : P.Dp = P.ν * P.lam + (1 - P.ν) * (1 - P.μ) := rfl
  have hκe : P.kappa = P.ν * P.lam + 1 - P.ν := rfl
  have hpUe : P.pUStar = P.ν * P.lam * P.μ * P.A / (P.ν * P.lam + (1 - P.ν) * (1 - P.μ)) := rfl
  have hκ : 0 < P.kappa := by
    rw [hκe]
    have := mul_pos hν hl0
    linarith
  have hDp' : 0 < P.ν * P.lam + (1 - P.ν) * (1 - P.μ) :=
    Prop2Aux.dp_pos P.μ P.ν P.lam hν hν1 hμ1 hl
  have hDp : 0 < P.Dp := hDp'
  have hC : 0 < P.μ * (P.lam - 1) * (1 - P.ν) * (1 - P.μ) :=
    mul_pos (mul_pos (mul_pos hμ (sub_pos.2 hl)) (sub_pos.2 hν1)) (sub_pos.2 hμ1)
  have hG : 0 < P.kappa * (1 - P.μ) * P.ψ - (1 - P.ψ) * P.lam * P.μ := by
    unfold Params.psiUnder at hψ
    have hden : 0 < P.lam * P.μ + P.kappa * (1 - P.μ) := by
      have := mul_pos hl0 hμ
      have := mul_pos hκ (sub_pos.2 hμ1)
      linarith
    rw [div_lt_iff₀ hden] at hψ
    linarith
  -- the screening threshold
  have hη0 : 0 < P.etaStar := by
    unfold Params.etaStar
    exact div_pos (mul_pos (mul_pos (mul_pos (mul_pos (sub_pos.2 hν1) (sub_pos.2 hμ1))
      (sub_pos.2 hμψ)) hκ) hA) hDp
  have hFr : ∀ x, 0 ≤ x → 0 ≤ P.F x ∧ P.F x ≤ 1 := by
    intro x hx
    rcases le_or_gt x P.etaBar with h | h
    · have m0 := hmono.monotoneOn ⟨le_refl 0, hEb.le⟩ ⟨hx, h⟩ hx
      have m1 := hmono.monotoneOn ⟨hx, h⟩ ⟨hEb.le, le_refl _⟩ h
      rw [hF0] at m0
      rw [hF1] at m1
      exact ⟨m0, m1⟩
    · rw [hFtop x h.le]
      exact ⟨zero_le_one, le_refl 1⟩
  obtain ⟨hf0, hf1⟩ := hFr _ hη0.le
  have hcond : (P.kappa * (1 - P.μ) * P.ψ - (1 - P.ψ) * P.lam * P.μ) * P.F P.etaStar <
      P.μ * (P.lam - 1) * (1 - P.ν) * (1 - P.μ) * (1 - P.F P.etaStar) :=
    Prop2Aux.cond_imp P.μ P.ψ P.ν P.lam (P.F P.etaStar) hν hν1 hμ1 hψ1 hl hf0 hf1 h35
  have hflt : P.F P.etaStar < 1 := by
    rcases lt_or_eq_of_le hf1 with h | h
    · exact h
    · rw [h, sub_self, mul_zero, mul_one] at hcond
      linarith
  have hηlt : P.etaStar < P.etaBar := by
    by_contra hc0
    have hc := not_lt.1 hc0
    rw [hFtop _ hc] at hflt
    exact lt_irrefl _ hflt
  have hfpos : 0 < P.F P.etaStar := by
    have := hmono ⟨le_refl 0, hEb.le⟩ ⟨hη0.le, hηlt.le⟩ hη0
    rwa [hF0] at this
  -- the insured share
  have hden : 0 < P.μ * (P.lam - 1) * (1 - P.ν) * (1 - P.μ) * (1 - P.F P.etaStar) :=
    mul_pos hC (sub_pos.2 hflt)
  have hq0 : 0 < (P.kappa * (1 - P.μ) * P.ψ - (1 - P.ψ) * P.lam * P.μ) * P.F P.etaStar /
      (P.μ * (P.lam - 1) * (1 - P.ν) * (1 - P.μ) * (1 - P.F P.etaStar)) :=
    div_pos (mul_pos hG hfpos) hden
  have hq1 : (P.kappa * (1 - P.μ) * P.ψ - (1 - P.ψ) * P.lam * P.μ) * P.F P.etaStar /
      (P.μ * (P.lam - 1) * (1 - P.ν) * (1 - P.μ) * (1 - P.F P.etaStar)) < 1 :=
    (div_lt_one hden).2 hcond
  have hm0 : 0 < P.mStar := by
    unfold Params.mStar
    linarith
  have hm1 : P.mStar < 1 := by
    unfold Params.mStar
    linarith
  have hx : (1 - P.F P.etaStar) * (1 - P.mStar) * (P.μ * (P.lam - 1) * (1 - P.ν) * (1 - P.μ)) =
      (P.kappa * (1 - P.μ) * P.ψ - (1 - P.ψ) * P.lam * P.μ) * P.F P.etaStar := by
    unfold Params.mStar
    rw [sub_sub_cancel]
    calc (1 - P.F P.etaStar) *
          ((P.kappa * (1 - P.μ) * P.ψ - (1 - P.ψ) * P.lam * P.μ) * P.F P.etaStar /
            (P.μ * (P.lam - 1) * (1 - P.ν) * (1 - P.μ) * (1 - P.F P.etaStar))) *
          (P.μ * (P.lam - 1) * (1 - P.ν) * (1 - P.μ))
        = (P.kappa * (1 - P.μ) * P.ψ - (1 - P.ψ) * P.lam * P.μ) * P.F P.etaStar /
            (P.μ * (P.lam - 1) * (1 - P.ν) * (1 - P.μ) * (1 - P.F P.etaStar)) *
            (P.μ * (P.lam - 1) * (1 - P.ν) * (1 - P.μ) * (1 - P.F P.etaStar)) := by ring
      _ = (P.kappa * (1 - P.μ) * P.ψ - (1 - P.ψ) * P.lam * P.μ) * P.F P.etaStar :=
          div_mul_cancel₀ _ hden.ne'
  rw [hκe] at hx
  -- the uninsured price
  have hpU' : P.pUStar * (P.ν * P.lam + (1 - P.ν) * (1 - P.μ)) = P.ν * P.lam * P.μ * P.A := by
    rw [hpUe]
    field_simp
  have hpUpos : 0 < P.pUStar := by
    rw [hpUe]
    exact div_pos (mul_pos (mul_pos (mul_pos hν hl0) hμ) hA) hDp'
  have hquad := Prop2Aux.quad P.μ P.ν P.lam hμ hν hμ1 hν1 hlam
  have hliq : P.A ≤ P.lam * P.pUStar := by
    by_contra hc0
    have hc := not_le.1 hc0
    have h1 := mul_lt_mul_of_pos_right hc hDp'
    have h2 := mul_le_mul_of_nonneg_left hquad hA.le
    have e : P.lam * P.pUStar * (P.ν * P.lam + (1 - P.ν) * (1 - P.μ)) =
        P.lam * (P.ν * P.lam * P.μ * P.A) := by
      rw [mul_assoc, hpU']
    linarith
  have hpUlt : P.pUStar < P.μ * P.A := by
    by_contra hc0
    have hc := not_lt.1 hc0
    have h1 := mul_le_mul_of_nonneg_right hc hDp'.le
    have h2 := mul_pos (mul_pos hμ hA) (mul_pos (sub_pos.2 hν1) (sub_pos.2 hμ1))
    linarith [hpU']
  have hμA : P.μ * P.A < P.A := by
    have := mul_lt_mul_of_pos_right hμ1 hA
    linarith
  have hpUltA : P.pUStar < P.A := hpUlt.trans hμA
  -- valuations
  have hvU : ∀ q, P.valUninsured P.pUStar q =
      P.ν * (P.lam * P.pUStar) + (1 - P.ν) * (q * P.A + (1 - q) * P.pUStar) := by
    intro q
    unfold Params.valUninsured
    rw [max_eq_left hliq, max_eq_left (by linarith : (0:ℝ) ≤ P.lam * P.pUStar),
      max_eq_right hpUltA.le, max_eq_left hpUpos.le]
    ring
  have hvI : P.valInsured (P.μ * P.A) (P.A - (1 - P.μ) * P.A) =
      P.ν * (P.lam * (P.μ * P.A)) + (1 - P.ν) * (P.μ * P.A) := by
    unfold Params.valInsured
    have e : P.A - (1 - P.μ) * P.A = P.μ * P.A := by ring
    have hle : P.μ * P.A ≤ P.lam * (P.μ * P.A) := by
      have := mul_pos hμ hA
      nlinarith
    rw [e, max_eq_left hle, max_self]
  have hthr : (1 - P.ν) * (P.ψ - P.μ) * (P.A - P.pUStar) = P.etaStar := by
    unfold Params.etaStar
    rw [eq_div_iff hDp.ne', hDpe, hκe]
    linear_combination (-(1 - P.ν) * (P.ψ - P.μ)) * hpU'
  have hind : P.ν * (P.lam * P.pUStar) + (1 - P.ν) * (P.μ * P.A + (1 - P.μ) * P.pUStar) =
      P.ν * (P.lam * (P.μ * P.A)) + (1 - P.ν) * (P.μ * P.A) := by
    linear_combination hpU'
  -- the four payoffs
  have pTF : ∀ η, P.payoff (P.μ * P.A) P.pUStar ((1 - P.μ) * P.A) η true false =
      P.ν * (P.lam * P.pUStar) + (1 - P.ν) * (P.ψ * P.A + (1 - P.ψ) * P.pUStar) - η := by
    intro η
    have : P.payoff (P.μ * P.A) P.pUStar ((1 - P.μ) * P.A) η true false =
        P.valUninsured P.pUStar P.ψ - η := rfl
    rw [this, hvU]
  have pFF : ∀ η, P.payoff (P.μ * P.A) P.pUStar ((1 - P.μ) * P.A) η false false =
      P.ν * (P.lam * P.pUStar) + (1 - P.ν) * (P.μ * P.A + (1 - P.μ) * P.pUStar) - 0 := by
    intro η
    have : P.payoff (P.μ * P.A) P.pUStar ((1 - P.μ) * P.A) η false false =
        P.valUninsured P.pUStar P.μ - 0 := rfl
    rw [this, hvU]
  have pTT : ∀ η, P.payoff (P.μ * P.A) P.pUStar ((1 - P.μ) * P.A) η true true =
      P.ν * (P.lam * (P.μ * P.A)) + (1 - P.ν) * (P.μ * P.A) - η := by
    intro η
    have : P.payoff (P.μ * P.A) P.pUStar ((1 - P.μ) * P.A) η true true =
        P.valInsured (P.μ * P.A) (P.A - (1 - P.μ) * P.A) - η := rfl
    rw [this, hvI]
  have pFT : ∀ η, P.payoff (P.μ * P.A) P.pUStar ((1 - P.μ) * P.A) η false true =
      P.ν * (P.lam * (P.μ * P.A)) + (1 - P.ν) * (P.μ * P.A) - 0 := by
    intro η
    have : P.payoff (P.μ * P.A) P.pUStar ((1 - P.μ) * P.A) η false true =
        P.valInsured (P.μ * P.A) (P.A - (1 - P.μ) * P.A) - 0 := rfl
    rw [this, hvI]
  have hBRlow : ∀ η, 0 ≤ η → η ≤ P.etaStar →
      P.BestResponse (P.μ * P.A) P.pUStar ((1 - P.μ) * P.A) η true false := by
    intro η h0 h1 s' ℓ'
    cases s' <;> cases ℓ'
    · rw [pFF, pTF]; linarith
    · rw [pFT, pTF]; linarith
    · rw [pTF]
    · rw [pTT, pTF]; linarith
  have hBRhigh : ∀ η, P.etaStar < η → ∀ ℓ : Bool,
      P.BestResponse (P.μ * P.A) P.pUStar ((1 - P.μ) * P.A) η false ℓ := by
    intro η h0 ℓ s' ℓ'
    cases ℓ <;> cases s' <;> cases ℓ'
    all_goals (simp only [pFF, pFT, pTF, pTT]; try linarith)
  refine ⟨⟨⟨P.etaStar, 0, P.mStar, P.μ * P.A, P.pUStar, (1 - P.μ) * P.A⟩, ?_, hm0, hm1,
    rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, hpUlt, ?_⟩
  · unfold Params.LiquidEq
    dsimp only
    refine ⟨hη0.le, hηlt.le, le_refl 0, zero_le_one, hm0.le, hm1.le, ?_, ?_, ?_, ?_, ?_, hliq⟩
    · intro η hη
      exact ⟨fun _ => hBRlow η hη.1 hη.2, fun h => absurd h (lt_irrefl 0)⟩
    · intro η hη
      exact ⟨fun _ => hBRhigh η hη.1 false, fun _ => hBRhigh η hη.1 true⟩
    · ring
    · ring
    · rw [hpUe, div_mul_eq_mul_div, div_eq_iff hDp'.ne']
      linear_combination (P.ν * P.A) * hx
  · rw [div_le_iff₀ hl0]
    linarith
  · intro η₀ p₀ hB
    unfold Params.BenchmarkFP at hB
    obtain ⟨h0, h1, hp, hη⟩ := hB
    have hlt : p₀ < P.pUStar := by
      by_contra hc0
      have hc := not_lt.1 hc0
      have hle : η₀ ≤ P.etaStar := by
        rw [hη, ← hthr]
        exact mul_le_mul_of_nonneg_left (by linarith)
          (mul_nonneg (sub_pos.2 hν1).le (sub_pos.2 hμψ).le)
      have hFle : P.F η₀ ≤ P.F P.etaStar := hmono.monotoneOn ⟨h0, h1⟩ ⟨hη0.le, hηlt.le⟩ hle
      obtain ⟨g0, g1⟩ := hFr η₀ h0
      have a1 := mul_le_mul_of_nonneg_left hFle hG.le
      have a2 := mul_le_mul_of_nonneg_left (by linarith : 1 - P.F P.etaStar ≤ 1 - P.F η₀) hC.le
      have hc0 : (P.kappa * (1 - P.μ) * P.ψ - (1 - P.ψ) * P.lam * P.μ) * P.F η₀ <
          P.μ * (P.lam - 1) * (1 - P.ν) * (1 - P.μ) * (1 - P.F η₀) := by linarith
      have h' : P.price4 η₀ < P.pUStar :=
        Prop2Aux.price_lt P.A P.μ P.ψ P.ν P.lam (P.F η₀) hA hν hν1 hμ1 hψ1 hl g0 g1 hc0
      rw [← hp] at h'
      linarith
    refine ⟨hlt, ?_⟩
    rw [hη, ← hthr]
    exact mul_lt_mul_of_pos_left (by linarith) (mul_pos (sub_pos.2 hν1) (sub_pos.2 hμψ))
