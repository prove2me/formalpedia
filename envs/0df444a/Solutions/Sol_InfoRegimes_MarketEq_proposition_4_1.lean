-- Prove2me | solution 1 for InfoRegimes.MarketEq.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T09:57:01.966108+00:00
-- url     : https://prove2.me/submissions/1177d084-391e-429b-92f8-dbdaf86190e9

import Mathlib
import Definitions.Def_InfoRegimes_MarketEq_Model
import Theorems.Thm_AGT_brouwer_fixed_point
import Theorems.Thm_InfoRegimes_MarketEq_selfConsistent_marketEquilibrium

namespace IR41Aux

lemma key_ineq (A B u x w N : ℝ) (hu : 0 ≤ u) (hx : 0 < x) (hw : w = u + x)
    (hN : N = A + B * (u / w)) : N ^ 2 * w ≤ u * (A + B) ^ 2 + x * A ^ 2 := by
  have hw0 : 0 < w := by rw [hw]; linarith
  have hNw : N * w = A * w + B * u := by rw [hN]; field_simp
  have h1 : N ^ 2 * w = (N * w) ^ 2 / w := by field_simp
  rw [h1, div_le_iff₀ hw0, hNw]
  have e : (u * (A + B) ^ 2 + x * A ^ 2) * w - (A * w + B * u) ^ 2 = B ^ 2 * u * x := by
    rw [hw]; ring
  have : 0 ≤ B ^ 2 * u * x := by positivity
  linarith

lemma core_upper_pos (k R γ x q qU l r s u w N D b c : ℝ)
    (hk : 0 < k) (hR0 : 0 < R) (hγ : 0 < γ) (hx : 0 < x) (hq0 : 0 < q) (hl : 0 < l)
    (hs : 0 ≤ s)
    (hr : r = l * k / (γ * q)) (hu : u = r ^ 2 * s) (hw : w = u + x)
    (hD : D = l * qU + (1 - l) * q) (hDq : q ≤ D)
    (hN : N = l * qU + (1 - l) * q * (u / w))
    (hb : b = k * N / (R * D)) (hc : c = b / r) :
    b ^ 2 * s + c ^ 2 * x ≤ (k ^ 2 * s + γ ^ 2 * x * qU ^ 2) / R ^ 2 := by
  have hr0 : 0 < r := by rw [hr]; positivity
  have hD0 : 0 < D := lt_of_lt_of_le hq0 hDq
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hkey : N ^ 2 * w ≤ u * D ^ 2 + x * (l * qU) ^ 2 := by
    have := key_ineq (l * qU) ((1 - l) * q) u x w N hu0 hx hw (by rw [hN])
    rw [hD]
    exact this
  have hrq : r * (γ * q) = l * k := by rw [hr]; field_simp
  have goal' : k ^ 2 * N ^ 2 * w ≤ k ^ 2 * u * D ^ 2 + γ ^ 2 * x * qU ^ 2 * D ^ 2 * r ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hkey (sq_nonneg k)
    have h3 : q ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hq0.le hDq 2
    have h4 : 0 ≤ x * qU ^ 2 * r ^ 2 * γ ^ 2 := by positivity
    have h5 := mul_le_mul_of_nonneg_left h3 h4
    have e1 : k ^ 2 * (u * D ^ 2 + x * (l * qU) ^ 2) =
        k ^ 2 * u * D ^ 2 + x * qU ^ 2 * r ^ 2 * γ ^ 2 * q ^ 2 := by
      have : (l * k) ^ 2 = (r * (γ * q)) ^ 2 := by rw [hrq]
      linear_combination (x * qU ^ 2) * this
    have e2 : x * qU ^ 2 * r ^ 2 * γ ^ 2 * D ^ 2 = γ ^ 2 * x * qU ^ 2 * D ^ 2 * r ^ 2 := by ring
    linarith
  have eL : b ^ 2 * s + c ^ 2 * x = k ^ 2 * N ^ 2 * w / (R ^ 2 * D ^ 2 * r ^ 2) := by
    rw [hc, hb, hw, hu]; field_simp
  have eR : (k ^ 2 * s + γ ^ 2 * x * qU ^ 2) / R ^ 2 =
      (k ^ 2 * u * D ^ 2 + γ ^ 2 * x * qU ^ 2 * D ^ 2 * r ^ 2) / (R ^ 2 * D ^ 2 * r ^ 2) := by
    rw [hu]; field_simp
  rw [eL, eR]
  exact div_le_div_of_nonneg_right goal' (by positivity)

lemma c_lower_pos (k R γ q qU l r N D b c : ℝ)
    (hk : 0 < k) (hR0 : 0 < R) (hγ : 0 < γ) (hq0 : 0 < q) (hl : 0 < l)
    (hr : r = l * k / (γ * q)) (hD0 : 0 < D) (hNA : l * qU ≤ N)
    (hb : b = k * N / (R * D)) (hc : c = b / r) : γ * q * qU / (R * D) ≤ c := by
  have e : c = γ * q * (N / l) / (R * D) := by rw [hc, hb, hr]; field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [le_div_iff₀ hl]; linarith

lemma b_lower (k R N D b t : ℝ) (hk : 0 < k) (hR0 : 0 < R) (hD0 : 0 < D)
    (hb : b = k * N / (R * D)) (ht : t * D ≤ N) : k * t / R ≤ b := by
  have e : b = k / R * (N / D) := by rw [hb]; field_simp
  have e2 : k * t / R = k / R * t := by ring
  rw [e, e2]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [le_div_iff₀ hD0]; exact ht

/-- Basic facts shared by the bounds. -/
lemma basic_facts (k R γ x σ f φ l q E r ℛ qU : ℝ)
    (hk : 0 < k) (hγ : 0 < γ) (hx : 0 < x) (hσ : 0 < σ)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hE : 0 < E)
    (hq : q = k ^ 2 * (1 - f) * σ + E)
    (hℛ : ℛ = r ^ 2 * f * φ * σ / (r ^ 2 * f * φ * σ + x))
    (hqU : qU = q + k ^ 2 * f * φ * σ * (1 - ℛ)) :
    0 < q ∧ 0 ≤ ℛ ∧ ℛ ≤ 1 ∧ q ≤ qU ∧ qU ≤ k ^ 2 * σ + E ∧
      q ≤ l * qU + (1 - l) * q ∧ l * qU + (1 - l) * q ≤ qU ∧
      0 ≤ l * qU + (1 - l) * q * ℛ ∧
      l * qU + (1 - l) * q * ℛ ≤ l * qU + (1 - l) * q ∧
      ℛ * (l * qU + (1 - l) * q) ≤ l * qU + (1 - l) * q * ℛ ∧
      l * qU ≤ l * qU + (1 - l) * q * ℛ := by
  have hq0 : 0 < q := by
    have : 0 ≤ k ^ 2 * (1 - f) * σ := by
      have : 0 ≤ 1 - f := by linarith
      positivity
    rw [hq]; linarith
  have hs0 : 0 ≤ f * φ * σ := by positivity
  have hu0 : 0 ≤ r ^ 2 * f * φ * σ := by positivity
  have hw0 : 0 < r ^ 2 * f * φ * σ + x := by linarith
  have hℛ0 : 0 ≤ ℛ := by rw [hℛ]; positivity
  have hℛ1 : ℛ ≤ 1 := by rw [hℛ, div_le_one hw0]; linarith
  have h1ℛ : 0 ≤ 1 - ℛ := by linarith
  have hK : 0 ≤ k ^ 2 * f * φ * σ := by positivity
  have hqU_ge : q ≤ qU := by
    have : 0 ≤ k ^ 2 * f * φ * σ * (1 - ℛ) := mul_nonneg hK h1ℛ
    rw [hqU]; linarith
  have hqU_le : qU ≤ k ^ 2 * σ + E := by
    have h1 : k ^ 2 * f * φ * σ * (1 - ℛ) ≤ k ^ 2 * f * φ * σ :=
      mul_le_of_le_one_right hK (by linarith)
    have h2 : k ^ 2 * f * φ * σ ≤ k ^ 2 * f * σ := by
      have e : k ^ 2 * f * φ * σ = (k ^ 2 * f * σ) * φ := by ring
      rw [e]; exact mul_le_of_le_one_right (by positivity) hφ1
    have e3 : k ^ 2 * σ + E = k ^ 2 * (1 - f) * σ + E + k ^ 2 * f * σ := by ring
    rw [hqU, hq, e3]; linarith
  have h1l : 0 ≤ 1 - l := by linarith
  have hlq : l * q ≤ l * qU := mul_le_mul_of_nonneg_left hqU_ge hl0
  have hlq2 : (1 - l) * q ≤ (1 - l) * qU := mul_le_mul_of_nonneg_left hqU_ge h1l
  have hBR : (1 - l) * q * ℛ ≤ (1 - l) * q := mul_le_of_le_one_right (mul_nonneg h1l hq0.le) hℛ1
  have hBR0 : 0 ≤ (1 - l) * q * ℛ := mul_nonneg (mul_nonneg h1l hq0.le) hℛ0
  have hlqU : 0 ≤ l * qU := mul_nonneg hl0 (by linarith)
  have hAR : ℛ * (l * qU) ≤ l * qU := mul_le_of_le_one_left hlqU hℛ1
  refine ⟨hq0, hℛ0, hℛ1, hqU_ge, hqU_le, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · have e : ℛ * (l * qU + (1 - l) * q) = ℛ * (l * qU) + (1 - l) * q * ℛ := by ring
    rw [e]; linarith
  · linarith

lemma T_upper (k R g γ x σ f φ l q E r ℛ qU b c : ℝ)
    (hk : 0 < k) (hR : 1 < R) (hg : g = k / R) (hγ : 0 < γ) (hx : 0 < x) (hσ : 0 < σ)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hE : 0 < E)
    (hq : q = k ^ 2 * (1 - f) * σ + E)
    (hr : r = l * k / (γ * q))
    (hℛ : ℛ = r ^ 2 * f * φ * σ / (r ^ 2 * f * φ * σ + x))
    (hqU : qU = q + k ^ 2 * f * φ * σ * (1 - ℛ))
    (hb : b = k / R * ((l * qU + (1 - l) * q * ℛ) / (l * qU + (1 - l) * q)))
    (hc : c = if 0 < l then b / r else γ * qU / R) :
    b ^ 2 * φ * f * σ + g ^ 2 * (1 - φ) * f * σ + c ^ 2 * x ≤
        (k ^ 2 * σ + γ ^ 2 * x * (k ^ 2 * σ + E) ^ 2) / R ^ 2 := by
  obtain ⟨hq0, hℛ0, hℛ1, hqU_ge, hqU_le, hDq, hDqU, hN0, hND, hNℛ, hNA⟩ :=
    basic_facts k R γ x σ f φ l q E r ℛ qU hk hγ hx hσ hf0 hf1 hφ0 hφ1 hl0 hl1 hE hq hℛ hqU
  have hR0 : 0 < R := by linarith
  have hD0 : 0 < l * qU + (1 - l) * q := lt_of_lt_of_le hq0 hDq
  have hbN : b = k * (l * qU + (1 - l) * q * ℛ) / (R * (l * qU + (1 - l) * q)) := by
    rw [hb]; field_simp
  have hs0 : 0 ≤ f * φ * σ := by positivity
  have hqU0 : 0 < qU := lt_of_lt_of_le hq0 hqU_ge
  have hcore : b ^ 2 * (f * φ * σ) + c ^ 2 * x ≤
      (k ^ 2 * (f * φ * σ) + γ ^ 2 * x * qU ^ 2) / R ^ 2 := by
    rcases eq_or_lt_of_le hl0 with hl | hl
    · have hc' : c = γ * qU / R := by rw [hc, ← hl]; simp
      have hr' : r = 0 := by rw [hr, ← hl]; simp
      have hℛ' : ℛ = 0 := by rw [hℛ, hr']; simp
      have hb' : b = 0 := by rw [hbN, hℛ', ← hl]; simp
      rw [hb', hc']
      have h0 : 0 ≤ k ^ 2 * (f * φ * σ) := by positivity
      have e : (0:ℝ) ^ 2 * (f * φ * σ) + (γ * qU / R) ^ 2 * x = (γ ^ 2 * x * qU ^ 2) / R ^ 2 := by
        field_simp; ring
      rw [e]
      have h1 : γ ^ 2 * x * qU ^ 2 ≤ k ^ 2 * (f * φ * σ) + γ ^ 2 * x * qU ^ 2 := by linarith
      exact div_le_div_of_nonneg_right h1 (by positivity)
    · have hc' : c = b / r := by rw [hc]; simp [hl]
      have hℛ' : ℛ = r ^ 2 * (f * φ * σ) / (r ^ 2 * (f * φ * σ) + x) := by rw [hℛ]; ring
      exact core_upper_pos k R γ x q qU l r (f * φ * σ) (r ^ 2 * (f * φ * σ))
        (r ^ 2 * (f * φ * σ) + x) _ _ b c hk hR0 hγ hx hq0 hl hs0 hr rfl rfl rfl hDq
        (by rw [hℛ']) hbN hc'
  have hg2 : g ^ 2 * (1 - φ) * f * σ = k ^ 2 * ((1 - φ) * f * σ) / R ^ 2 := by
    rw [hg]; field_simp
  have e : b ^ 2 * φ * f * σ + g ^ 2 * (1 - φ) * f * σ + c ^ 2 * x =
      (b ^ 2 * (f * φ * σ) + c ^ 2 * x) + k ^ 2 * ((1 - φ) * f * σ) / R ^ 2 := by
    rw [hg2]; ring
  rw [e]
  have h2 : (k ^ 2 * (f * φ * σ) + γ ^ 2 * x * qU ^ 2) / R ^ 2 + k ^ 2 * ((1 - φ) * f * σ) / R ^ 2
      = (k ^ 2 * f * σ + γ ^ 2 * x * qU ^ 2) / R ^ 2 := by ring
  have h3 : (k ^ 2 * f * σ + γ ^ 2 * x * qU ^ 2) / R ^ 2 ≤
      (k ^ 2 * σ + γ ^ 2 * x * (k ^ 2 * σ + E) ^ 2) / R ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h4 : k ^ 2 * f * σ ≤ k ^ 2 * σ := by
      have e : k ^ 2 * f * σ = (k ^ 2 * σ) * f := by ring
      rw [e]; exact mul_le_of_le_one_right (by positivity) hf1
    have h5 : qU ^ 2 ≤ (k ^ 2 * σ + E) ^ 2 := pow_le_pow_left₀ hqU0.le hqU_le 2
    have h6 : γ ^ 2 * x * qU ^ 2 ≤ γ ^ 2 * x * (k ^ 2 * σ + E) ^ 2 :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    linarith
  linarith

lemma T_lower (k R g γ x σ f φ l q E r ℛ qU b c : ℝ)
    (hk : 0 < k) (hR : 1 < R) (hg : g = k / R) (hγ : 0 < γ) (hx : 0 < x) (hσ : 0 < σ)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hE : 0 < E)
    (hq : q = k ^ 2 * (1 - f) * σ + E)
    (hr : r = l * k / (γ * q))
    (hℛ : ℛ = r ^ 2 * f * φ * σ / (r ^ 2 * f * φ * σ + x))
    (hqU : qU = q + k ^ 2 * f * φ * σ * (1 - ℛ))
    (hb : b = k / R * ((l * qU + (1 - l) * q * ℛ) / (l * qU + (1 - l) * q)))
    (hc : c = if 0 < l then b / r else γ * qU / R) :
    min (k ^ 2 * σ / (16 * R ^ 2)) (γ ^ 2 * x * k ^ 4 * σ ^ 2 / (256 * R ^ 2)) ≤
        b ^ 2 * φ * f * σ + g ^ 2 * (1 - φ) * f * σ + c ^ 2 * x := by
  obtain ⟨hq0, hℛ0, hℛ1, hqU_ge, hqU_le, hDq, hDqU, hN0, hND, hNℛ, hNA⟩ :=
    basic_facts k R γ x σ f φ l q E r ℛ qU hk hγ hx hσ hf0 hf1 hφ0 hφ1 hl0 hl1 hE hq hℛ hqU
  have hR0 : 0 < R := by linarith
  set D := l * qU + (1 - l) * q with hD_def
  set N := l * qU + (1 - l) * q * ℛ with hN_def
  have hD0 : 0 < D := lt_of_lt_of_le hq0 hDq
  have hbN : b = k * N / (R * D) := by rw [hb]; field_simp
  have hqU0 : 0 < qU := lt_of_lt_of_le hq0 hqU_ge
  have hT1 : 0 ≤ b ^ 2 * φ * f * σ := by positivity
  have hT2 : 0 ≤ g ^ 2 * (1 - φ) * f * σ := by
    have : 0 ≤ 1 - φ := by linarith
    positivity
  have hT3 : 0 ≤ c ^ 2 * x := by positivity
  have hL1 := min_le_left (k ^ 2 * σ / (16 * R ^ 2)) (γ ^ 2 * x * k ^ 4 * σ ^ 2 / (256 * R ^ 2))
  have hL2 := min_le_right (k ^ 2 * σ / (16 * R ^ 2)) (γ ^ 2 * x * k ^ 4 * σ ^ 2 / (256 * R ^ 2))
  -- general lower bound on c
  have hcl : γ * q * qU / (R * D) ≤ c := by
    rcases eq_or_lt_of_le hl0 with hl | hl
    · have hc' : c = γ * qU / R := by rw [hc, ← hl]; simp
      have hD' : D = q := by rw [hD_def, ← hl]; ring
      rw [hc', hD']
      apply le_of_eq; field_simp
    · have hc' : c = b / r := by rw [hc]; simp [hl]
      exact c_lower_pos k R γ q qU l r N D b c hk hR0 hγ hq0 hl hr hD0 hNA hbN hc'
  -- three sufficient conditions
  have suff_c : γ * k ^ 2 * σ / (16 * R) ≤ c →
      min (k ^ 2 * σ / (16 * R ^ 2)) (γ ^ 2 * x * k ^ 4 * σ ^ 2 / (256 * R ^ 2)) ≤
        b ^ 2 * φ * f * σ + g ^ 2 * (1 - φ) * f * σ + c ^ 2 * x := by
    intro hc1
    have h0 : 0 ≤ γ * k ^ 2 * σ / (16 * R) := by positivity
    have h1 : (γ * k ^ 2 * σ / (16 * R)) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ h0 hc1 2
    have h2 : (γ * k ^ 2 * σ / (16 * R)) ^ 2 * x ≤ c ^ 2 * x := mul_le_mul_of_nonneg_right h1 hx.le
    have e : (γ * k ^ 2 * σ / (16 * R)) ^ 2 * x = γ ^ 2 * x * k ^ 4 * σ ^ 2 / (256 * R ^ 2) := by
      field_simp; ring
    linarith
  have suff_b : k / (2 * R) ≤ b → σ / 4 ≤ f * φ * σ →
      min (k ^ 2 * σ / (16 * R ^ 2)) (γ ^ 2 * x * k ^ 4 * σ ^ 2 / (256 * R ^ 2)) ≤
        b ^ 2 * φ * f * σ + g ^ 2 * (1 - φ) * f * σ + c ^ 2 * x := by
    intro hb1 hs1
    have h0 : 0 ≤ k / (2 * R) := by positivity
    have h1 : (k / (2 * R)) ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ h0 hb1 2
    have h2 : (k / (2 * R)) ^ 2 * (σ / 4) ≤ b ^ 2 * (f * φ * σ) :=
      mul_le_mul h1 hs1 (by positivity) (by positivity)
    have e : (k / (2 * R)) ^ 2 * (σ / 4) = k ^ 2 * σ / (16 * R ^ 2) := by field_simp; ring
    have e2 : b ^ 2 * (f * φ * σ) = b ^ 2 * φ * f * σ := by ring
    linarith
  by_cases hf2 : f ≤ 1 / 2
  · apply suff_c
    have hqb : k ^ 2 * σ / 2 ≤ q := by
      have : k ^ 2 * σ / 2 ≤ k ^ 2 * (1 - f) * σ := by
        have e : k ^ 2 * (1 - f) * σ = (k ^ 2 * σ) * (1 - f) := by ring
        rw [e]
        have : (1:ℝ) / 2 ≤ 1 - f := by linarith
        have h := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ k ^ 2 * σ)
        linarith
      rw [hq]; linarith
    have hcq : γ * q / R ≤ c := by
      refine le_trans ?_ hcl
      rw [div_le_div_iff₀ hR0 (by positivity)]
      have h := mul_le_mul_of_nonneg_left hDqU (by positivity : (0:ℝ) ≤ γ * q * R)
      linarith
    refine le_trans ?_ hcq
    rw [div_le_div_iff₀ (by positivity) hR0]
    have h := mul_le_mul_of_nonneg_left hqb (by positivity : (0:ℝ) ≤ γ * (16 * R))
    have h0 : 0 ≤ γ * k ^ 2 * σ * R := by positivity
    linarith
  push_neg at hf2
  by_cases hφ2 : φ ≤ 1 / 2
  · have h1 : (1:ℝ) / 4 ≤ (1 - φ) * f := by
      have := mul_le_mul (by linarith : (1:ℝ) / 2 ≤ 1 - φ) hf2.le (by norm_num) (by linarith)
      linarith
    have hg2 : g ^ 2 * (1 - φ) * f * σ = (k ^ 2 * σ / R ^ 2) * ((1 - φ) * f) := by
      rw [hg]; field_simp
    have h2 : (k ^ 2 * σ / R ^ 2) * (1 / 4) ≤ (k ^ 2 * σ / R ^ 2) * ((1 - φ) * f) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e : (k ^ 2 * σ / R ^ 2) * (1 / 4) = 4 * (k ^ 2 * σ / (16 * R ^ 2)) := by field_simp; ring
    have h3 : 0 ≤ k ^ 2 * σ / (16 * R ^ 2) := by positivity
    linarith
  push_neg at hφ2
  have hfφ : (1:ℝ) / 4 ≤ f * φ := by
    have := mul_le_mul hf2.le hφ2.le (by norm_num) hf0
    linarith
  have hs4 : σ / 4 ≤ f * φ * σ := by
    have h := mul_le_mul_of_nonneg_right hfφ hσ.le
    linarith
  have hk2s : k ^ 2 * σ / 4 ≤ k ^ 2 * f * φ * σ := by
    have h := mul_le_mul_of_nonneg_left hs4 (by positivity : (0:ℝ) ≤ k ^ 2)
    have e : k ^ 2 * f * φ * σ = k ^ 2 * (f * φ * σ) := by ring
    rw [e]; linarith
  rcases eq_or_lt_of_le hl0 with hl | hl
  · apply suff_c
    have hc' : c = γ * qU / R := by rw [hc, ← hl]; simp
    have hr' : r = 0 := by rw [hr, ← hl]; simp
    have hℛ' : ℛ = 0 := by rw [hℛ, hr']; simp
    have hqU' : k ^ 2 * σ / 4 ≤ qU := by rw [hqU, hℛ']; linarith
    rw [hc', div_le_div_iff₀ (by positivity) hR0]
    have h := mul_le_mul_of_nonneg_left hqU' (by positivity : (0:ℝ) ≤ γ * (16 * R))
    have h0 : 0 ≤ γ * k ^ 2 * σ * R := by positivity
    linarith
  by_cases hℛ2 : 1 / 2 ≤ ℛ
  · apply suff_b _ hs4
    have := b_lower k R N D b ℛ hk hR0 hD0 hbN hNℛ
    refine le_trans ?_ this
    rw [div_le_div_iff₀ (by positivity) hR0]
    have := mul_le_mul_of_nonneg_left hℛ2 (by positivity : (0:ℝ) ≤ k * (2 * R))
    linarith
  push_neg at hℛ2
  by_cases hAB : (1 - l) * q ≤ l * qU
  · apply suff_b _ hs4
    have h2 : (1 / 2) * D ≤ N := by rw [hD_def]; linarith
    have := b_lower k R N D b (1 / 2) hk hR0 hD0 hbN h2
    refine le_trans (le_of_eq ?_) this
    field_simp
  push_neg at hAB
  apply suff_c
  have hD2 : D ≤ 2 * q := by
    rw [hD_def]
    have : (1 - l) * q ≤ q := mul_le_of_le_one_left hq0.le (by linarith)
    linarith
  have hqUb : k ^ 2 * σ / 8 ≤ qU := by
    have h12 : (1:ℝ) / 2 ≤ 1 - ℛ := by linarith
    have h := mul_le_mul_of_nonneg_left h12 (by positivity : (0:ℝ) ≤ k ^ 2 * f * φ * σ)
    rw [hqU]; linarith
  refine le_trans ?_ hcl
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : γ * k ^ 2 * σ * (R * D) ≤ γ * k ^ 2 * σ * (R * (2 * q)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD2 hR0.le) (by positivity)
  have h2 : γ * k ^ 2 * σ * (R * (2 * q)) ≤ γ * q * qU * (16 * R) := by
    have h := mul_le_mul_of_nonneg_left hqUb (by positivity : (0:ℝ) ≤ γ * q * (16 * R))
    linarith
  linarith

/-- The self-consistency map at one state, as a function of `E = E[V_B(f_{t+1}) | f_t]`. -/
noncomputable def qF (k σ f E : ℝ) : ℝ := k ^ 2 * (1 - f) * σ + E
noncomputable def rF (k γ σ f l E : ℝ) : ℝ := l * k / (γ * qF k σ f E)
noncomputable def ℛF (k γ x σ f φ l E : ℝ) : ℝ :=
  rF k γ σ f l E ^ 2 * f * φ * σ / (rF k γ σ f l E ^ 2 * f * φ * σ + x)
noncomputable def qUF (k γ x σ f φ l E : ℝ) : ℝ :=
  qF k σ f E + k ^ 2 * f * φ * σ * (1 - ℛF k γ x σ f φ l E)
noncomputable def bF (k R γ x σ f φ l E : ℝ) : ℝ :=
  k / R * ((l * qUF k γ x σ f φ l E + (1 - l) * qF k σ f E * ℛF k γ x σ f φ l E) /
    (l * qUF k γ x σ f φ l E + (1 - l) * qF k σ f E))
noncomputable def cF (k R γ x σ f φ l E : ℝ) : ℝ :=
  if 0 < l then bF k R γ x σ f φ l E / rF k γ σ f l E else γ * qUF k γ x σ f φ l E / R
noncomputable def TF (k R g γ x σ f φ l E : ℝ) : ℝ :=
  bF k R γ x σ f φ l E ^ 2 * φ * f * σ + g ^ 2 * (1 - φ) * f * σ + cF k R γ x σ f φ l E ^ 2 * x

lemma TF_contOn (k R g γ x σ f φ l : ℝ)
    (hk : 0 < k) (hR : 1 < R) (hγ : 0 < γ) (hx : 0 < x) (hσ : 0 < σ)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    ContinuousOn (fun E => TF k R g γ x σ f φ l E) (Set.Ioi 0) := by
  have hR0 : 0 < R := by linarith
  have facts : ∀ E ∈ Set.Ioi (0:ℝ), 0 < qF k σ f E ∧
      0 < l * qUF k γ x σ f φ l E + (1 - l) * qF k σ f E := by
    intro E hE
    obtain ⟨hq0, -, -, -, -, hDq, -⟩ := basic_facts k R γ x σ f φ l (qF k σ f E) E
      (rF k γ σ f l E) (ℛF k γ x σ f φ l E) (qUF k γ x σ f φ l E) hk hγ hx hσ hf0 hf1 hφ0 hφ1
      hl0 hl1 hE rfl rfl rfl
    exact ⟨hq0, lt_of_lt_of_le hq0 hDq⟩
  have hq : ContinuousOn (fun E => qF k σ f E) (Set.Ioi 0) := by
    unfold qF; fun_prop
  have hr : ContinuousOn (fun E => rF k γ σ f l E) (Set.Ioi 0) := by
    unfold rF
    exact continuousOn_const.div (continuousOn_const.mul hq)
      (fun E hE => (mul_pos hγ (facts E hE).1).ne')
  have hℛ : ContinuousOn (fun E => ℛF k γ x σ f φ l E) (Set.Ioi 0) := by
    unfold ℛF
    have h1 : ContinuousOn (fun E => rF k γ σ f l E ^ 2 * f * φ * σ) (Set.Ioi 0) := by
      fun_prop
    refine h1.div (h1.add continuousOn_const) ?_
    intro E _
    have : 0 ≤ rF k γ σ f l E ^ 2 * f * φ * σ := by positivity
    exact (by linarith : (0:ℝ) < rF k γ σ f l E ^ 2 * f * φ * σ + x).ne'
  have hqU : ContinuousOn (fun E => qUF k γ x σ f φ l E) (Set.Ioi 0) := by
    unfold qUF
    exact hq.add (continuousOn_const.mul (continuousOn_const.sub hℛ))
  have hb : ContinuousOn (fun E => bF k R γ x σ f φ l E) (Set.Ioi 0) := by
    unfold bF
    refine continuousOn_const.mul ?_
    refine ((continuousOn_const.mul hqU).add ((continuousOn_const.mul hq).mul hℛ)).div
      ((continuousOn_const.mul hqU).add (continuousOn_const.mul hq)) ?_
    intro E hE
    exact (facts E hE).2.ne'
  have hc : ContinuousOn (fun E => cF k R γ x σ f φ l E) (Set.Ioi 0) := by
    unfold cF
    by_cases hl : 0 < l
    · simp only [hl, if_true]
      refine hb.div hr ?_
      intro E hE
      unfold rF
      exact (div_pos (mul_pos hl hk) (mul_pos hγ (facts E hE).1)).ne'
    · simp only [hl, if_false]
      exact (continuousOn_const.mul hqU).div continuousOn_const (fun _ _ => hR0.ne')
  unfold TF
  exact ((((hb.pow 2).mul continuousOn_const).mul continuousOn_const).mul continuousOn_const).add
    continuousOn_const |>.add ((hc.pow 2).mul continuousOn_const)

end IR41Aux

namespace IR41Aux
open InfoRegimes.MarketEq

lemma trans_nonneg (P : Params) (lam : State P → ℝ) (i j : State P) : 0 ≤ trans P lam i j :=
  ENNReal.toReal_nonneg

lemma trans_sum (P : Params) (lam : State P → ℝ) (i : State P) :
    ∑ j, trans P lam i j = 1 := by
  set c := P.af + P.bf * lam i + P.kf * (grid P i - P.af) with hc
  let A : State P → Set ℝ := fun j => {e : ℝ | projD P (c + e) = j}
  have hnat : Measurable (fun e : ℝ => min P.m ⌈(P.m : ℝ) * max 0 (min 1 (c + e))⌉₊) :=
    measurable_const.min ((measurable_const.mul (measurable_const.max
      (measurable_const.min (measurable_const.add measurable_id)))).nat_ceil)
  have hmeas : ∀ j, MeasurableSet (A j) := by
    intro j
    have : A j = (fun e : ℝ => min P.m ⌈(P.m : ℝ) * max 0 (min 1 (c + e))⌉₊) ⁻¹' {(j : ℕ)} := by
      ext e
      simp only [A, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, projD, Fin.ext_iff]
    rw [this]
    exact hnat (measurableSet_singleton _)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (State P))) A := by
    intro j _ k _ hjk
    rw [Function.onFun, Set.disjoint_left]
    intro e hej hek
    exact hjk (hej.symm.trans hek)
  have hunion : (⋃ j ∈ (Finset.univ : Finset (State P)), A j) = Set.univ := by
    ext e
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left, Set.mem_univ, iff_true]
    exact ⟨projD P (c + e), rfl⟩
  have h1 := MeasureTheory.measure_biUnion_finset (μ := (P.shock : MeasureTheory.Measure ℝ))
    hdisj (fun j _ => hmeas j)
  rw [hunion, MeasureTheory.measure_univ] at h1
  unfold InfoRegimes.MarketEq.trans
  rw [← ENNReal.toReal_sum (fun j _ => MeasureTheory.measure_ne_top _ _)]
  have : (∑ j, (P.shock : MeasureTheory.Measure ℝ) {e : ℝ | projD P
      (P.af + P.bf * lam i + P.kf * (grid P i - P.af) + e) = j}) = 1 := by
    rw [h1]
  rw [this, ENNReal.toReal_one]

lemma Ef_bounds (P : Params) (lam : State P → ℝ) (i : State P) (h : State P → ℝ) (L U : ℝ)
    (hh : ∀ j, L ≤ h j ∧ h j ≤ U) : L ≤ Ef P lam i h ∧ Ef P lam i h ≤ U := by
  unfold Ef
  constructor
  · calc L = ∑ j, trans P lam i j * L := by rw [← Finset.sum_mul, trans_sum, one_mul]
      _ ≤ ∑ j, trans P lam i j * h j := Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (hh j).1 (trans_nonneg P lam i j))
  · calc ∑ j, trans P lam i j * h j ≤ ∑ j, trans P lam i j * U := Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (hh j).2 (trans_nonneg P lam i j))
      _ = U := by rw [← Finset.sum_mul, trans_sum, one_mul]

lemma Ef_continuous (P : Params) (lam : State P → ℝ) (i : State P) :
    Continuous (fun h : State P → ℝ => Ef P lam i h) := by
  unfold Ef
  exact continuous_finset_sum _ (fun j _ => continuous_const.mul (continuous_apply j))

lemma grid_bounds (P : Params) (hm : 1 ≤ P.m) (i : State P) : 0 ≤ grid P i ∧ grid P i ≤ 1 := by
  have hm' : (0 : ℝ) < P.m := by exact_mod_cast hm
  unfold grid
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hm']
  exact_mod_cast Nat.lt_succ_iff.mp i.2

lemma Tmap_eq (P : Params) (lam VB : State P → ℝ) (i : State P) :
    Tmap P lam VB i = TF (1 + dConst P) P.R (gConst P) P.gam (P.sigX ^ 2) (P.sigM ^ 2)
      (grid P i) P.phi (lam i) (Ef P lam i VB) := rfl

end IR41Aux

open InfoRegimes.MarketEq IR41Aux in
theorem solution (P : Params) (hS : P.Standing) (hR : P.R ≤ 6 / 5)
    (h27 : (1 + P.rho / (P.R - P.rho)) * P.gam * P.sigM * P.sigX ≤ 7 / 25)
    (lam : State P → ℝ) (hlam : ∀ i, lam i ∈ Set.Icc (0 : ℝ) 1) :
    MarketEquilibrium P lam := by
  obtain ⟨hR1, hρ1, hρ2, hσM, hσX, hγ, hφ0, hφ1, hX, hm⟩ := hS
  have hS' : P.Standing := ⟨hR1, hρ1, hρ2, hσM, hσX, hγ, hφ0, hφ1, hX, hm⟩
  set k := 1 + dConst P with hk_def
  have hRρ : 0 < P.R - P.rho := by linarith
  have hk_eq : k = P.R / (P.R - P.rho) := by
    rw [hk_def]; unfold dConst; field_simp; ring
  have hk : 0 < k := by rw [hk_eq]; exact div_pos (by linarith) hRρ
  have hg : gConst P = k / P.R := by
    rw [hk_eq]; unfold gConst; field_simp
  have hR0 : 0 < P.R := by linarith
  set σ := P.sigM ^ 2 with hσ_def
  set x := P.sigX ^ 2 with hx_def
  have hσ : 0 < σ := by positivity
  have hx : 0 < x := by positivity
  set U := 2 * k ^ 2 * σ with hU_def
  set L := min (k ^ 2 * σ / (16 * P.R ^ 2)) (P.gam ^ 2 * x * k ^ 4 * σ ^ 2 / (256 * P.R ^ 2))
    with hL_def
  have hL0 : 0 < L := by
    rw [hL_def]; apply lt_min <;> positivity
  have hLU : L ≤ U := by
    have h1 : L ≤ k ^ 2 * σ / (16 * P.R ^ 2) := min_le_left _ _
    have h2 : k ^ 2 * σ / (16 * P.R ^ 2) ≤ k ^ 2 * σ := by
      rw [div_le_iff₀ (by positivity)]
      have : 1 ≤ 16 * P.R ^ 2 := by nlinarith
      have h0 : 0 ≤ k ^ 2 * σ := by positivity
      nlinarith
    have : 0 ≤ k ^ 2 * σ := by positivity
    linarith
  -- (27) squared
  have h27' : P.gam ^ 2 * x * k ^ 2 * σ ≤ 49 / 625 := by
    have e : P.gam ^ 2 * x * k ^ 2 * σ = (k * P.gam * P.sigM * P.sigX) ^ 2 := by
      rw [hx_def, hσ_def]; ring
    have h0 : 0 ≤ k * P.gam * P.sigM * P.sigX := by positivity
    have h27k : k * P.gam * P.sigM * P.sigX ≤ 7 / 25 := by
      rw [hk_def]; unfold dConst; exact h27
    rw [e]
    have := pow_le_pow_left₀ h0 h27k 2
    linarith [show ((7:ℝ) / 25) ^ 2 = 49 / 625 by norm_num]
  set K : Set (State P → ℝ) := Set.Icc (fun _ => L) (fun _ => U) with hK_def
  have memK : ∀ VB : State P → ℝ, VB ∈ K ↔ ∀ j, L ≤ VB j ∧ VB j ≤ U := by
    intro VB
    simp only [hK_def, Set.mem_Icc, Pi.le_def]
    exact ⟨fun h j => ⟨h.1 j, h.2 j⟩, fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩⟩
  have hKconv : Convex ℝ K := convex_Icc _ _
  have hKcpt : IsCompact K := isCompact_Icc
  have hKne : K.Nonempty := ⟨fun _ => L, (memK _).2 (fun _ => ⟨le_rfl, hLU⟩)⟩
  -- per-state bounds
  have hbounds : ∀ VB ∈ K, ∀ i, L ≤ Tmap P lam VB i ∧ Tmap P lam VB i ≤ U := by
    intro VB hVB i
    obtain ⟨hE1, hE2⟩ := Ef_bounds P lam i VB L U ((memK VB).1 hVB)
    have hE : 0 < Ef P lam i VB := lt_of_lt_of_le hL0 hE1
    obtain ⟨hf0, hf1⟩ := grid_bounds P hm i
    obtain ⟨hl0, hl1⟩ := hlam i
    rw [Tmap_eq]
    unfold TF
    constructor
    · exact T_lower k P.R (gConst P) P.gam x σ (grid P i) P.phi (lam i) _ (Ef P lam i VB) _ _ _ _ _
        hk hR1 hg hγ hx hσ hf0 hf1 hφ0 hφ1 hl0 hl1 hE rfl rfl rfl rfl rfl rfl
    · have hup := T_upper k P.R (gConst P) P.gam x σ (grid P i) P.phi (lam i) _ (Ef P lam i VB)
        _ _ _ _ _ hk hR1 hg hγ hx hσ hf0 hf1 hφ0 hφ1 hl0 hl1 hE rfl rfl rfl rfl rfl rfl
      refine le_trans hup ?_
      have hR2 : 1 ≤ P.R ^ 2 := by nlinarith
      have hnum0 : 0 ≤ k ^ 2 * σ + P.gam ^ 2 * x * (k ^ 2 * σ + Ef P lam i VB) ^ 2 := by positivity
      have h1 : (k ^ 2 * σ + P.gam ^ 2 * x * (k ^ 2 * σ + Ef P lam i VB) ^ 2) / P.R ^ 2 ≤
          k ^ 2 * σ + P.gam ^ 2 * x * (k ^ 2 * σ + Ef P lam i VB) ^ 2 :=
        div_le_self hnum0 hR2
      have h2 : (k ^ 2 * σ + Ef P lam i VB) ^ 2 ≤ (3 * (k ^ 2 * σ)) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        rw [hU_def] at hE2; linarith
      have h3 : P.gam ^ 2 * x * (k ^ 2 * σ + Ef P lam i VB) ^ 2 ≤
          P.gam ^ 2 * x * (3 * (k ^ 2 * σ)) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 : P.gam ^ 2 * x * (3 * (k ^ 2 * σ)) ^ 2 = 9 * (P.gam ^ 2 * x * k ^ 2 * σ) * (k ^ 2 * σ) := by
        ring
      have h5 : 9 * (P.gam ^ 2 * x * k ^ 2 * σ) * (k ^ 2 * σ) ≤ 9 * (49 / 625) * (k ^ 2 * σ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
      have h6 : 0 ≤ k ^ 2 * σ := by positivity
      rw [hU_def]
      linarith
  have hmaps : Set.MapsTo (Tmap P lam) K K := by
    intro VB hVB
    exact (memK _).2 (hbounds VB hVB)
  have hcont : ContinuousOn (Tmap P lam) K := by
    apply continuousOn_pi.2
    intro i
    obtain ⟨hf0, hf1⟩ := grid_bounds P hm i
    obtain ⟨hl0, hl1⟩ := hlam i
    have hTF := TF_contOn k P.R (gConst P) P.gam x σ (grid P i) P.phi (lam i) hk hR1 hγ hx hσ
      hf0 hf1 hφ0 hφ1 hl0 hl1
    have hcomp := hTF.comp (Ef_continuous P lam i).continuousOn (fun VB hVB => by
      obtain ⟨hE1, -⟩ := Ef_bounds P lam i VB L U ((memK VB).1 hVB)
      exact Set.mem_Ioi.2 (lt_of_lt_of_le hL0 hE1))
    refine hcomp.congr ?_
    intro VB _
    exact Tmap_eq P lam VB i
  obtain ⟨VB, hVBK, hfix⟩ := AGT.brouwer_fixed_point hKconv hKcpt hKne (Tmap P lam) hcont hmaps
  have hVBpos : ∀ i, 0 < VB i := fun i => lt_of_lt_of_le hL0 ((memK VB).1 hVBK i).1
  exact (selfConsistent_marketEquilibrium P hS' lam hlam VB hVBpos).2 hfix
