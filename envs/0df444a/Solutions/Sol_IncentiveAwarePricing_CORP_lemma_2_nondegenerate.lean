-- Prove2me | solution 1 for IncentiveAwarePricing.CORP.lemma_2_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:17:56.766147+00:00
-- url     : https://prove2.me/submissions/e62863d4-c8b0-4f77-983f-dde5c2e18b92

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_IncentiveAwarePricing_CORP_Model

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace G80IAP
open IncentiveAwarePricing.CORP

variable {Bn : ℝ} {f : ℝ → ℝ}

theorem integrable_f (hf : NoiseStanding Bn f) : Integrable f := by
  have h1 : IntegrableOn f (Icc (-Bn) Bn) := hf.continuousOn.integrableOn_Icc
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp h1
  intro x hx
  by_contra h
  exact hx (hf.zero_outside x h)

theorem integral_f (hf : NoiseStanding Bn f) : ∫ x, f x = 1 := by
  have h1 : ∫ x in Icc (-Bn) Bn, f x = ∫ x, f x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hf.zero_outside x hx
  rw [← h1, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [hf.pos]),
    hf.mass_one]

theorem cdf_le_one (hf : NoiseStanding Bn f) (z : ℝ) : noiseCDF f z ≤ 1 := by
  unfold noiseCDF
  rw [← integral_f hf]
  exact setIntegral_le_integral (integrable_f hf) (Filter.Eventually.of_forall hf.nonneg)

theorem cdf_low (hf : NoiseStanding Bn f) {z : ℝ} (hz : z < -Bn) : noiseCDF f z = 0 := by
  unfold noiseCDF
  refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => hf.zero_outside x ?_
  intro h; have : x ≤ z := hx; linarith [h.1]

theorem cdf_high (hf : NoiseStanding Bn f) {z : ℝ} (hz : Bn ≤ z) : noiseCDF f z = 1 := by
  unfold noiseCDF
  rw [← integral_f hf]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hf.zero_outside x ?_
  intro h; have : z < x := not_le.mp hx; linarith [h.2]

/-- survival function -/
noncomputable def G (f : ℝ → ℝ) (z : ℝ) : ℝ := 1 - noiseCDF f z

theorem G_nonneg (hf : NoiseStanding Bn f) (z : ℝ) : 0 ≤ G f z := by
  unfold G; linarith [cdf_le_one hf z]

theorem obj_eq (θ y : ℝ) : reserveObjective f θ y = y * G f (y - θ) := rfl

/-- basic facts about a maximizer -/
theorem max_facts (hf : NoiseStanding Bn f) (hF : ∀ z, z < Bn → noiseCDF f z < 1)
    {θ r : ℝ} (hθ : -Bn < θ) (hr : IsMaxOn (reserveObjective f θ) univ r) :
    0 < r * G f (r - θ) ∧ 0 < r ∧ 0 < G f (r - θ) ∧ -Bn ≤ r - θ ∧ r - θ < Bn := by
  have hmax : ∀ y, y * G f (y - θ) ≤ r * G f (r - θ) := fun y =>
    isMaxOn_iff.mp hr y (mem_univ _)
  set y0 := (θ + Bn) / 2
  have hy0 : 0 < y0 := by simp only [y0]; linarith
  have hG0 : 0 < G f (y0 - θ) := by
    unfold G; have := hF (y0 - θ) (by simp only [y0]; linarith); linarith
  have hpos : 0 < r * G f (r - θ) := lt_of_lt_of_le (mul_pos hy0 hG0) (hmax y0)
  have hGnn := G_nonneg hf (r - θ)
  have hr0 : 0 < r := by
    by_contra h; push_neg at h; nlinarith
  have hG : 0 < G f (r - θ) := by
    rcases hGnn.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hpos; exact absurd hpos (lt_irrefl _)
  refine ⟨hpos, hr0, hG, ?_, ?_⟩
  · by_contra h
    push_neg at h
    set ε := (-Bn - (r - θ)) / 2
    have hε : 0 < ε := by simp only [ε]; linarith
    have h1 : G f (r - θ) = 1 := by unfold G; rw [cdf_low hf h]; ring
    have h2 : G f (r + ε - θ) = 1 := by
      unfold G; rw [cdf_low hf (by simp only [ε]; linarith)]; ring
    have := hmax (r + ε)
    rw [h1, h2] at this
    linarith
  · by_contra h
    push_neg at h
    have : G f (r - θ) = 0 := by unfold G; rw [cdf_high hf h]; ring
    linarith

/-- log-concavity in product form -/
theorem logconc_pair (hf : NoiseStanding Bn f) (hA : Assumption1 Bn f) {a b c d : ℝ}
    (ha : a ∈ Icc (-Bn) Bn) (hd : d ∈ Icc (-Bn) Bn) (hab : a < b) (hbd : b < d)
    (hsum : a + d = b + c) (hGa : 0 < G f a) (hGd : 0 < G f d) :
    G f a * G f d ≤ G f b * G f c := by
  have hlc := hA.2.2
  set lam := (d - b) / (d - a) with hlam
  have hda : 0 < d - a := by linarith
  have hl0 : 0 ≤ lam := div_nonneg (by linarith) hda.le
  have hl1 : 0 ≤ 1 - lam := by
    rw [hlam, one_sub_div hda.ne']; exact div_nonneg (by linarith) hda.le
  have hb : lam • a + (1 - lam) • d = b := by
    simp only [smul_eq_mul, hlam]; field_simp; ring
  have hc : (1 - lam) • a + lam • d = c := by
    rw [show c = a + d - b by linarith]
    simp only [smul_eq_mul, hlam]; field_simp; ring
  have h1 := hlc a ha d hd lam (1 - lam) hl0 hl1 (by ring)
  have h2 := hlc a ha d hd (1 - lam) lam hl1 hl0 (by ring)
  rw [hb] at h1; rw [hc] at h2
  change G f a ^ lam * G f d ^ (1 - lam) ≤ G f b at h1
  change G f a ^ (1 - lam) * G f d ^ lam ≤ G f c at h2
  have h3 := mul_le_mul h1 h2 (by positivity) (le_trans (by positivity) h1)
  calc G f a * G f d = (G f a ^ lam * G f d ^ (1 - lam)) * (G f a ^ (1 - lam) * G f d ^ lam) := by
        rw [show (G f a ^ lam * G f d ^ (1 - lam)) * (G f a ^ (1 - lam) * G f d ^ lam)
          = (G f a ^ lam * G f a ^ (1 - lam)) * (G f d ^ (1 - lam) * G f d ^ lam) by ring,
          ← Real.rpow_add hGa, ← Real.rpow_add hGd]
        simp
    _ ≤ G f b * G f c := h3

/-- uniqueness of the maximizer -/
theorem max_unique (hf : NoiseStanding Bn f) (hA : Assumption1 Bn f)
    (hF : ∀ z, z < Bn → noiseCDF f z < 1)
    {θ r₁ r₂ : ℝ} (hθ : -Bn < θ) (h₁ : IsMaxOn (reserveObjective f θ) univ r₁)
    (h₂ : IsMaxOn (reserveObjective f θ) univ r₂) : r₁ = r₂ := by
  wlog hlt : r₁ < r₂ generalizing r₁ r₂
  · rcases lt_trichotomy r₁ r₂ with h | h | h
    · exact this h₁ h₂ h
    · exact h
    · exact (this h₂ h₁ h).symm
  obtain ⟨hp1, hr1, hG1, hl1, hu1⟩ := max_facts hf hF hθ h₁
  obtain ⟨hp2, hr2, hG2, hl2, hu2⟩ := max_facts hf hF hθ h₂
  have hV : r₁ * G f (r₁ - θ) = r₂ * G f (r₂ - θ) :=
    le_antisymm (by have := isMaxOn_iff.mp h₂ r₁ (mem_univ _); exact this)
      (by have := isMaxOn_iff.mp h₁ r₂ (mem_univ _); exact this)
  set m := (r₁ + r₂) / 2
  have hlc := hA.2.2 (r₁ - θ) ⟨hl1, hu1.le⟩ (r₂ - θ) ⟨hl2, hu2.le⟩ (1/2) (1/2)
    (by norm_num) (by norm_num) (by norm_num)
  have hmid : (1/2 : ℝ) • (r₁ - θ) + (1/2 : ℝ) • (r₂ - θ) = m - θ := by
    simp only [smul_eq_mul, m]; ring
  rw [hmid] at hlc
  change G f (r₁ - θ) ^ (1/2 : ℝ) * G f (r₂ - θ) ^ (1/2 : ℝ) ≤ G f (m - θ) at hlc
  have hsq : (G f (r₁ - θ) ^ (1/2 : ℝ) * G f (r₂ - θ) ^ (1/2 : ℝ)) ^ 2
      = G f (r₁ - θ) * G f (r₂ - θ) := by
    rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hG1.le,
      Real.sq_sqrt hG2.le]
  have hGm2 : G f (r₁ - θ) * G f (r₂ - θ) ≤ G f (m - θ) ^ 2 := by
    rw [← hsq]; exact pow_le_pow_left₀ (by positivity) hlc 2
  have hm : r₁ * r₂ < m ^ 2 := by simp only [m]; nlinarith [sq_pos_of_pos (sub_pos.mpr hlt)]
  have hPm : (r₁ * G f (r₁ - θ)) ^ 2 < (m * G f (m - θ)) ^ 2 := by
    have e : (r₁ * G f (r₁ - θ)) ^ 2 = (r₁ * r₂) * (G f (r₁ - θ) * G f (r₂ - θ)) := by
      rw [sq]; nth_rewrite 2 [hV]; ring
    rw [e, mul_pow]
    calc (r₁ * r₂) * (G f (r₁ - θ) * G f (r₂ - θ)) < m ^ 2 * (G f (r₁ - θ) * G f (r₂ - θ)) :=
          mul_lt_mul_of_pos_right hm (mul_pos hG1 hG2)
      _ ≤ m ^ 2 * G f (m - θ) ^ 2 := mul_le_mul_of_nonneg_left hGm2 (by positivity)
  have hmax := isMaxOn_iff.mp h₁ m (mem_univ _)
  change m * G f (m - θ) ≤ r₁ * G f (r₁ - θ) at hmax
  have hmn : 0 ≤ m * G f (m - θ) := mul_nonneg (by simp only [m]; linarith) (G_nonneg hf _)
  nlinarith

/-- monotonicity of `r - θ` -/
theorem z_anti (hf : NoiseStanding Bn f) (hF : ∀ z, z < Bn → noiseCDF f z < 1)
    {θ θ' r r' : ℝ} (hθ : -Bn < θ) (hθθ : θ < θ')
    (hr : IsMaxOn (reserveObjective f θ) univ r) (hr' : IsMaxOn (reserveObjective f θ') univ r') :
    r' - θ' ≤ r - θ := by
  obtain ⟨hp, hr0, hG, -, -⟩ := max_facts hf hF hθ hr
  obtain ⟨hp', hr0', hG', -, -⟩ := max_facts hf hF (by linarith) hr'
  by_contra hcon
  push_neg at hcon
  set z := r - θ
  set z' := r' - θ'
  have h1 := isMaxOn_iff.mp hr (z' + θ) (mem_univ _)
  have h2 := isMaxOn_iff.mp hr' (z + θ') (mem_univ _)
  rw [obj_eq, obj_eq] at h1 h2
  simp only [add_sub_cancel_right] at h1 h2
  -- A = r G(z), B = (z'+θ) G(z'), C = r' G(z'), D = (z+θ') G(z)
  have hA : r * G f z = (z + θ) * G f z := by simp only [z]; ring_nf
  have hC : r' * G f z' = (z' + θ') * G f z' := by simp only [z']; ring_nf
  have hD : 0 ≤ (z + θ') * G f z := mul_nonneg (by simp only [z]; linarith) hG.le
  have key : (r * G f z) * (r' * G f z') ≥ ((z' + θ) * G f z') * ((z + θ') * G f z) := by
    rcases le_total 0 ((z' + θ) * G f z') with hB | hB
    · calc (r * G f z) * (r' * G f z') ≥ ((z' + θ) * G f z') * (r' * G f z') :=
            mul_le_mul_of_nonneg_right h1 hp'.le
        _ ≥ ((z' + θ) * G f z') * ((z + θ') * G f z) := mul_le_mul_of_nonneg_left h2 hB
    · have : ((z' + θ) * G f z') * ((z + θ') * G f z) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hB hD
      nlinarith
  rw [hA, hC] at key
  have : 0 < G f z * G f z' * ((z' - z) * (θ' - θ)) :=
    mul_pos (mul_pos hG hG') (mul_pos (by linarith) (by linarith))
  nlinarith

/-- monotonicity of `r` -/
theorem r_mono (hf : NoiseStanding Bn f) (hA : Assumption1 Bn f)
    (hF : ∀ z, z < Bn → noiseCDF f z < 1)
    {θ θ' r r' : ℝ} (hθ : -Bn < θ) (hθθ : θ < θ')
    (hr : IsMaxOn (reserveObjective f θ) univ r) (hr' : IsMaxOn (reserveObjective f θ') univ r') :
    r ≤ r' := by
  obtain ⟨hp, hr0, hG, hl, hu⟩ := max_facts hf hF hθ hr
  have hθ' : -Bn < θ' := by linarith
  obtain ⟨hp', hr0', hG', hl', hu'⟩ := max_facts hf hF hθ' hr'
  by_contra hcon
  push_neg at hcon
  -- a = r' - θ', b = r - θ', c = r' - θ, d = r - θ
  have hlc := logconc_pair hf hA (a := r' - θ') (b := r - θ') (c := r' - θ) (d := r - θ)
    ⟨hl', hu'.le⟩ ⟨hl, hu.le⟩ (by linarith) (by linarith) (by ring) hG' hG
  have h1 := isMaxOn_iff.mp hr r' (mem_univ _)
  have h2 := isMaxOn_iff.mp hr' r (mem_univ _)
  rw [obj_eq, obj_eq] at h1 h2
  have hGb := G_nonneg hf (r - θ')
  have hGc := G_nonneg hf (r' - θ)
  -- r' is also a maximizer at θ
  have heq : r' * G f (r' - θ) = r * G f (r - θ) := by
    by_contra hne
    have hlt : r' * G f (r' - θ) < r * G f (r - θ) := lt_of_le_of_ne h1 hne
    have e1 : (r' * G f (r' - θ)) * (r' * G f (r' - θ')) < (r * G f (r - θ)) * (r' * G f (r' - θ')) :=
      mul_lt_mul_of_pos_right hlt hp'
    have e2 : (r' * G f (r' - θ)) * (r * G f (r - θ')) ≤ (r' * G f (r' - θ)) * (r' * G f (r' - θ')) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hr0'.le hGc)
    have e3 : r * r' * (G f (r' - θ') * G f (r - θ)) ≤ r * r' * (G f (r - θ') * G f (r' - θ)) :=
      mul_le_mul_of_nonneg_left hlc (mul_pos hr0 hr0').le
    nlinarith
  have hr'max : IsMaxOn (reserveObjective f θ) univ r' := by
    refine isMaxOn_iff.mpr fun y _ => ?_
    have := isMaxOn_iff.mp hr y (mem_univ _)
    rw [obj_eq] at this ⊢
    rw [obj_eq, heq]; exact this
  have := max_unique hf hA hF hθ hr hr'max
  linarith

end G80IAP

open G80IAP IncentiveAwarePricing.CORP in
theorem solution (d : ℕ) (Bn : ℝ) (f : ℝ → ℝ)
    (hf : NoiseStanding Bn f) (hA1 : Assumption1 Bn f)
    (hF : ∀ z, z < Bn → noiseCDF f z < 1)
    (x β βhat : Ctx d) (hβ : -Bn < ⟪x, β⟫) (hβhat : -Bn < ⟪x, βhat⟫)
    (rStar r : ℝ) (hrStar : IsMaxOn (reserveObjective f ⟪x, β⟫) Set.univ rStar)
    (hr : IsMaxOn (reserveObjective f ⟪x, βhat⟫) Set.univ r) :
    |rStar - r| ≤ |⟪x, β - βhat⟫| := by
  rw [inner_sub_right]
  rcases lt_trichotomy ⟪x, β⟫ ⟪x, βhat⟫ with h | h | h
  · have h1 := r_mono hf hA1 hF hβ h hrStar hr
    have h2 := z_anti hf hF hβ h hrStar hr
    rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)]
    linarith
  · rw [h] at hrStar ⊢
    rw [max_unique hf hA1 hF hβhat hrStar hr]; simp
  · have h1 := r_mono hf hA1 hF hβhat h hr hrStar
    have h2 := z_anti hf hF hβhat h hr hrStar
    rw [abs_of_nonneg (by linarith), abs_of_pos (by linarith)]
    linarith
