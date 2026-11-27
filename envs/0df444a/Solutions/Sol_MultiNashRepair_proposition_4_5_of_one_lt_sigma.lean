-- Prove2me | solution 1 for MultiNashRepair.proposition_4_5_of_one_lt_sigma
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:47:11.374685+00:00
-- url     : https://prove2.me/submissions/4e771ed0-6724-4c60-acd1-5f04d12cd8c1

import Mathlib
import Definitions.Def_MultiNashRepair_Controls
import Theorems.Thm_MultiNashRepair_controls_5_7
import Theorems.Thm_MultiNashRepair_lemma_5_9
import Theorems.Thm_MultiNashRepair_lemma_5_11
import Theorems.Thm_MultiNashRepair_theorem_5_8

open MultiNashRepair

theorem MNR45_lp (η d Z P ς ς' H G0 au Q Su μ LP Lr : ℝ)
    (hη0 : 0 < η) (hη1 : η ≤ 1/8) (hηd : η ≤ d/48) (hd : 0 < d)
    (hZ0 : 0 ≤ Z) (hZ1 : Z ≤ 1) (hP0 : 1 - η*Z ≤ P) (hP1 : P ≤ 1)
    (hς' : P*((1+η*Z)*ς + η*μ) ≤ ς')
    (hH : 0 < H) (hau0 : 0 ≤ au) (hau1 : au ≤ 1) (hQ : 0 ≤ Q)
    (hSu : Su = G0 + H*(1-au) + au*Q*H^2/(1+Q*H)) (hSuhi : Su ≤ 13/5)
    (hμ : μ = Su - ς - d) (hμd : d ≤ μ) (hS' : 2*d ≤ Su) (hG0d : 2*d ≤ G0)
    (hLP : -(1-P)/P ≤ LP) (hLr : -(Q*H*(1-P))/(1+Q*P*H) ≤ Lr) :
    η*d/2 ≤ (ς' + 2*d - G0)/P - (ς + 2*d - G0) + H*(1-au)*LP + H*au*Lr := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 - P := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by linarith
  have hηZ : η*Z ≤ η := by nlinarith only [hη0, hZ1]
  have hδη : δ ≤ η*Z := by linarith
  have hδ1 : δ ≤ 1/8 := by linarith
  have hPpos : 0 < P := by linarith
  have hQH : 0 ≤ Q*H := mul_nonneg hQ hH.le
  have hQPH : 0 < 1 + Q*P*H := by nlinarith only [hQH, hPpos]
  have hQH1 : 0 < 1 + Q*H := by linarith
  -- 1/P ≤ 1 + 2δ
  have hPδ : P = 1 - δ := by linarith
  have h12 : 0 ≤ δ*(1 - 2*δ) := mul_nonneg hδ0 (by linarith)
  have hinvP : 1/P ≤ 1 + 2*δ := by
    rw [div_le_iff₀ hPpos, hPδ]; nlinarith only [h12]
  -- the three pieces
  have t1 : (1+η*Z)*ς + η*μ + (2*d - G0)/P ≤ (ς' + 2*d - G0)/P := by
    have : (1+η*Z)*ς + η*μ ≤ ς'/P := by
      rw [le_div_iff₀ hPpos]; linarith [show ((1+η*Z)*ς + η*μ)*P = P*((1+η*Z)*ς + η*μ) by ring]
    have e : (ς' + 2*d - G0)/P = ς'/P + (2*d - G0)/P := by ring
    linarith
  have t2 : -(H*(1-au))*(δ/P) ≤ H*(1-au)*LP := by
    have h := mul_le_mul_of_nonneg_left hLP (mul_nonneg hH.le (by linarith : (0:ℝ) ≤ 1 - au))
    rw [hδ]; linarith [show H*(1-au)*(-(1-P)/P) = -(H*(1-au))*((1-P)/P) by ring]
  have t3 : -(H*au)*(Q*H*δ/(1+Q*P*H)) ≤ H*au*Lr := by
    have h := mul_le_mul_of_nonneg_left hLr (mul_nonneg hH.le hau0)
    rw [hδ]; linarith [show H*au*(-(Q*H*(1-P))/(1+Q*P*H)) = -(H*au)*(Q*H*(1-P)/(1+Q*P*H)) by ring]
  -- bound the δ-terms by δ(1+2δ)(Su - 2d)
  have hG : 0 ≤ G0 - 2*d + H*(1-au) := by
    have := mul_nonneg hH.le (by linarith : (0:ℝ) ≤ 1 - au)
    linarith
  have k1 : (G0 - 2*d)*(1/P - 1) + H*(1-au)*(δ/P) ≤ (1 + 2*δ)*δ*(G0 - 2*d + H*(1-au)) := by
    have e1 : 1/P - 1 = δ/P := by rw [hδ]; field_simp
    rw [e1]
    have : δ/P ≤ (1 + 2*δ)*δ := by
      rw [div_le_iff₀ hPpos, hPδ]; nlinarith only [h12, hδ0]
    have e2 : (G0 - 2*d)*(δ/P) + H*(1-au)*(δ/P) = (δ/P)*(G0 - 2*d + H*(1-au)) := by ring
    rw [e2]
    exact mul_le_mul_of_nonneg_right this hG
  have k2 : H*au*(Q*H*δ/(1+Q*P*H)) ≤ (1 + 2*δ)*δ*(au*Q*H^2/(1+Q*H)) := by
    have hfrac : 1/(1+Q*P*H) ≤ (1+2*δ)/(1+Q*H) := by
      rw [div_le_div_iff₀ hQPH hQH1]
      have : P = 1 - δ := by linarith
      rw [this]; nlinarith only [mul_nonneg hQH hδ0, mul_nonneg (mul_nonneg hQH hδ0) (by linarith : (0:ℝ) ≤ 1 - 2*δ), hδ0]
    have hnn : 0 ≤ H*au*Q*H*δ := by positivity
    have := mul_le_mul_of_nonneg_left hfrac hnn
    have e1 : H*au*(Q*H*δ/(1+Q*P*H)) = H*au*Q*H*δ*(1/(1+Q*P*H)) := by ring
    have e2 : (1 + 2*δ)*δ*(au*Q*H^2/(1+Q*H)) = H*au*Q*H*δ*((1+2*δ)/(1+Q*H)) := by ring
    rw [e1, e2]; exact this
  have hS'' : (1 + 2*δ)*δ*(G0 - 2*d + H*(1-au)) + (1 + 2*δ)*δ*(au*Q*H^2/(1+Q*H))
      = (1 + 2*δ)*δ*(Su - 2*d) := by rw [hSu]; ring
  have hSd : 0 ≤ Su - 2*d := by linarith
  have k3 : (1 + 2*δ)*δ*(Su - 2*d) ≤ η*Z*(Su - 2*d) + 2*η^2*(Su - 2*d) := by
    have h1 : δ*(Su - 2*d) ≤ η*Z*(Su - 2*d) := mul_le_mul_of_nonneg_right hδη hSd
    have h2 : δ^2 ≤ η^2 := by nlinarith only [hδ0, hδη, hηZ]
    have h3 : 2*δ^2*(Su - 2*d) ≤ 2*η^2*(Su - 2*d) := by nlinarith only [h2, hSd]
    nlinarith only [h1, h3]
  have k4 : 2*η^2*(Su - 2*d) ≤ η*d/2 := by
    have : η*(Su - 2*d) ≤ d/4 := by nlinarith only [hηd, hSuhi, hη0, hSd, hd]
    nlinarith only [this, hη0]
  -- main term
  have k5 : η*Z*ς + η*μ - η*Z*(Su - 2*d) ≥ η*d := by
    have : η*Z*ς + η*μ - η*Z*(Su - 2*d) = η*(1-Z)*μ + η*Z*d := by rw [hμ]; ring
    rw [this]
    nlinarith only [mul_le_mul_of_nonneg_left hμd (mul_nonneg hη0.le (by linarith : (0:ℝ) ≤ 1 - Z)), hη0, hZ0, hd]
  have e3 : (1+η*Z)*ς + η*μ + (2*d - G0)/P - (ς + 2*d - G0)
      = η*Z*ς + η*μ - (G0 - 2*d)*(1/P - 1) := by ring
  nlinarith only [t1, t2, t3, k1, k2, hS'', k3, k4, k5, e3]

theorem MNR45_rep (d c t H E ς ς' G0 A Ku D u : ℝ)
    (hd : 0 < d) (hu0 : 0 < u) (hu1 : u ≤ 1/288) (hud : u ≤ d/200)
    (hclo : 1 - u ≤ c) (hc1 : c < 1) (htlo : 7/12*u ≤ t)
    (hH0 : 0 < H) (hH1 : H ≤ 3/5) (hHL : (1-c)*H ≤ c*t)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 3*u^3/25)
    (hς' : c*ς + D - E ≤ ς')
    (hKu : Ku = G0 + H*(D - (1-c)*G0)/(c*t) + H*(H+t)/t*A)
    (hKς : 6*d ≤ Ku - ς) :
    3*d*(1-c) ≤ H*(ς' + 2*d - G0)/(c*(H+t)) - (ς + 2*d - G0) + H*A := by
  have ht0 : 0 < t := by linarith
  have hc0 : 0 < c := by linarith
  have hHt : 0 < H + t := by linarith
  have hden : 0 < c*(H+t) := by positivity
  have h1 : c*H*(H+t)*A = c*t*(Ku - G0) - H*(D - (1-c)*G0) := by
    rw [hKu]; field_simp; ring
  have e1 : c*(H+t)*(H*(ς' + 2*d - G0)/(c*(H+t))) = H*(ς' + 2*d - G0) := by field_simp
  have hX : c*(H+t)*(H*(ς' + 2*d - G0)/(c*(H+t)) - (ς + 2*d - G0) + H*A)
      = H*(ς' - (c*ς + D - E)) - H*E + c*t*(Ku - ς) + 2*d*((1-c)*H - c*t) := by
    calc c*(H+t)*(H*(ς' + 2*d - G0)/(c*(H+t)) - (ς + 2*d - G0) + H*A)
        = c*(H+t)*(H*(ς' + 2*d - G0)/(c*(H+t))) - c*(H+t)*(ς + 2*d - G0) + c*H*(H+t)*A := by ring
      _ = H*(ς' + 2*d - G0) - c*(H+t)*(ς + 2*d - G0) + (c*t*(Ku - G0) - H*(D - (1-c)*G0)) := by
          rw [e1, h1]
      _ = _ := by ring
  have w0 : 0 < 1 - c := by linarith
  have w1 : 1 - c ≤ u := by linarith
  have p1 : 0 ≤ H*(ς' - (c*ς + D - E)) := mul_nonneg hH0.le (by linarith)
  have p2 : 6*d*(c*t) ≤ c*t*(Ku - ς) := by
    have := mul_le_mul_of_nonneg_left hKς (by positivity : (0:ℝ) ≤ c*t)
    linarith
  have p3 : -(d*(c*t)) ≤ d*((1-c)*H)*(2 - 3*c) := by
    have h23 : -1 ≤ 2 - 3*c := by linarith
    have hwH : 0 ≤ (1-c)*H := by positivity
    have := mul_le_mul_of_nonneg_left h23 (mul_nonneg hd.le hwH)
    have := mul_le_mul_of_nonneg_left hHL hd.le
    nlinarith only [this, ‹d * ((1 - c) * H) * -1 ≤ d * ((1 - c) * H) * (2 - 3 * c)›]
  have p4 : 3*d*(1-c)*(c*t) ≤ d*(c*t)/96 := by
    have : 3*(1-c) ≤ 1/96 := by linarith
    have := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ d*(c*t))
    nlinarith only [this]
  have p5 : H*E ≤ 9*u^3/125 := by
    have := mul_le_mul hH1 hE1 hE0 (by norm_num)
    nlinarith only [this]
  have p6 : 9*u^3/125 ≤ d*(c*t) := by
    have hct : 1/2*u ≤ c*t := by nlinarith only [hclo, htlo, hu0, hu1, mul_nonneg hu0.le hu0.le]
    have hu2 : u^2 ≤ d/200 * (1/288) := by nlinarith only [hu0, hu1, hud]
    have : 9*u^3/125 ≤ d*(1/2*u) := by nlinarith only [hu2, hu0, hd]
    nlinarith only [this, mul_le_mul_of_nonneg_left hct hd.le]
  have key : 3*d*(1-c)*(c*(H+t)) ≤ c*(H+t)*(H*(ς' + 2*d - G0)/(c*(H+t)) - (ς + 2*d - G0) + H*A) := by
    rw [hX]
    nlinarith only [p1, p2, p3, p4, p5, p6, mul_pos hd (mul_pos hc0 ht0)]
  rw [mul_comm (c*(H+t))] at key
  exact le_of_mul_le_mul_right key hden

set_option maxHeartbeats 4000000 in
theorem solution {σ : ℚ} (ctrl : Controls σ) (hσ1 : 1 < σ) {m : ℕ} (hm : ctrl.m0 ≤ m) (ς H : ℝ)
    (hH0 : 0 < H) (hHL : H ≤ ctrl.knobs.L0) (hς : ς < σ) :
    let k := ctrl.knobs
    let d : ℝ := ctrl.d
    let η : ℝ := ctrl.η
    let mu := ctrl.mu ς H
    (∀ Z P ς' H' : ℝ, 0 ≤ Z → Z ≤ 1 → 1 - η * Z ≤ P → P ≤ 1 →
      P * ((1 + η * Z) * ς + η * mu) ≤ ς' → H' = P * H →
      η * d / 2 ≤ H * (k.Phihat d ς' H' - k.Phihat d ς H)) ∧
    (∀ E ς' H' : ℝ, 0 ≤ E → E ≤ 120 * (ctrl.u : ℝ) / m →
      k.c * ς + k.Dsh H - E ≤ ς' → H' = k.c * (H + k.t) →
      3 * d * (1 - k.c) ≤ H * (k.Phihat d ς' H' - k.Phihat d ς H)) ∧
    0 < η * d / 2 ∧ 0 < 3 * d * (1 - k.c) := by
  dsimp only
  -- scalar constants
  have hdq : (0:ℚ) < ctrl.d := ctrl.d_pos
  have hd : (0:ℝ) < ctrl.d := by exact_mod_cast hdq
  have huq : ctrl.u = 1/2 * min (1/144) (ctrl.d/100) := rfl
  have hηq : ctrl.η = 1/2 * min (1/4) (ctrl.d/24) := rfl
  have hu0q : (0:ℚ) < ctrl.u := by rw [huq]; have := lt_min (by norm_num : (0:ℚ) < 1/144) (by positivity : (0:ℚ) < ctrl.d/100); linarith
  have hu1q : ctrl.u ≤ 1/288 := by rw [huq]; have := min_le_left (1/144 : ℚ) (ctrl.d/100); linarith
  have hudq : ctrl.u ≤ ctrl.d/200 := by rw [huq]; have := min_le_right (1/144 : ℚ) (ctrl.d/100); linarith
  have hη0q : (0:ℚ) < ctrl.η := by rw [hηq]; have := lt_min (by norm_num : (0:ℚ) < 1/4) (by positivity : (0:ℚ) < ctrl.d/24); linarith
  have hη1q : ctrl.η ≤ 1/8 := by rw [hηq]; have := min_le_left (1/4 : ℚ) (ctrl.d/24); linarith
  have hηdq : ctrl.η ≤ ctrl.d/48 := by rw [hηq]; have := min_le_right (1/4 : ℚ) (ctrl.d/24); linarith
  have hu0 : (0:ℝ) < ctrl.u := by exact_mod_cast hu0q
  have hu1 : (ctrl.u:ℝ) ≤ 1/288 := by
    have := (Rat.cast_le (K := ℝ)).mpr hu1q; push_cast at this; exact this
  have hud : (ctrl.u:ℝ) ≤ ctrl.d/200 := by exact_mod_cast hudq
  have hη0 : (0:ℝ) < ctrl.η := by exact_mod_cast hη0q
  have hη1 : (ctrl.η:ℝ) ≤ 1/8 := by
    have := (Rat.cast_le (K := ℝ)).mpr hη1q; push_cast at this; exact this
  have hηd : (ctrl.η:ℝ) ≤ ctrl.d/48 := by exact_mod_cast hηdq
  have hf1 : (7/12:ℝ) ≤ ctrl.f0 := by
    have := (Rat.cast_le (K := ℝ)).mpr ctrl.f0_ge; push_cast at this; exact this
  have hf2 : (ctrl.f0:ℝ) ≤ 3/5 := by
    have := (Rat.cast_le (K := ℝ)).mpr ctrl.f0_le; push_cast at this; exact this
  have hF0 : (0:ℝ) < ctrl.f0 := by linarith
  have hσ1r : (1:ℝ) < σ := by exact_mod_cast hσ1
  have hσs : sigmaStar < 2 := MultiNashRepair.theorem_5_8.2.2.1.2.1
  have hdres := ctrl.d_reserve
  have hd8 : (ctrl.d:ℝ) < 1/8 := by linarith
  have hfinv := ctrl.f0_inv
  have hfU := ctrl.f0_U
  -- imported milestones
  have hC := MultiNashRepair.controls_5_7 (ctrl.f0:ℝ) (ctrl.u:ℝ) hf1 hf2 hu0 (by linarith)
  have h511 := MultiNashRepair.lemma_5_11 (ctrl.f0:ℝ) (ctrl.u:ℝ) hf1 hf2 hu0 (by linarith)
  have h59 := MultiNashRepair.lemma_5_9.1 (ctrl.f0:ℝ) hF0 (by linarith)
  dsimp only at hC h511
  have hk : ctrl.knobs = ⟨(ctrl.f0:ℝ), (ctrl.u:ℝ)⟩ := rfl
  have hmu : ctrl.mu ς H = (⟨(ctrl.f0:ℝ), (ctrl.u:ℝ)⟩ : Knobs).Su H - ς - ctrl.d := rfl
  rw [hmu]
  rw [hk] at hHL ⊢
  set K : Knobs := ⟨(ctrl.f0:ℝ), (ctrl.u:ℝ)⟩ with hK
  obtain ⟨⟨hR0pos, hR0lt, hQ1, hQ2, hau0, hau1, hL0f, hQL0⟩, hSuB⟩ := hC
  obtain ⟨hKu0, -, hKu⟩ := h511
  have eF : K.f0 = ctrl.f0 := rfl
  have eU : K.u = ctrl.u := rfl
  have hc : K.c = 1 - ctrl.u + (ctrl.u:ℝ)^2/2 - (ctrl.u:ℝ)^3 := rfl
  have ht : K.t = ctrl.f0 * ctrl.u := rfl
  have hcpos : 0 < K.c := by rw [hc]; nlinarith only [hu0, hu1]
  have hclo : 1 - (ctrl.u:ℝ) ≤ K.c := by rw [hc]; nlinarith only [hu0, hu1]
  have hc1 : K.c < 1 := by rw [hc]; nlinarith only [hu0, hu1]
  have htpos : 0 < K.t := by rw [ht]; positivity
  have hHL0 : H ≤ K.c * K.t / (1 - K.c) := hHL
  have hHF : H < ctrl.f0 := lt_of_le_of_lt hHL hL0f
  have hG0lo : 1/(ctrl.f0:ℝ) - 32 * ctrl.u ≤ K.G0 := by
    have h := hKu 0 le_rfl (by linarith)
    rw [hKu0] at h
    have e : Kf (ctrl.f0) 0 = 1/(ctrl.f0:ℝ) := by
      unfold Kf; rw [div_eq_div_iff (by positivity) (by positivity)]; ring
    rw [e] at h
    linarith [(abs_le.mp h).1]
  have hif : (5/3:ℝ) ≤ 1/(ctrl.f0:ℝ) := by rw [le_div_iff₀ hF0]; linarith
  have hSuId : K.Su H = K.G0 + H*(1-K.au) + K.au*K.Q*H^2/(1+K.Q*H) := by
    have hQH : 0 < 1 + K.Q*H := by nlinarith only [hQ1, hH0]
    simp only [Knobs.Su, Knobs.Cu, Knobs.G0, Knobs.au]
    field_simp; ring
  have hQH : 0 < 1 + K.Q*H := by nlinarith only [hQ1, hH0]
  have hSuG : K.G0 ≤ K.Su H := by
    rw [hSuId]
    have := mul_nonneg hH0.le (by linarith : (0:ℝ) ≤ 1 - K.au)
    have : 0 ≤ K.au*K.Q*H^2/(1+K.Q*H) := by
      apply div_nonneg _ hQH.le; apply mul_nonneg (mul_nonneg hau0.le (by linarith)) (sq_nonneg H)
    linarith
  refine ⟨?_, ?_, by positivity, ?_⟩
  · intro Z P ς' H' hZ0 hZ1 hP0 hP1 hς' hH'
    subst hH'
    have hPpos : 0 < P := by nlinarith only [hP0, hη1, hZ1, hZ0, hη0]
    have l1 : Real.log (P*H/K.f0) = Real.log P + Real.log (H/K.f0) := by
      rw [mul_div_assoc, Real.log_mul hPpos.ne' (by rw [eF]; positivity)]
    have hQPH : 0 < 1 + K.Q*P*H := by
      have : 0 ≤ K.Q*P*H := by have := hQ1; positivity
      linarith
    have l2 : Real.log (1 + K.Q*(P*H)) = Real.log ((1+K.Q*P*H)/(1+K.Q*H)) + Real.log (1+K.Q*H) := by
      rw [Real.log_div hQPH.ne' hQH.ne', mul_assoc]; ring
    have eq1 : H*(K.Phihat ctrl.d ς' (P*H) - K.Phihat ctrl.d ς H)
        = (ς' + 2*ctrl.d - K.G0)/P - (ς + 2*ctrl.d - K.G0) + H*(1-K.au)*Real.log P
          + H*K.au*Real.log ((1+K.Q*P*H)/(1+K.Q*H)) := by
      simp only [Knobs.Phihat, Knobs.Phiu, Knobs.Fu]
      rw [l1, l2]; field_simp; ring
    rw [eq1]
    have hLP : -(1-P)/P ≤ Real.log P := by
      have := Real.one_sub_inv_le_log_of_pos hPpos
      have e : 1 - P⁻¹ = -(1-P)/P := by field_simp; ring
      linarith
    have hLr : -(K.Q*H*(1-P))/(1+K.Q*P*H) ≤ Real.log ((1+K.Q*P*H)/(1+K.Q*H)) := by
      have := Real.one_sub_inv_le_log_of_pos (div_pos hQPH hQH)
      have e : 1 - ((1+K.Q*P*H)/(1+K.Q*H))⁻¹ = -(K.Q*H*(1-P))/(1+K.Q*P*H) := by
        field_simp; ring
      linarith
    have hSuhi : K.Su H ≤ 13/5 := by
      have := hSuB H hH0.le hHL; linarith
    have hμd : (ctrl.d:ℝ) ≤ K.Su H - ς - ctrl.d := by linarith
    exact MNR45_lp ctrl.η ctrl.d Z P ς ς' H K.G0 K.au K.Q (K.Su H) (K.Su H - ς - ctrl.d)
      (Real.log P) (Real.log ((1+K.Q*P*H)/(1+K.Q*H))) hη0 hη1 hηd hd hZ0 hZ1 hP0 hP1 hς' hH0
      hau0.le hau1.le (by linarith) hSuId hSuhi rfl hμd (by linarith) (by linarith) hLP hLr
  · intro E ς' H' hE0 hE1 hς' hH'
    subst hH'
    have hHt : 0 < H + K.t := by linarith
    have hcHt : 0 < K.c*(H+K.t) := by positivity
    have l1 : Real.log (K.c*(H+K.t)/K.f0) = Real.log (K.c*(H+K.t)/H) + Real.log (H/K.f0) := by
      rw [← Real.log_mul (by positivity) (by rw [eF]; positivity)]
      congr 1; rw [eF]; field_simp
    have hQcH : 0 < 1 + K.Q*(K.c*(H+K.t)) := by
      have : 0 ≤ K.Q*(K.c*(H+K.t)) := by have := hQ1; positivity
      linarith
    have l2 : Real.log (1 + K.Q*(K.c*(H+K.t))) = Real.log ((1+K.Q*(K.c*(H+K.t)))/(1+K.Q*H))
        + Real.log (1+K.Q*H) := by
      rw [Real.log_div hQcH.ne' hQH.ne']; ring
    set A := (1-K.au)*Real.log (K.c*(H+K.t)/H) + K.au*Real.log ((1+K.Q*(K.c*(H+K.t)))/(1+K.Q*H)) with hA
    have eq2 : H*(K.Phihat ctrl.d ς' (K.c*(H+K.t)) - K.Phihat ctrl.d ς H)
        = H*(ς' + 2*ctrl.d - K.G0)/(K.c*(H+K.t)) - (ς + 2*ctrl.d - K.G0) + H*A := by
      simp only [Knobs.Phihat, Knobs.Phiu, Knobs.Fu]
      rw [l1, l2, hA]; field_simp; ring
    rw [eq2]
    have hKuH : K.Ku H = K.G0 + H*(K.Dsh H - (1-K.c)*K.G0)/(K.c*K.t) + H*(H+K.t)/K.t*A := by
      simp only [Knobs.Ku, if_neg hH0.ne', hA]
    have hKf : U ctrl.f0 ≤ Kf ctrl.f0 H := h59.2 (Set.mem_image_of_mem _ ⟨hH0.le, hHF.le⟩)
    have hKuB := (abs_le.mp (hKu H hH0.le hHL)).1
    have hKς : 6*(ctrl.d:ℝ) ≤ K.Ku H - ς := by linarith
    have hmpos : (0:ℝ) < m := by
      have h1 := ctrl.m0_ge_u
      have : (0:ℝ) < 1000 / ((uOf ctrl.d : ℚ) : ℝ)^2 := by
        have : ((uOf ctrl.d : ℚ) : ℝ) = ctrl.u := rfl
        rw [this]; positivity
      have : (ctrl.m0:ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have hE1' : E ≤ 3*(ctrl.u:ℝ)^3/25 := by
      have h1 := ctrl.m0_ge_u
      have e : ((uOf ctrl.d : ℚ) : ℝ) = ctrl.u := rfl
      rw [e] at h1
      have hm' : (ctrl.m0:ℝ) ≤ m := by exact_mod_cast hm
      have hmu2 : 1000 / (ctrl.u:ℝ)^2 ≤ m := le_trans h1 hm'
      have : 120 * (ctrl.u:ℝ) / m ≤ 120 * ctrl.u / (1000 / (ctrl.u:ℝ)^2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hmu2
      have e2 : 120 * (ctrl.u:ℝ) / (1000 / (ctrl.u:ℝ)^2) = 3*(ctrl.u:ℝ)^3/25 := by
        field_simp; ring
      linarith
    have hHL' : (1-K.c)*H ≤ K.c*K.t := by
      have := (le_div_iff₀ (by linarith : (0:ℝ) < 1 - K.c)).mp hHL0
      linarith
    exact MNR45_rep ctrl.d K.c K.t H E ς ς' K.G0 A (K.Ku H) (K.Dsh H) ctrl.u hd hu0 hu1 hud
      hclo hc1 (by rw [ht]; nlinarith only [hf1, hu0]) hH0 (by linarith) hHL' hE0 hE1' hς'
      hKuH hKς
  · have : 0 < 1 - K.c := by linarith
    positivity
