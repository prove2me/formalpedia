-- Prove2me | solution 1 for MultiNashRepair.lemma_5_11
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:30:22.519846+00:00
-- url     : https://prove2.me/submissions/6c004eea-1a7b-4532-a35b-8ea247b79418

import Mathlib
import Definitions.Def_MultiNashRepair_ScalarCertificate
import Definitions.Def_MultiNashRepair_Knobs

open MultiNashRepair

theorem MNR511_absmul {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

theorem MNR511_abs2 {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a + b| ≤ A + B :=
  (abs_add_le _ _).trans (add_le_add ha hb)

theorem MNR511_abssub {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a - b| ≤ A + B := by
  rw [sub_eq_add_neg]; exact MNR511_abs2 ha (by rwa [abs_neg])

theorem MNR511_abs3 {a b c A B C : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) :
    |a + b + c| ≤ A + B + C :=
  MNR511_abs2 (MNR511_abs2 ha hb) hc

theorem MNR511_alg (f u c t Q R0 G0 au H v p : ℝ)
    (hf1 : 7/12 ≤ f) (hf2 : f ≤ 3/5) (hu0 : 0 < u) (hu1 : u ≤ 1/16)
    (hclo : 1 - u ≤ c) (hchi : c ≤ 1) (ht : t = f*u)
    (hvlo : 1 - u/2 ≤ v) (hvhi : v ≤ 1) (hp1 : 1 ≤ p) (hpu : p ≤ 1 + u)
    (hG0 : G0 = 1 + R0) (hR0lo : 1/f - 1 - u/5 ≤ R0) (hR0hi : R0 ≤ 1/f - 1)
    (hQlo : 1/f - 7*u/2 ≤ Q) (hQhi : Q ≤ 1/f) (hQ1 : 1 ≤ Q) (hau : au = R0*(Q-1))
    (hH0 : 0 ≤ H) (hHf : H ≤ f) :
    |G0 + (H*p*G0 + p*Q*H^2 - H*v*G0/(f*c)) + (1-au)*(H - H*(H+t)*v/f)
       + au*(H*(H+t)*Q*(c*f - v*H)/(f*(1+Q*H))) - Kf f H| ≤ 20*u := by
  have hf0 : 0 < f := by linarith
  have hcpos : 0 < c := by linarith
  have hif : 1/f ≤ 12/7 := by rw [div_le_iff₀ hf0]; linarith
  have hif' : 5/3 ≤ 1/f := by rw [le_div_iff₀ hf0]; linarith
  have hQf : Q * f ≤ 1 := (le_div_iff₀ hf0).mp hQhi
  have hQH : 0 < 1 + Q*H := by nlinarith only [hQ1, hH0]
  have hfH : 0 < f + H := by linarith
  -- atoms
  have aH : |H| ≤ 3/5 := abs_le.mpr ⟨by linarith, by linarith⟩
  have ap1 : |p - 1| ≤ u := abs_le.mpr ⟨by linarith, by linarith⟩
  have aG0 : |G0| ≤ 12/7 := abs_le.mpr ⟨by linarith, by linarith⟩
  have aT1 : |G0 - 1/f| ≤ u/5 := abs_le.mpr ⟨by linarith, by linarith⟩
  have aQ : |Q| ≤ 12/7 := abs_le.mpr ⟨by linarith, by linarith⟩
  have aQf : |Q - 1/f| ≤ 7*u/2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have av1 : |v - 1| ≤ u/2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have a1v : |1 - v| ≤ u/2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have av : |v| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have ac : |c| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have ac1 : |1 - c| ≤ u := abs_le.mpr ⟨by linarith, by linarith⟩
  have aif : |1/f| ≤ 12/7 := abs_le.mpr ⟨by linarith, by linarith⟩
  have af : |f| ≤ 3/5 := abs_le.mpr ⟨by linarith, by linarith⟩
  have afH : |f + H| ≤ 6/5 := abs_le.mpr ⟨by linarith, by linarith⟩
  have afmH : |f - H| ≤ 3/5 := abs_le.mpr ⟨by linarith, by linarith⟩
  have aic : |1/c| ≤ 16/15 := by
    rw [abs_of_pos (by positivity)]
    rw [div_le_iff₀ hcpos]; linarith
  have aHf : |H/f| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), div_le_one hf0]; exact hHf
  have a1Hf : |1 - H/f| ≤ 1 := by
    have : H/f ≤ 1 := by rw [div_le_one hf0]; exact hHf
    have : 0 ≤ H/f := by positivity
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have at' : |t| ≤ 3*u/5 := by
    rw [ht]; exact abs_le.mpr ⟨by nlinarith only [hu0, hf0], by nlinarith only [hu0, hf2]⟩
  have hR0pos : 0 < R0 := by linarith
  have hau0 : 0 ≤ au := by rw [hau]; exact mul_nonneg hR0pos.le (by linarith)
  have hau1 : au ≤ 1 := by
    rw [hau]
    have h1 : R0 ≤ 5/7 := by linarith
    have h2 : Q - 1 ≤ 5/7 := by linarith
    nlinarith only [h1, h2, hR0pos, hQ1]
  have aau : |au| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have a1au : |1 - au| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  set as := (1/f - 1)^2 with has
  have hda : au - as = (R0 - (1/f - 1))*(Q - 1) + (1/f - 1)*(Q - 1/f) := by
    rw [hau, has]; ring
  have ada : |au - as| ≤ 27*u/10 := by
    rw [hda]
    have h1 : |R0 - (1/f - 1)| ≤ u/5 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |Q - 1| ≤ 5/7 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h3 : |1/f - 1| ≤ 5/7 := abs_le.mpr ⟨by linarith, by linarith⟩
    have := MNR511_abs2 (MNR511_absmul h1 h2) (MNR511_absmul h3 aQf)
    linarith
  have ada' : |as - au| ≤ 27*u/10 := by rw [abs_sub_comm]; exact ada
  -- Kf in expanded form
  have IK : Kf f H = 1/f + H/f + H^2/f - H/f^2 + (1-as)*(H - H^2/f)
      + as*(H^2*(f-H)/(f*(f+H))) := by
    unfold Kf; rw [has]; field_simp; ring
  -- decomposition
  have hN6 : H*(H+t)*Q*(c*f - v*H)/(f*(1+Q*H)) - H^2*(f-H)/(f*(f+H))
      = (H/f) * (H*Q*(f+H)*(H*(1-v) - f*(1-c)) - H*(f-H)*(1-Q*f)
          + t*Q*(c*f - v*H)*(f+H)) * (1/((1+Q*H)*(f+H))) := by
    field_simp; ring
  have hdec : G0 + (H*p*G0 + p*Q*H^2 - H*v*G0/(f*c)) + (1-au)*(H - H*(H+t)*v/f)
       + au*(H*(H+t)*Q*(c*f - v*H)/(f*(1+Q*H))) - Kf f H
      = (G0 - 1/f) + H*((p-1)*G0 + (G0 - 1/f)) + (H*H)*((p-1)*Q + (Q - 1/f))
        - (H/f)*((((v-1)*G0 + (G0 - 1/f)) + (1-c)*(1/f))*(1/c))
        + ((1-au)*((H/f)*(H*(1-v) - t*v)) + (as - au)*(H*(1 - H/f)))
        + (au*(H*(H+t)*Q*(c*f - v*H)/(f*(1+Q*H)) - H^2*(f-H)/(f*(f+H)))
            + (au - as)*((H/f)*H*((f-H)/(f+H)))) := by
    rw [IK]; field_simp; ring
  rw [hdec, hN6]
  -- bounds on the pieces
  have b2 := MNR511_absmul aH (MNR511_abs2 (MNR511_absmul ap1 aG0) aT1)
  have b3 := MNR511_absmul (MNR511_absmul aH aH) (MNR511_abs2 (MNR511_absmul ap1 aQ) aQf)
  have b4 := MNR511_absmul aHf (MNR511_absmul
    (MNR511_abs2 (MNR511_abs2 (MNR511_absmul av1 aG0) aT1) (MNR511_absmul ac1 aif)) aic)
  have b5 := MNR511_abs2 (MNR511_absmul a1au (MNR511_absmul aHf
      (MNR511_abssub (MNR511_absmul aH a1v) (MNR511_absmul at' av))))
    (MNR511_absmul ada' (MNR511_absmul aH a1Hf))
  have a1Qf : |1 - Q*f| ≤ 3/5*(7*u/2) := by
    have e : 1 - Q*f = f*(1/f - Q) := by field_simp
    rw [e]; exact MNR511_absmul af (by rw [abs_sub_comm]; exact aQf)
  have aN6 := MNR511_abs2 (MNR511_abssub
      (MNR511_absmul (MNR511_absmul (MNR511_absmul aH aQ) afH)
        (MNR511_abssub (MNR511_absmul aH a1v) (MNR511_absmul af ac1)))
      (MNR511_absmul (MNR511_absmul aH afmH) a1Qf))
    (MNR511_absmul (MNR511_absmul (MNR511_absmul at' aQ)
      (MNR511_abssub (MNR511_absmul ac af) (MNR511_absmul av aH))) afH)
  have aden : |1/((1+Q*H)*(f+H))| ≤ 12/7 := by
    rw [abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
    have h1 : 1 ≤ 1 + Q*H := by nlinarith only [hQ1, hH0]
    have h2 : (f+H) ≤ (1+Q*H)*(f+H) := by nlinarith only [h1, hfH]
    linarith
  have aY : |(H/f)*H*((f-H)/(f+H))| ≤ 1*(3/5)*1 := by
    have : |(f-H)/(f+H)| ≤ 1 := by
      rw [abs_le]; constructor
      · rw [le_div_iff₀ hfH]; linarith
      · rw [div_le_one hfH]; linarith
    exact MNR511_absmul (MNR511_absmul aHf aH) this
  have b6 := MNR511_abs2 (MNR511_absmul aau (MNR511_absmul (MNR511_absmul aHf aN6) aden))
    (MNR511_absmul ada aY)
  have b4' : |-((H/f)*((((v-1)*G0 + (G0 - 1/f)) + (1-c)*(1/f))*(1/c)))|
      ≤ 1 * ((u / 2 * (12 / 7) + u / 5 + u * (12 / 7)) * (16 / 15)) := by
    rw [abs_neg]; exact b4
  have tot := MNR511_abs2 (MNR511_abs2 (MNR511_abs2 (MNR511_abs2 (MNR511_abs2 aT1 b2) b3) b4') b5) b6
  rw [sub_eq_add_neg _ ((H/f)*((((v-1)*G0 + (G0 - 1/f)) + (1-c)*(1/f))*(1/c)))]
  refine tot.trans ?_
  nlinarith only [hu0]

theorem MNR511_core (f u c t β Q R0 G0 au H : ℝ)
    (hf1 : 7/12 ≤ f) (hf2 : f ≤ 3/5) (hu0 : 0 < u) (hu1 : u ≤ 1/16)
    (hc : c = 1 - u + u^2/2 - u^3) (ht : t = f*u) (hβ : β = c*t*(1+u-u^2))
    (hG0 : G0 = 1 + R0) (hR0lo : 1/f - 1 - u/5 ≤ R0) (hR0hi : R0 ≤ 1/f - 1)
    (hQlo : 1/f - 7*u/2 ≤ Q) (hQhi : Q ≤ 1/f) (hQ1 : 1 ≤ Q)
    (hau : au = R0*(Q-1))
    (hH0 : 0 < H) (hHL : H ≤ c*t/(1-c)) :
    |G0 + H*(β*(G0+Q*H) - (1-c)*G0)/(c*t) + H*(H+t)/t*((1-au)*Real.log (c*(H+t)/H)
      + au*Real.log ((1+Q*(c*(H+t)))/(1+Q*H))) - Kf f H| ≤ 32*u := by
  have hf0 : 0 < f := by linarith
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = 1 - u/2 + u^2 := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 1 + u - u^2 := ⟨_, rfl⟩
  have hw : 1 - c = u * v := by rw [hc, hv]; ring
  have hvlo : 1 - u/2 ≤ v := by rw [hv]; nlinarith only [hu0]
  have hvhi : v ≤ 1 := by rw [hv]; nlinarith only [hu0, hu1]
  have hcpos : 0 < c := by rw [hc]; nlinarith only [hu0, hu1]
  have hclo : 1 - u ≤ c := by rw [hc]; nlinarith only [hu0, hu1]
  have hchi : c ≤ 1 := by rw [hc]; nlinarith only [hu0, hu1]
  have hcv : c ≤ v := by rw [hc, hv]; nlinarith only [hu0, hu1]
  have htpos : 0 < t := by rw [ht]; positivity
  have hvpos : 0 < v := by linarith
  have h1c : 0 < 1 - c := by rw [hw]; positivity
  have hp1 : 1 ≤ p := by rw [hp]; nlinarith only [hu0, hu1]
  have hpu : p ≤ 1 + u := by rw [hp]; nlinarith only [hu0]
  have htu : t ≤ u := by rw [ht]; nlinarith only [hu0, hf2]
  have hHct : H * (1 - c) ≤ c * t := (le_div_iff₀ h1c).mp hHL
  have hHf : H ≤ f := by
    have e : H * (u * v) ≤ c * (f * u) := by rw [← hw, ← ht]; exact hHct
    have h2 : H * v ≤ c * f := by
      have e2 : H * (u * v) = u * (H * v) := by ring
      have e3 : c * (f * u) = u * (c * f) := by ring
      rw [e2, e3] at e
      exact le_of_mul_le_mul_left e hu0
    have h3 : c * f ≤ v * f := mul_le_mul_of_nonneg_right hcv hf0.le
    have h4 : H * v ≤ f * v := by linarith
    exact le_of_mul_le_mul_right h4 hvpos
  have hQf : Q * f ≤ 1 := (le_div_iff₀ hf0).mp hQhi
  have hQpos : 0 < Q := by linarith
  have hR0pos : 0 < R0 := by
    have : 5/3 ≤ 1/f := by rw [le_div_iff₀ hf0]; linarith
    linarith
  have hau0 : 0 ≤ au := by rw [hau]; exact mul_nonneg hR0pos.le (by linarith)
  have hau1 : au ≤ 1 := by
    have : 1/f ≤ 12/7 := by rw [div_le_iff₀ hf0]; linarith
    rw [hau]
    have h1 : R0 ≤ 5/7 := by linarith
    have h2 : Q - 1 ≤ 5/7 := by linarith
    nlinarith only [h1, h2, hR0pos, hQ1]
  -- logarithmic part
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = H*(H+t)/t := ⟨_, rfl⟩
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hQH : 0 < 1 + Q*H := by nlinarith only [hQpos, hH0]
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = Q*(c*t - (1-c)*H)/(1+Q*H) := ⟨_, rfl⟩
  have hznn : 0 ≤ z := by
    rw [hz]; apply div_nonneg _ hQH.le
    apply mul_nonneg hQpos.le; linarith
  have hzle : z ≤ Q*c*t := by
    rw [hz, div_le_iff₀ hQH]
    have h1 : 0 ≤ Q*(1-c)*H := by positivity
    have h2 : 0 ≤ Q*c*t*(Q*H) := by positivity
    nlinarith only [h1, h2]
  have hQct : Q*c*t ≤ u := by
    have e : Q*c*t = (Q*f)*c*u := by rw [ht]; ring
    rw [e]
    have h1 : (Q*f)*c ≤ 1 := by
      have := mul_le_mul hQf hchi hcpos.le zero_le_one
      linarith
    nlinarith only [h1, hu0]
  have hMz : M * z ≤ 1 := by
    have h1 : M * z ≤ M * (Q*c*t) := mul_le_mul_of_nonneg_left hzle hMnn
    have h2 : M * (Q*c*t) = H*(H+t)*(Q*c) := by rw [hM]; field_simp
    have h3 : H*(H+t) ≤ f*(f+t) := by nlinarith only [hH0, hHf, htpos]
    have h4 : Q*c ≤ 1/f := by
      have := mul_le_mul hQhi hchi hcpos.le (by positivity)
      linarith
    have h5 : H*(H+t)*(Q*c) ≤ f*(f+t)*(1/f) :=
      mul_le_mul h3 h4 (by positivity) (by positivity)
    have h6 : f*(f+t)*(1/f) = f + t := by field_simp
    linarith
  have hzu : z ≤ u := le_trans hzle hQct
  have hMw : M * (1 - c) ≤ 1 := by
    have e : M * (1 - c) = H*(H+t)*v/f := by rw [hM, hw, ht]; field_simp
    rw [e, div_le_iff₀ hf0]
    have h3 : H*(H+t) ≤ f*(f+t) := by nlinarith only [hH0, hHf, htpos]
    have h4 : H*(H+t)*v ≤ f*(f+t) := by
      have := mul_le_mul_of_nonneg_left hvhi (by positivity : (0:ℝ) ≤ H*(H+t))
      linarith
    nlinarith only [h4, htu, hf0, hf2, hu1]
  have hl1 : Real.log (c*(H+t)/H) = Real.log c + Real.log (1 + t/H) := by
    rw [show c*(H+t)/H = c*(1+t/H) by field_simp, Real.log_mul hcpos.ne' (by positivity)]
  have hl2 : (1+Q*(c*(H+t)))/(1+Q*H) = 1 + z := by
    rw [hz]; field_simp; ring
  rw [hl1, hl2, ← hM]
  -- log bounds
  have hLc_hi : Real.log c ≤ -(1 - c) := by linarith [Real.log_le_sub_one_of_pos hcpos]
  have hLc_lo : -(1 - c) - 2*(1-c)^2 ≤ Real.log c := by
    have h := Real.one_sub_inv_le_log_of_pos hcpos
    have e : 1 - c⁻¹ = -(1-c)/c := by field_simp; ring
    have : -(1-c) - 2*(1-c)^2 ≤ -(1-c)/c := by
      rw [le_div_iff₀ hcpos]; nlinarith only [h1c, hclo, hu1, hchi]
    linarith
  have hxpos : 0 < 1 + t/H := by positivity
  have hLx_hi : M * Real.log (1 + t/H) ≤ H + t := by
    have h := Real.log_le_sub_one_of_pos hxpos
    have e : M * (1 + t/H - 1) = H + t := by rw [hM]; field_simp; ring
    have := mul_le_mul_of_nonneg_left h hMnn
    linarith
  have hLx_lo : H ≤ M * Real.log (1 + t/H) := by
    have h := Real.one_sub_inv_le_log_of_pos hxpos
    have e : M * (1 - (1 + t/H)⁻¹) = H := by rw [hM]; field_simp; ring
    have := mul_le_mul_of_nonneg_left h hMnn
    linarith
  have hzpos1 : 0 < 1 + z := by linarith
  have hLz_hi : Real.log (1 + z) ≤ z := by linarith [Real.log_le_sub_one_of_pos hzpos1]
  have hLz_lo : z - z^2 ≤ Real.log (1 + z) := by
    have h := Real.one_sub_inv_le_log_of_pos hzpos1
    have e : 1 - (1 + z)⁻¹ = z/(1+z) := by field_simp; ring
    have : z - z^2 ≤ z/(1+z) := by
      rw [le_div_iff₀ hzpos1]; nlinarith only [mul_nonneg hznn (sq_nonneg z)]
    linarith
  -- the three error terms
  have hA1lo : -2*u ≤ M * Real.log c + M * (1 - c) := by
    have h := mul_le_mul_of_nonneg_left hLc_lo hMnn
    have : M * (1-c)^2 ≤ u := by
      have e : M*(1-c)^2 = (M*(1-c))*(1-c) := by ring
      rw [e]
      have : 1 - c ≤ u := by linarith
      nlinarith only [mul_nonneg hMnn h1c.le, hMw, this, h1c]
    nlinarith only [h, this]
  have hA1hi : M * Real.log c + M * (1 - c) ≤ 0 := by
    nlinarith only [mul_le_mul_of_nonneg_left hLc_hi hMnn]
  have hA2lo : 0 ≤ M * Real.log (1 + t/H) - H := by linarith
  have hA2hi : M * Real.log (1 + t/H) - H ≤ u := by linarith
  have hA3lo : -u ≤ M * Real.log (1 + z) - M * z := by
    have h := mul_le_mul_of_nonneg_left hLz_lo hMnn
    have : M * z^2 ≤ u := by
      have e : M*z^2 = (M*z)*z := by ring
      rw [e]; nlinarith only [mul_nonneg hMnn hznn, hMz, hzu, hznn]
    nlinarith only [h, this]
  have hA3hi : M * Real.log (1 + z) - M * z ≤ 0 := by
    nlinarith only [mul_le_mul_of_nonneg_left hLz_hi hMnn]
  -- algebraic part
  have IA : H*(β*(G0+Q*H) - (1-c)*G0)/(c*t)
      = H*p*G0 + p*Q*H^2 - H*v*G0/(f*c) := by
    rw [hβ, hw, ht, hp]; field_simp
  have IM : M * (1 - c) = H*(H+t)*v/f := by rw [hM, hw, ht]; field_simp
  have IZ : M * z = H*(H+t)*Q*(c*f - v*H)/(f*(1+Q*H)) := by
    rw [hM, hz, hw, ht]; field_simp
  have hB := MNR511_alg f u c t Q R0 G0 au H v p hf1 hf2 hu0 hu1 hclo hchi ht hvlo hvhi hp1 hpu
    hG0 hR0lo hR0hi hQlo hQhi hQ1 hau hH0.le hHf
  set E := (1-au)*(M * Real.log c + M * (1 - c)) + (1-au)*(M * Real.log (1 + t/H) - H)
    + au*(M * Real.log (1 + z) - M * z) with hE
  have hsplit : G0 + H*(β*(G0+Q*H) - (1-c)*G0)/(c*t)
      + M*((1-au)*(Real.log c + Real.log (1 + t/H)) + au*Real.log (1 + z)) - Kf f H
      = (G0 + (H*p*G0 + p*Q*H^2 - H*v*G0/(f*c)) + (1-au)*(H - H*(H+t)*v/f)
       + au*(H*(H+t)*Q*(c*f - v*H)/(f*(1+Q*H))) - Kf f H) + E := by
    rw [IA, ← IM, ← IZ, hE]; ring
  have h1a : 0 ≤ 1 - au := by linarith
  have hElo : -2*u ≤ E := by
    have p1 := mul_le_mul_of_nonneg_left hA1lo h1a
    have p2 := mul_nonneg h1a hA2lo
    have p3 := mul_le_mul_of_nonneg_left hA3lo hau0
    have p4 := mul_nonneg hau0 hu0.le
    rw [hE]; nlinarith only [p1, p2, p3, p4]
  have hEhi : E ≤ u := by
    have p1 := mul_nonpos_of_nonneg_of_nonpos h1a hA1hi
    have p2 := mul_le_mul_of_nonneg_left hA2hi h1a
    have p3 := mul_nonpos_of_nonneg_of_nonpos hau0 hA3hi
    have p4 := mul_nonneg hau0 hu0.le
    rw [hE]; nlinarith only [p1, p2, p3, p4]
  rw [hsplit]
  have hEabs : |E| ≤ 2*u := abs_le.mpr ⟨by linarith, by linarith⟩
  have := MNR511_abs2 hB hEabs
  linarith

set_option maxHeartbeats 4000000 in
theorem solution (f0 u : ℝ) (hf1 : 7 / 12 ≤ f0) (hf2 : f0 ≤ 3 / 5) (hu0 : 0 < u)
    (hu1 : u ≤ 1 / 16) :
    let k : Knobs := ⟨f0, u⟩
    k.Ku 0 = k.G0 ∧ ContinuousWithinAt k.Ku (Set.Ici 0) 0 ∧
      ∀ H : ℝ, 0 ≤ H → H ≤ k.L0 → |k.Ku H - Kf f0 H| ≤ 32 * u := by
  intro k
  have hf0 : 0 < f0 := by linarith
  have e1 : k.f0 = f0 := rfl
  have e2 : k.u = u := rfl
  have hc : k.c = 1 - u + u ^ 2 / 2 - u ^ 3 := rfl
  have ht : k.t = f0 * u := rfl
  have hcpos : 0 < k.c := by rw [hc]; nlinarith only [hu0, hu1]
  have hcle : k.c ≤ 1 := by rw [hc]; nlinarith only [hu0, hu1]
  have htpos : 0 < k.t := by rw [ht]; positivity
  have hw : 0 < 1 + u - u ^ 2 := by nlinarith only [hu0, hu1]
  have hβ : k.beta = k.c * k.t * (1 + u - u ^ 2) := by
    simp only [Knobs.beta, Knobs.u0, e2]; ring
  have hG0 : k.G0 = 1 + k.R0 := rfl
  have hau : k.au = k.R0 * (k.Q - 1) := rfl
  have hL0 : k.L0 = k.c * k.t / (1 - k.c) := rfl
  have hR0 : k.R0 = (1 - f0) * (1 - (1 - f0) * u / 2) / (k.c * f0 * (1 + u - u ^ 2)) := by
    simp only [Knobs.R0, Knobs.rho, Knobs.beta, Knobs.t, Knobs.u0, e1, e2]
    have h1 : (0:ℝ) < 1 + (u - u^2) := by linarith
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hQ : k.Q = (1 - u) / (f0 * (1 + u - u ^ 2)) := by
    simp only [Knobs.Q, Knobs.nu, Knobs.beta, Knobs.t, Knobs.u0, e1, e2]
    have h1 : (0:ℝ) < 1 + (u - u^2) := by linarith
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  -- c * p' bounds
  have hcp_hi : k.c * (1 + u - u ^ 2) ≤ 1 := by
    rw [hc]; nlinarith only [hu0, hu1, pow_pos hu0 3, pow_pos hu0 4, pow_pos hu0 5]
  have hcp_lo : 1 - 3/2 * u ^ 2 - 3/2 * u ^ 4 ≤ k.c * (1 + u - u ^ 2) := by
    rw [hc]; nlinarith only [hu0, hu1, pow_pos hu0 3, pow_pos hu0 4, pow_pos hu0 5]
  have hden : 0 < k.c * f0 * (1 + u - u ^ 2) := by positivity
  have hRs : (1 / f0 - 1) * (k.c * f0 * (1 + u - u ^ 2)) = (1 - f0) * (k.c * (1 + u - u ^ 2)) := by
    field_simp
  have hR0hi : k.R0 ≤ 1 / f0 - 1 := by
    rw [hR0, div_le_iff₀ hden, hRs]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    have hu2 : u ^ 2 ≤ 1 / 16 := by nlinarith only [hu0, hu1]
    have := mul_le_mul_of_nonneg_left hu2 (sq_nonneg u)
    have h4 : u ^ 4 ≤ u ^ 2 / 16 := by nlinarith only [this]
    have h5 : u ^ 2 ≤ u / 16 := by nlinarith only [hu0, hu1]
    nlinarith only [hcp_lo, h4, h5, hu0, hu1, hf2, mul_le_mul_of_nonneg_left hf2 hu0.le]
  have hR0lo : 1 / f0 - 1 - u / 5 ≤ k.R0 := by
    rw [hR0, le_div_iff₀ hden]
    have e : (1 / f0 - 1 - u / 5) * (k.c * f0 * (1 + u - u ^ 2))
        = (1 - f0) * (k.c * (1 + u - u ^ 2)) - u / 5 * f0 * (k.c * (1 + u - u ^ 2)) := by
      rw [sub_mul, hRs]; ring
    rw [e]
    have hu2 : u ^ 2 ≤ 1 / 16 := by nlinarith only [hu0, hu1]
    have := mul_le_mul_of_nonneg_left hu2 (sq_nonneg u)
    have h4 : u ^ 4 ≤ u ^ 2 / 16 := by nlinarith only [this]
    have hcp2 : 15 / 16 ≤ k.c * (1 + u - u ^ 2) := by nlinarith only [hcp_lo, h4, hu0, hu1]
    have m1 := mul_le_mul_of_nonneg_left hcp_hi (by linarith : (0:ℝ) ≤ 1 - f0)
    have m2 := mul_le_mul_of_nonneg_left hcp2 (by positivity : (0:ℝ) ≤ u / 5 * f0)
    have hq : 8 * (1 - f0) ^ 2 ≤ 3 * f0 := by nlinarith only [hf1, hf2]
    have m3 := mul_le_mul_of_nonneg_left hq hu0.le
    nlinarith only [m1, m2, m3]
  have hfp : 0 < f0 * (1 + u - u ^ 2) := by positivity
  have hQhi : k.Q ≤ 1 / f0 := by
    rw [hQ, div_le_div_iff₀ hfp hf0]; nlinarith only [hf0, hu0, hu1, mul_pos hf0 hu0]
  have hQlo : 1 / f0 - 7 * u / 2 ≤ k.Q := by
    rw [hQ, le_div_iff₀ hfp]
    have e : (1 / f0 - 7 * u / 2) * (f0 * (1 + u - u ^ 2))
        = (1 + u - u ^ 2) - 7 * u / 2 * (f0 * (1 + u - u ^ 2)) := by field_simp
    rw [e]
    have : 7 / 12 ≤ f0 * (1 + u - u ^ 2) := by
      have huu : 0 ≤ u - u ^ 2 := by nlinarith only [hu0, hu1]
      nlinarith only [hf1, mul_nonneg hf0.le huu]
    nlinarith only [this, hu0]
  have hQ1 : 1 ≤ k.Q := by
    rw [hQ, le_div_iff₀ hfp]
    have := mul_le_mul_of_nonneg_right hf2 hw.le
    nlinarith only [this, hu0, hu1]
  have hKu : ∀ H : ℝ, H ≠ 0 → k.Ku H = k.G0 + H * (k.beta * (k.G0 + k.Q * H) - (1 - k.c) * k.G0) / (k.c * k.t)
      + H * (H + k.t) / k.t * ((1 - k.au) * Real.log (k.c * (H + k.t) / H)
        + k.au * Real.log ((1 + k.Q * (k.c * (H + k.t))) / (1 + k.Q * H))) := by
    intro H hH
    simp only [Knobs.Ku, if_neg hH, Knobs.Dsh]
  have hR0pos : 0 < k.R0 := by
    have : 5/3 ≤ 1/f0 := by rw [le_div_iff₀ hf0]; linarith
    linarith
  have hQpos : 0 < k.Q := by linarith
  refine ⟨if_pos rfl, ?_, ?_⟩
  · -- continuity at zero from the right
    let g : ℝ → ℝ := fun H => k.G0 + H * (k.beta * (k.G0 + k.Q * H) - (1 - k.c) * k.G0) / (k.c * k.t)
      + (H + k.t) / k.t * ((1 - k.au) * (H * Real.log (k.c * (H + k.t)) - H * Real.log H)
        + k.au * (H * Real.log ((1 + k.Q * (k.c * (H + k.t))) / (1 + k.Q * H))))
    have hl1 : ContinuousAt (fun H : ℝ => Real.log (k.c * (H + k.t))) 0 :=
      ContinuousAt.log (by fun_prop) (by simp; exact ⟨hcpos.ne', htpos.ne'⟩)
    have hl2 : ContinuousAt (fun H : ℝ => Real.log ((1 + k.Q * (k.c * (H + k.t))) / (1 + k.Q * H))) 0 := by
      apply ContinuousAt.log
      · apply ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)
      · simp; positivity
    have hl3 : Continuous (fun H : ℝ => H * Real.log H) := Real.continuous_mul_log
    have hg : ContinuousAt g 0 := by
      have a1 : ContinuousAt (fun H : ℝ => H * Real.log (k.c * (H + k.t))) 0 :=
        continuousAt_id.mul hl1
      have a2 : ContinuousAt (fun H : ℝ => H * Real.log ((1 + k.Q * (k.c * (H + k.t))) / (1 + k.Q * H))) 0 :=
        continuousAt_id.mul hl2
      have a3 : ContinuousAt (fun H : ℝ => H * Real.log H) 0 := hl3.continuousAt
      have a4 : ContinuousAt (fun H : ℝ => k.G0 + H * (k.beta * (k.G0 + k.Q * H) - (1 - k.c) * k.G0) / (k.c * k.t)) 0 := by
        fun_prop
      have a5 : ContinuousAt (fun H : ℝ => (H + k.t) / k.t) 0 := by fun_prop
      exact a4.add (a5.mul (((continuousAt_const.mul (a1.sub a3))).add (continuousAt_const.mul a2)))
    have heq : ∀ H ∈ Set.Ici (0:ℝ), k.Ku H = g H := by
      intro H hH
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hH) with h | h
      · subst h; simp [g, Knobs.Ku]
      · rw [hKu H h.ne']
        simp only [g]
        rw [Real.log_div (by positivity) h.ne']
        ring
    exact (hg.continuousWithinAt).congr heq (heq 0 (Set.mem_Ici.mpr le_rfl))
  · intro H h0 hL
    rcases eq_or_lt_of_le h0 with h | h
    · subst h
      have e0 : k.Ku 0 = k.G0 := if_pos rfl
      have ek : Kf f0 0 = 1 / f0 := by
        unfold Kf; rw [div_eq_div_iff (by positivity) (by positivity)]; ring
      rw [e0, ek, hG0]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rw [hKu H h.ne']
      exact MNR511_core f0 u k.c k.t k.beta k.Q k.R0 k.G0 k.au H hf1 hf2 hu0 hu1 hc ht hβ hG0
        hR0lo hR0hi hQlo hQhi hQ1 hau h (hL0 ▸ hL)
