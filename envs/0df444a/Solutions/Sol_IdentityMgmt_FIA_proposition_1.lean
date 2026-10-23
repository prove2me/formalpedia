-- Prove2me | solution 1 for IdentityMgmt.FIA.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T04:07:25.583255+00:00
-- url     : https://prove2.me/submissions/2895ba30-46af-442d-bd2b-2853dcd01441

import Mathlib
import Definitions.Def_IdentityMgmt_FIA_Model

set_option autoImplicit false

namespace IdentityMgmt.FIA

lemma ec18_dy (b t x y0 : ℝ) (Ψ : ℝ → ℝ) (hb : b ≠ 1) :
    deriv (fun y => periodProfit b t Ψ x y) y0 = (1-b)*(1-t+x-2*y0) + Ψ x := by
  have hb' : (1:ℝ) - b ≠ 0 := by intro h; exact hb (by linarith)
  have h1 : HasDerivAt (fun y : ℝ => y) 1 y0 := hasDerivAt_id' y0
  have h2 := (((h1.const_sub (1-t+x)).mul (h1.sub_const (Ψ x/(1-b)))).const_add
    ((t^2-x^2)/2)).const_mul (1-b)
  calc deriv (fun y => periodProfit b t Ψ x y) y0 = _ := h2.deriv
    _ = (1-b)*(1-t+x-2*y0) + Ψ x := by field_simp; ring

lemma ec18_dx (b t y x0 l : ℝ) (Ψ : ℝ → ℝ) (hΨ : HasDerivAt Ψ l x0) (hb : b ≠ 1) :
    deriv (fun x => periodProfit b t Ψ x y) x0 = (1-b)*(y-x0) - Ψ x0 - l*(1-t+x0-y) := by
  have hb' : (1:ℝ) - b ≠ 0 := by intro h; exact hb (by linarith)
  have hx : HasDerivAt (fun x : ℝ => x) 1 x0 := hasDerivAt_id' x0
  have hsq : HasDerivAt (fun x : ℝ => x^2) (2*x0) x0 := by
    simpa using hasDerivAt_pow 2 x0
  have hA := (hsq.const_sub (t^2)).div_const 2
  have hB := (hx.const_add (1-t)).sub_const y
  have hD := (hΨ.div_const (1-b)).const_sub y
  have h2 := (hA.add (hB.mul hD)).const_mul (1-b)
  calc deriv (fun x => periodProfit b t Ψ x y) x0 = _ := h2.deriv
    _ = (1-b)*(y-x0) - Ψ x0 - l*(1-t+x0-y) := by field_simp; ring

lemma ec18_hasDerivΨ (P : Profile) (x : ℝ) : HasDerivAt P.Ψ P.lam x := by
  have h : P.Ψ = fun z => P.C + P.lam * z := rfl
  rw [h]
  simpa using ((hasDerivAt_id' x).const_mul P.lam).const_add P.C

lemma ec18_arb (P : Profile) (hA : P.Arbitrage) :
    P.lam * (1 - P.β*P.γ) = P.β*(1-P.β)*P.γ*(1-P.γ) ∧
    P.C * (1 - P.β) = P.β*P.K*(P.lam - (1-P.β)*P.γ) := by
  have h0 := hA 0 ⟨le_refl _, zero_le_one⟩
  have h1 := hA 1 ⟨zero_le_one, le_refl _⟩
  simp only [Profile.Ψ, Profile.Φ] at h0 h1
  exact ⟨by linear_combination h1 - h0, by linear_combination h0⟩

lemma ec18_euler (P : Profile) (hb : P.β ≠ 1) (hE : P.Euler) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (0:ℝ) 1) :
    ((1-P.β)*(1-P.θt+θ-2*P.Φ θ) + P.Ψ θ) + P.β*((1-P.β)*(P.Φ (P.Φ θ) - P.Φ θ)
      - P.Ψ (P.Φ θ) - P.lam*(1-P.θt+P.Φ θ - P.Φ (P.Φ θ))) = 0 := by
  have h := hE θ hθ
  rw [ec18_dy _ _ _ _ _ hb, ec18_dx _ _ _ _ _ _ (ec18_hasDerivΨ P _) hb] at h
  exact h

lemma ec18_struct (P : Profile) (h : P.IsMarkovEq) :
    P.lam * (1 - P.β*P.γ) = P.β*(1-P.β)*P.γ*(1-P.γ) ∧
    P.C * (1 - P.β) = P.β*P.K*(P.lam - (1-P.β)*P.γ) ∧
    (1-2*P.γ)*(1-P.β*P.γ) = P.β^2*P.γ^2*(1-P.γ)^2 ∧
    P.K*(2*(1-P.β*P.γ) - P.β^2*P.γ^2*(1-P.γ))
      = (1-P.θt)*((1-P.β*P.γ) - P.β^2*P.γ*(1-P.γ)) := by
  obtain ⟨hb0, hb1, hg0, hg1, hi0, hit, ht1, hA, hE⟩ := h
  obtain ⟨hl, hC⟩ := ec18_arb P hA
  have hbne : P.β ≠ 1 := ne_of_lt hb1
  have E0 := ec18_euler P hbne hE 0 ⟨le_refl _, zero_le_one⟩
  have E1 := ec18_euler P hbne hE 1 ⟨zero_le_one, le_refl _⟩
  simp only [Profile.Ψ, Profile.Φ] at E0 E1
  have h1b : (1:ℝ) - P.β ≠ 0 := by intro h; linarith
  refine ⟨hl, hC, ?_, ?_⟩
  · have : (1-P.β) * ((1-2*P.γ)*(1-P.β*P.γ) - P.β^2*P.γ^2*(1-P.γ)^2) = 0 := by
      linear_combination (1-P.β*P.γ)*(E1-E0) - (1-2*P.β*P.γ+P.β*P.γ^2)*hl
    have := (mul_eq_zero.mp this).resolve_left h1b
    linarith
  · have : (1-P.β) * (P.K*(2*(1-P.β*P.γ) - P.β^2*P.γ^2*(1-P.γ))
        - (1-P.θt)*((1-P.β*P.γ) - P.β^2*P.γ*(1-P.γ))) = 0 := by
      linear_combination -(1-P.β*P.γ)*(E0-hC) - P.β*((1-P.θt)-P.γ*P.K)*hl
    have := (mul_eq_zero.mp this).resolve_left h1b
    linarith

lemma ec18_bg {β γ : ℝ} (hb1 : β < 1) (hg0 : 0 ≤ γ) (hg1 : γ < 1) : 0 < 1 - β*γ := by
  nlinarith [mul_le_mul_of_nonneg_right hb1.le hg0]

lemma ec18_closed (P : Profile) (h : P.IsMarkovEq) :
    P.lam = P.β*(1-P.β)*P.γ*(1-P.γ)/(1-P.β*P.γ) ∧
    P.C = -(P.β*(1-P.β)*P.γ*(1-P.γ)/(1-P.β*P.γ)) * P.θinf := by
  obtain ⟨hl, hC, -, -⟩ := ec18_struct P h
  obtain ⟨hb0, hb1, hg0, hg1, -⟩ := h
  have hbg := ec18_bg hb1 hg0 hg1
  have h1b : (1:ℝ) - P.β ≠ 0 := by intro h; linarith
  have h1g : (1:ℝ) - P.γ ≠ 0 := by intro h; linarith
  have key : P.C * (1-P.β*P.γ) = -(P.β*(1-P.β)*P.γ*P.K) := by
    apply mul_left_cancel₀ h1b
    linear_combination (1-P.β*P.γ)*hC + P.β*P.K*hl
  refine ⟨by rw [eq_div_iff hbg.ne']; exact hl, ?_⟩
  unfold Profile.θinf
  field_simp
  linear_combination key

lemma ec18_path (P : Profile) (hg1 : P.γ < 1) (n : ℕ) :
    P.path n = P.θinf + P.γ^n * (P.θt - P.θinf) := by
  have hne : (1:ℝ) - P.γ ≠ 0 := by intro h; linarith
  induction n with
  | zero => simp [Profile.path]
  | succ n ih =>
    have : P.path (n+1) = P.Φ (P.path n) := by
      simp only [Profile.path]; rw [Function.iterate_succ_apply']
    rw [this, ih]
    simp only [Profile.Φ, Profile.θinf]
    field_simp
    ring

lemma ec18_gain (P : Profile) (h : P.IsMarkovEq) :
    P.activeGain = (P.θt - P.θinf) * cbarFIA P.β P.γ - P.c := by
  obtain ⟨hlam, hC⟩ := ec18_closed P h
  obtain ⟨hb0, hb1, hg0, hg1, -⟩ := h
  have hbg := ec18_bg hb1 hg0 hg1
  have h1b : (1:ℝ) - P.β ≠ 0 := by intro h; linarith
  have hbg1 : P.β * P.γ < 1 := by linarith
  have hbg0 : 0 ≤ P.β * P.γ := mul_nonneg hb0.le hg0
  have hs : ∀ n : ℕ, (1 - P.β) * P.pI (n+1) * P.β^(n+1) =
      (P.β*(1-P.β)*P.θinf) * P.β^n
        + ((1-P.β)^2*P.β*P.γ^2*(P.θt - P.θinf)/(1-P.β*P.γ)) * (P.β*P.γ)^n := by
    intro n
    simp only [Profile.pI, Profile.Ψ]
    rw [ec18_path P hg1, ec18_path P hg1, hlam, hC]
    field_simp
    ring
  have s1 : Summable (fun n : ℕ => P.β^n) := summable_geometric_of_lt_one hb0.le hb1
  have s2 : Summable (fun n : ℕ => (P.β*P.γ)^n) := summable_geometric_of_lt_one hbg0 hbg1
  unfold Profile.activeGain
  rw [tsum_congr hs, (s1.mul_left _).tsum_add (s2.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_lt_one hb0.le hb1, tsum_geometric_of_lt_one hbg0 hbg1]
  unfold cbarFIA
  field_simp
  ring

noncomputable def ec18_k (β γ : ℝ) : ℝ :=
  ((1-β*γ) - β^2*γ*(1-γ)) / ((1-γ)*(2*(1-β*γ) - β^2*γ^2*(1-γ)))

lemma ec18_NM {β γ : ℝ} (hb0 : 0 < β) (hb1 : β < 1) (hg0 : 0 ≤ γ) (hg1 : γ < 1) :
    0 < (1-β*γ) - β^2*γ*(1-γ) ∧ 0 < 2*(1-β*γ) - β^2*γ^2*(1-γ) := by
  have hbg : β*γ ≤ γ := by nlinarith
  have hb2 : β^2 ≤ 1 := by nlinarith
  have hb2g : β^2*γ ≤ γ := by nlinarith
  have hbg2 : (β*γ)^2 ≤ 1 := by nlinarith
  constructor
  · nlinarith [mul_pos (show (0:ℝ) < 1 - γ by linarith) (show (0:ℝ) < 1 - β^2*γ by linarith),
      mul_nonneg hg0 (show (0:ℝ) ≤ 1 - β by linarith)]
  · have : β^2*γ^2*(1-γ) ≤ 1 - γ := by
      have h1 : (β*γ)^2*(1-γ) ≤ 1*(1-γ) :=
        mul_le_mul_of_nonneg_right hbg2 (by linarith)
      nlinarith
    nlinarith

lemma ec18_kpos {β γ : ℝ} (hb0 : 0 < β) (hb1 : β < 1) (hg0 : 0 ≤ γ) (hg1 : γ < 1) :
    0 < ec18_k β γ := by
  obtain ⟨hN, hM⟩ := ec18_NM hb0 hb1 hg0 hg1
  unfold ec18_k
  exact div_pos hN (mul_pos (by linarith) hM)

lemma ec18_theta (P : Profile) (h : P.IsMarkovEq) :
    P.θinf = ec18_k P.β P.γ * (1 - P.θt) := by
  obtain ⟨-, -, -, Kq⟩ := ec18_struct P h
  obtain ⟨hb0, hb1, hg0, hg1, -⟩ := h
  obtain ⟨hN, hM⟩ := ec18_NM hb0 hb1 hg0 hg1
  have h1g : (1:ℝ) - P.γ ≠ 0 := by intro h; linarith
  unfold Profile.θinf ec18_k
  rw [div_mul_eq_mul_div, div_eq_div_iff h1g (mul_ne_zero h1g hM.ne')]
  linear_combination (1-P.γ)*Kq

lemma ec18_cbpos {β γ : ℝ} (hb0 : 0 < β) (hb1 : β < 1) (hg0 : 0 ≤ γ) (hg1 : γ < 1) :
    0 < cbarFIA β γ := by
  have hbg := ec18_bg hb1 hg0 hg1
  have hbg' : β*γ ≤ γ := by nlinarith
  unfold cbarFIA
  apply div_pos
  · apply mul_pos (mul_pos hb0 (by linarith))
    nlinarith
  · exact pow_pos hbg 2

lemma ec18_gu_aux (β g1 g2 : ℝ) (hb0 : 0 < β) (hb1 : β < 1) (h10 : 0 ≤ g1)
    (h21 : g2 < 1)
    (e1 : (1-2*g1)*(1-β*g1) = β^2*g1^2*(1-g1)^2)
    (e2 : (1-2*g2)*(1-β*g2) = β^2*g2^2*(1-g2)^2) (hlt : g1 < g2) : False := by
  have h20 : 0 ≤ g2 := by linarith
  have hbg2 := ec18_bg hb1 h20 h21
  have hsq : β^2*g2^2*(1-g2)^2 = (β*g2*(1-g2))^2 := by ring
  have hhalf : 2*g2 ≤ 1 := by
    by_contra hc
    push Not at hc
    have : (1-2*g2)*(1-β*g2) < 0 := mul_neg_of_neg_of_pos (by linarith) hbg2
    nlinarith [sq_nonneg (β*g2*(1-g2))]
  have hL : (1-2*g2)*(1-β*g2) < (1-2*g1)*(1-β*g1) := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 1-2*g1 by linarith)
      (mul_nonneg hb0.le (show (0:ℝ) ≤ g2-g1 by linarith)),
      mul_pos hbg2 (show (0:ℝ) < g2-g1 by linarith)]
  have hu0 : 0 ≤ g1*(1-g1) := mul_nonneg h10 (by linarith)
  have hu : g1*(1-g1) ≤ g2*(1-g2) := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ g2-g1 by linarith) (show (0:ℝ) ≤ 1-g1-g2 by linarith)]
  have hu2 : (g1*(1-g1))^2 ≤ (g2*(1-g2))^2 := pow_le_pow_left₀ hu0 hu 2
  have hR : β^2*g1^2*(1-g1)^2 ≤ β^2*g2^2*(1-g2)^2 := by
    have := mul_le_mul_of_nonneg_left hu2 (sq_nonneg β)
    nlinarith
  linarith

lemma ec18_gu (β g1 g2 : ℝ) (hb0 : 0 < β) (hb1 : β < 1) (h10 : 0 ≤ g1) (h11 : g1 < 1)
    (h20 : 0 ≤ g2) (h21 : g2 < 1)
    (e1 : (1-2*g1)*(1-β*g1) = β^2*g1^2*(1-g1)^2)
    (e2 : (1-2*g2)*(1-β*g2) = β^2*g2^2*(1-g2)^2) : g1 = g2 := by
  rcases lt_trichotomy g1 g2 with h | h | h
  · exact (ec18_gu_aux β g1 g2 hb0 hb1 h10 h21 e1 e2 h).elim
  · exact h
  · exact (ec18_gu_aux β g2 g1 hb0 hb1 h20 h11 e2 e1 h).elim

lemma ec18_gamma_eq (P Q : Profile) (hP : P.IsMarkovEq) (hQ : Q.IsMarkovEq) (h : P.β = Q.β) :
    P.γ = Q.γ := by
  obtain ⟨-, -, eP, -⟩ := ec18_struct P hP
  obtain ⟨-, -, eQ, -⟩ := ec18_struct Q hQ
  obtain ⟨hb0, hb1, hg0, hg1, -⟩ := hP
  obtain ⟨-, -, hq0, hq1, -⟩ := hQ
  rw [← h] at eQ
  exact ec18_gu P.β P.γ Q.γ hb0 hb1 hg0 hg1 hq0 hq1 eP eQ

lemma ec18_c1 (P : Profile) (hP : P.IsMPE) (hc : P.c < cbarFIA P.β P.γ) :
    P.θt < 1 ∧ 0 < P.θinf := by
  obtain ⟨hM, -, -, hpiv2⟩ := hP
  have hg := ec18_gain P hM
  have hth := ec18_theta P hM
  obtain ⟨hb0, hb1, hg0, hg1, -, -, ht1, -⟩ := hM
  have hk := ec18_kpos hb0 hb1 hg0 hg1
  have ht : P.θt < 1 := by
    rcases lt_or_eq_of_le ht1 with h | h
    · exact h
    · exfalso
      have := hpiv2 h
      rw [hg, hth, h] at this
      norm_num at this
      linarith
  exact ⟨ht, by rw [hth]; exact mul_pos hk (by linarith)⟩

lemma ec18_interior (P : Profile) (hP : P.IsMPE) (ht : P.θt < 1) :
    P.c = (P.θt - ec18_k P.β P.γ * (1 - P.θt)) * cbarFIA P.β P.γ := by
  obtain ⟨hM, -, hpiv1, -⟩ := hP
  have := hpiv1 ht
  rw [ec18_gain P hM, ec18_theta P hM] at this
  linarith

end IdentityMgmt.FIA

open IdentityMgmt.FIA in
theorem solution :
    -- (i) below the threshold: active customers exist and some consumers are never served
    (∀ P : Profile, P.IsMPE → P.c < cbarFIA P.β P.γ → P.θt < 1 ∧ 0 < P.θinf) ∧
    -- (i) both fractions decrease when c increases (equilibria with the same β)
    (∀ P Q : Profile, P.IsMPE → Q.IsMPE → P.β = Q.β → P.c < Q.c → Q.c < cbarFIA Q.β Q.γ →
      Q.θinf < P.θinf ∧ 1 - Q.θt < 1 - P.θt) ∧
    -- (i) … and both tend to zero as c approaches the threshold from below
    (∀ β ε : ℝ, 0 < ε → ∃ δ > 0, ∀ P : Profile, P.IsMPE → P.β = β →
      cbarFIA P.β P.γ - δ < P.c → P.c < cbarFIA P.β P.γ → P.θinf < ε ∧ 1 - P.θt < ε) ∧
    -- (ii) at or above the threshold: everyone is passive and the market is asymptotically covered
    (∀ P : Profile, P.IsMPE → cbarFIA P.β P.γ ≤ P.c →
      P.θt = 1 ∧ Filter.Tendsto P.path Filter.atTop (nhds 0)) ∧
    -- (iii) the lifetime net utility of the marginal customer tends to zero along the path
    (∀ P : Profile, P.IsMPE → Filter.Tendsto (fun n => P.Ψ (P.path n)) Filter.atTop (nhds 0)) := by
  refine ⟨ec18_c1, ?_, ?_, ?_, ?_⟩
  · -- monotonicity in c
    intro P Q hP hQ hβ hc hcQ
    have hγ := ec18_gamma_eq P Q hP.1 hQ.1 hβ
    have htQ := (ec18_c1 Q hQ hcQ).1
    have htP := (ec18_c1 P hP (by rw [hβ, hγ]; linarith)).1
    have gP := ec18_interior P hP htP
    have gQ := ec18_interior Q hQ htQ
    rw [← hβ, ← hγ] at gQ
    obtain ⟨hb0, hb1, hg0, hg1, -⟩ := hP.1
    have hk := ec18_kpos hb0 hb1 hg0 hg1
    have hcb := ec18_cbpos hb0 hb1 hg0 hg1
    have hd : ((Q.θt - ec18_k P.β P.γ * (1 - Q.θt)) - (P.θt - ec18_k P.β P.γ * (1 - P.θt)))
        * cbarFIA P.β P.γ = Q.c - P.c := by linear_combination gP - gQ
    have hX : 0 < (Q.θt - ec18_k P.β P.γ * (1 - Q.θt)) - (P.θt - ec18_k P.β P.γ * (1 - P.θt)) := by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_le_mul_of_nonneg_right hcon hcb.le]
    have ha : 1 - Q.θt < 1 - P.θt := by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_le_mul_of_nonneg_left hcon hk.le]
    refine ⟨?_, ha⟩
    rw [ec18_theta P hP.1, ec18_theta Q hQ.1, ← hβ, ← hγ]
    exact mul_lt_mul_of_pos_left ha hk
  · -- limit as c ↑ c̄
    intro β ε hε
    by_cases hex : ∃ P0 : Profile, P0.IsMPE ∧ P0.β = β
    · obtain ⟨P0, hP0, hb⟩ := hex
      obtain ⟨hb0, hb1, hg0, hg1, -⟩ := hP0.1
      have hk := ec18_kpos hb0 hb1 hg0 hg1
      have hcb := ec18_cbpos hb0 hb1 hg0 hg1
      refine ⟨ε * cbarFIA P0.β P0.γ, mul_pos hε hcb, ?_⟩
      intro P hP hPb h1 h2
      have hPβ : P.β = P0.β := hPb.trans hb.symm
      have hγ := ec18_gamma_eq P P0 hP.1 hP0.1 hPβ
      have ht := (ec18_c1 P hP h2).1
      have gP := ec18_interior P hP ht
      have hth := ec18_theta P hP.1
      rw [hPβ, hγ] at gP hth h1
      have hlt : (1 + ec18_k P0.β P0.γ) * (1 - P.θt) < ε := by
        by_contra hcon
        push Not at hcon
        nlinarith [mul_le_mul_of_nonneg_right hcon hcb.le]
      have ha : 0 < 1 - P.θt := by linarith
      have hka : 0 < ec18_k P0.β P0.γ * (1 - P.θt) := mul_pos hk ha
      constructor
      · rw [hth]; nlinarith
      · nlinarith
    · refine ⟨1, one_pos, ?_⟩
      intro P hP hPb
      exact absurd ⟨P, hP, hPb⟩ hex
  · -- (ii) above the threshold
    intro P hP hc
    have hth := ec18_theta P hP.1
    obtain ⟨hb0, hb1, hg0, hg1, -, -, ht1, -⟩ := hP.1
    have hk := ec18_kpos hb0 hb1 hg0 hg1
    have hcb := ec18_cbpos hb0 hb1 hg0 hg1
    have ht : P.θt = 1 := by
      by_contra hne
      have ht' : P.θt < 1 := lt_of_le_of_ne ht1 hne
      have gP := ec18_interior P hP ht'
      have hka : 0 < ec18_k P.β P.γ * (1 - P.θt) := mul_pos hk (by linarith)
      have : (1 - (P.θt - ec18_k P.β P.γ * (1 - P.θt))) * cbarFIA P.β P.γ > 0 :=
        mul_pos (by linarith) hcb
      nlinarith
    refine ⟨ht, ?_⟩
    have hp : P.path = fun n => P.γ ^ n := by
      funext n
      rw [ec18_path P hg1, hth, ht]
      ring
    rw [hp]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one hg0 hg1
  · -- (iii) zero utility in the limit
    intro P hP
    obtain ⟨hlam, hC⟩ := ec18_closed P hP.1
    obtain ⟨hb0, hb1, hg0, hg1, -⟩ := hP.1
    have e : (fun n => P.Ψ (P.path n)) = fun n =>
        (P.β*(1-P.β)*P.γ*(1-P.γ)/(1-P.β*P.γ) * (P.θt - P.θinf)) * P.γ ^ n := by
      funext n
      simp only [Profile.Ψ]
      rw [ec18_path P hg1 n, hC, hlam]
      ring
    rw [e]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hg0 hg1).const_mul
      (P.β*(1-P.β)*P.γ*(1-P.γ)/(1-P.β*P.γ) * (P.θt - P.θinf))
