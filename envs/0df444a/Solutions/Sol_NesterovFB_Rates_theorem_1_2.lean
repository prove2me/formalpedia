-- Prove2me | solution 2 for NesterovFB.Rates.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T10:57:18.991871+00:00
-- url     : https://prove2.me/submissions/1fbeb61c-17ab-4231-b7f2-26eb8cfa4784

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_NesterovFB_Rates_Algorithm
import Theorems.Thm_Gradient_descent_lemma_gradient
import Theorems.Thm_Gradient_convex_first_order_gradient
import Theorems.Thm_ProxOperator_ne_top
import Theorems.Thm_DiscreteEnergy_limits_of_energy_recursions
import Theorems.Thm_Real_le_of_le_add_mul_of_mem_Ioc

-- carved verbatim out of submission 842bba92-1894-4b7e-9e8c-de15dbe6d45f, lines 809-823

section
open Filter Topology InnerProductSpace
open Filter Topology InnerProductSpace NNReal
open NesterovFB
open NesterovFB.Rates
open ThreeOpSplitting.ConvexRates

lemma nfb_prox_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (hγ : 0 < γ) (f : H → EReal) (P : H → H) (hf : IsProperClosedConvex f)
    (hP : IsProx γ f P) (x y : H) (a b : ℝ) (ha : f (P x) = a) (hb : f y ≤ b) :
    ⟪x - P x, y - P x⟫_ℝ ≤ γ * (b - a) := by
  obtain ⟨hbot, _, _, hconv⟩ := hf
  have key : γ * (a - b) ≤ ⟪P x - x, y - P x⟫_ℝ := by
    have h := Real.le_of_le_add_mul_of_mem_Ioc (A := a - b) (B := ⟪P x - x, y - P x⟫_ℝ / γ)
      (C := ‖y - P x‖ ^ 2 / (2 * γ)) (fun t ht0 ht1 => by
        set yt := (1 - t) • P x + t • y with hyt
        have hm1 : (P x, a) ∈ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)} := by
          simp only [Set.mem_ofPred_eq]; rw [ha]
        have hm2 : (y, b) ∈ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)} := by
          simp only [Set.mem_ofPred_eq]; exact hb
        have hc := hconv hm1 hm2 (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
        simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
          smul_eq_mul] at hc
        have hq := hP x yt
        rw [ha] at hq
        have hp2 : ((a + ‖P x - x‖ ^ 2 / (2 * γ) : ℝ) : EReal) ≤
            (((1 - t) * a + t * b + ‖yt - x‖ ^ 2 / (2 * γ) : ℝ) : EReal) := by
          rw [EReal.coe_add, EReal.coe_add]
          exact hq.trans (add_le_add hc le_rfl)
        rw [EReal.coe_le_coe_iff] at hp2
        have hexp : yt - x = (P x - x) + t • (y - P x) := by rw [hyt]; module
        rw [hexp, norm_add_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs,
          abs_of_pos ht0] at hp2
        have k1 : t * (a - b) ≤ t * (⟪P x - x, y - P x⟫_ℝ / γ + t * (‖y - P x‖ ^ 2 / (2 * γ))) := by
          have e2 : (‖P x - x‖ ^ 2 + 2 * (t * ⟪P x - x, y - P x⟫_ℝ) + (t * ‖y - P x‖) ^ 2) / (2 * γ)
              = ‖P x - x‖ ^ 2 / (2 * γ) + t * (⟪P x - x, y - P x⟫_ℝ / γ
                + t * (‖y - P x‖ ^ 2 / (2 * γ))) := by
            field_simp; ring
          rw [e2] at hp2
          nlinarith
        exact le_of_mul_le_mul_left k1 ht0)
    rw [le_div_iff₀ hγ] at h
    linarith
  have e : ⟪x - P x, y - P x⟫_ℝ = -⟪P x - x, y - P x⟫_ℝ := by
    rw [← inner_neg_left, neg_sub]
  linarith

lemma nfb_fb_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : ℝ≥0) (s : ℝ) (P : H → H)
    (hΨ : IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * (L : ℝ) ≤ 1)
    (hP : IsProx s Ψ P) (y z : H) (a b : ℝ)
    (ha : Ψ (P (y - s • gradient Φ y)) = a) (hb : Ψ z ≤ b) :
    a + Φ (P (y - s • gradient Φ y)) + 1 / (2 * s) * ‖P (y - s • gradient Φ y) - z‖ ^ 2 ≤
      b + Φ z + 1 / (2 * s) * ‖y - z‖ ^ 2 := by
  have hd : Differentiable ℝ Φ := hΦd.differentiable (by norm_num)
  set g := gradient Φ y with hg
  set p := P (y - s • g) with hp
  have h1 := nfb_prox_ineq s hs Ψ P hΨ hP (y - s • g) z a b ha hb
  rw [← hp] at h1
  have hLip : ∀ u v : H, ‖gradient Φ u - gradient Φ v‖ ≤ (L:ℝ) * ‖u - v‖ := by
    intro u v; have := hL.dist_le_mul u v; rwa [dist_eq_norm, dist_eq_norm] at this
  have h2 := Gradient.descent_lemma_gradient Φ hd L L.2 hLip y p
  have h3 := Gradient.convex_first_order_gradient Φ hΦc hd y z
  rw [← hg] at h2 h3
  have e1 : y - s • g - p = (y - p) - s • g := by abel
  rw [e1, inner_sub_left, real_inner_smul_left] at h1
  have e2 : ‖y - z‖ ^ 2 = ‖y - p‖ ^ 2 - 2 * ⟪y - p, z - p⟫_ℝ + ‖p - z‖ ^ 2 := by
    have : y - z = (y - p) - (z - p) := by abel
    rw [this, norm_sub_sq_real, norm_sub_rev z p]
  have e3 : ⟪g, z - p⟫_ℝ = ⟪g, z - y⟫_ℝ - ⟪g, p - y⟫_ℝ := by
    rw [← inner_sub_right]; congr 1; abel
  have hpy : ‖p - y‖ = ‖y - p‖ := norm_sub_rev _ _
  rw [hpy] at h2
  have hq : 0 ≤ ‖y - p‖ ^ 2 := sq_nonneg _
  have hLs : s * (L:ℝ) * ‖y - p‖ ^ 2 ≤ ‖y - p‖ ^ 2 := by nlinarith
  rw [e2]
  have key : s * (a + Φ p) ≤ s * (b + Φ z) - ⟪y - p, z - p⟫_ℝ + s * ((L:ℝ) / 2) * ‖y - p‖ ^ 2 := by
    nlinarith
  have : s * (a + Φ p + 1 / (2 * s) * ‖p - z‖ ^ 2) ≤
      s * (b + Φ z + 1 / (2 * s) * (‖y - p‖ ^ 2 - 2 * ⟪y - p, z - p⟫_ℝ + ‖p - z‖ ^ 2)) := by
    have e4 : s * (1 / (2 * s)) = 1 / 2 := by field_simp
    nlinarith
  exact le_of_mul_le_mul_left this hs

lemma nfb_theta_le {H : Type*} (Ψ : H → EReal) (Φ : H → ℝ) (u v : H)
    (hu : Ψ u ≠ ⊤) (hu' : Ψ u ≠ ⊥) (hv : Ψ v ≠ ⊤) (hv' : Ψ v ≠ ⊥)
    (h : theta Ψ Φ u ≤ theta Ψ Φ v) :
    (Ψ u).toReal + Φ u ≤ (Ψ v).toReal + Φ v := by
  unfold theta at h
  rw [← EReal.coe_toReal hu hu', ← EReal.coe_toReal hv hv', ← EReal.coe_add,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  exact h

lemma nfb_star_fin {H : Type*} (Ψ : H → EReal) (Φ : H → ℝ)
    (hΨ1 : ∀ x, Ψ x ≠ ⊥) (hΨ2 : ∃ x, Ψ x ≠ ⊤) (xstar : H)
    (hxstar : ∀ y, theta Ψ Φ xstar ≤ theta Ψ Φ y) : Ψ xstar ≠ ⊤ := by
  obtain ⟨u, hu⟩ := hΨ2
  intro htop
  have h := hxstar u
  unfold theta at h
  rw [htop, EReal.top_add_coe, ← EReal.coe_toReal hu (hΨ1 u), ← EReal.coe_add] at h
  exact absurd h (not_le.2 (EReal.coe_lt_top _))

lemma nfb_iter_fin {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : IsProperClosedConvex Ψ) (hP : IsProx s Ψ P)
    (hrun : IsAccelFBRun Φ P α s x) (k : ℕ) (hk : 2 ≤ k) : Ψ (x k) ≠ ⊤ := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [hrun j (by omega)]
  exact ProxOperator.ne_top s Ψ P hΨ hP _

lemma nfb_epi {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ψ : H → EReal) (hΨ : IsProperClosedConvex Ψ) (u v : H) (a b t : ℝ)
    (ha : Ψ u ≤ a) (hb : Ψ v ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ψ ((1 - t) • u + t • v) ≤ (((1 - t) * a + t * b : ℝ) : EReal) := by
  have hm1 : (u, a) ∈ {p : H × ℝ | Ψ p.1 ≤ (p.2 : EReal)} := ha
  have hm2 : (v, b) ∈ {p : H × ℝ | Ψ p.1 ≤ (p.2 : EReal)} := hb
  have hc := hΨ.2.2.2 hm1 hm2 (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
  simpa only [Set.mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
    smul_eq_mul] using hc

lemma nfb_energy_step
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : ℝ≥0) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * (L : ℝ) ≤ 1)
    (hP : IsProx s Ψ P) (hα : 1 < α)
    (hrun : IsAccelFBRun Φ P α s x)
    (xstar : H) (hsf : Ψ xstar ≠ ⊤) (k : ℕ) (hk : 1 ≤ k) (hkf : Ψ (x k) ≠ ⊤) :
    2 * s / (α - 1) * ((k:ℝ) + α - 1) ^ 2 *
        ((Ψ (x (k + 1))).toReal + Φ (x (k + 1)) - ((Ψ xstar).toReal + Φ xstar))
      + (α - 1) * ‖zSeq α x (k + 1) - xstar‖ ^ 2
      + 2 * s / (α - 1) * ((α - 3) * k + (α - 2) ^ 2) *
        ((Ψ (x k)).toReal + Φ (x k) - ((Ψ xstar).toReal + Φ xstar)) ≤
    2 * s / (α - 1) * ((k:ℝ) + α - 2) ^ 2 *
        ((Ψ (x k)).toReal + Φ (x k) - ((Ψ xstar).toReal + Φ xstar))
      + (α - 1) * ‖zSeq α x k - xstar‖ ^ 2 := by
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  set T : ℝ := (k:ℝ) + α - 1 with hT
  have hT0 : 0 < T := by linarith
  set τ : ℝ := (α - 1) / T with hτ
  have hτT : τ * T = α - 1 := by rw [hτ]; field_simp
  have hτ0 : 0 ≤ τ := div_nonneg (by linarith) hT0.le
  have hτ1 : τ ≤ 1 := (div_le_one hT0).2 (by linarith)
  have hk1f : Ψ (x (k + 1)) ≠ ⊤ := nfb_iter_fin Ψ Φ s α P x hΨ hP hrun (k + 1) (by omega)
  set w := (1 - τ) • x k + τ • xstar with hw
  have hΨw := nfb_epi Ψ hΨ (x k) xstar (Ψ (x k)).toReal (Ψ xstar).toReal τ
    (EReal.coe_toReal hkf (hΨ.1 _)).ge (EReal.coe_toReal hsf (hΨ.1 _)).ge hτ0 hτ1
  have hΦw : Φ w ≤ (1 - τ) * Φ (x k) + τ * Φ xstar := by
    have := hΦc.2 (Set.mem_univ (x k)) (Set.mem_univ xstar) (by linarith : (0:ℝ) ≤ 1 - τ) hτ0
      (by ring)
    simpa only [smul_eq_mul] using this
  have hfb := nfb_fb_ineq Ψ Φ L s P hΨ hΦc hΦd hL hs hsL hP (extrap α x k) w
    (Ψ (x (k + 1))).toReal _
    (by rw [← hrun k (by omega)]; exact (EReal.coe_toReal hk1f (hΨ.1 _)).symm) hΨw
  rw [← hrun k (by omega)] at hfb
  have hα1 : (0:ℝ) < α - 1 := by linarith
  clear_value T τ
  have hTne : T ≠ 0 := hT0.ne'
  have hαne : α - 1 ≠ 0 := hα1.ne'
  have c1 : τ * ((k:ℝ) / (α - 1)) = 1 - τ := by
    rw [hτ]; field_simp; rw [hT]; ring
  have c2 : τ * (((k:ℝ) - 1) / (α - 1)) = ((k:ℝ) - 1) / T := by
    rw [hτ]; field_simp
  have e1 : x (k + 1) - w = τ • (zSeq α x (k + 1) - xstar) := by
    unfold zSeq
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Nat.add_sub_cancel]
    rw [hw]
    linear_combination (norm := module) c1 • (x k - x (k + 1))
  have e2 : extrap α x k - w = τ • (zSeq α x k - xstar) := by
    unfold zSeq extrap
    rw [hw, ← hT]
    linear_combination (norm := module) c2 • (x (k - 1) - x k)
  rw [e1, e2, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ0, mul_pow, mul_pow] at hfb
  set F1 := (Ψ (x (k + 1))).toReal + Φ (x (k + 1))
  set Fk := (Ψ (x k)).toReal + Φ (x k)
  set Fs := (Ψ xstar).toReal + Φ xstar
  set Z1 := ‖zSeq α x (k + 1) - xstar‖ ^ 2
  set Zk := ‖zSeq α x k - xstar‖ ^ 2
  have key : F1 - Fs + 1 / (2 * s) * (τ ^ 2 * Z1) ≤ (1 - τ) * (Fk - Fs) + 1 / (2 * s) * (τ ^ 2 * Zk) := by
    simp only [F1, Fk, Fs] at *
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left key (by positivity : (0:ℝ) ≤ 2 * s * T ^ 2 / (α - 1))
  have hkT : 1 - τ = (k:ℝ) / T := by rw [hτ]; field_simp; rw [hT]; ring
  rw [hkT] at hmul
  have r1 : 2 * s * T ^ 2 / (α - 1) * (F1 - Fs + 1 / (2 * s) * (τ ^ 2 * Z1)) =
      2 * s / (α - 1) * T ^ 2 * (F1 - Fs) + (α - 1) * Z1 := by
    rw [hτ]; field_simp
  have r2 : 2 * s * T ^ 2 / (α - 1) * ((k:ℝ) / T * (Fk - Fs) + 1 / (2 * s) * (τ ^ 2 * Zk)) =
      2 * s / (α - 1) * (k * T) * (Fk - Fs) + (α - 1) * Zk := by
    rw [hτ]; field_simp
  rw [r1, r2] at hmul
  have r3 : ((k:ℝ) + α - 2) ^ 2 = k * T + ((α - 3) * k + (α - 2) ^ 2) := by rw [hT]; ring
  rw [r3]
  linarith

lemma nfb_step_decr
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : ℝ≥0) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * (L : ℝ) < 1)
    (hP : IsProx s Ψ P) (hα : 1 < α)
    (hrun : IsAccelFBRun Φ P α s x) (k : ℕ) (hk : 1 ≤ k) (hkf : Ψ (x k) ≠ ⊤) :
    2 * s * ((Ψ (x (k + 1))).toReal + Φ (x (k + 1))) + ‖x (k + 1) - x k‖ ^ 2 ≤
      2 * s * ((Ψ (x k)).toReal + Φ (x k)) +
        (((k:ℝ) - 1) / ((k:ℝ) + α - 1)) ^ 2 * ‖x k - x (k - 1)‖ ^ 2 := by
  have hk1f : Ψ (x (k + 1)) ≠ ⊤ := nfb_iter_fin Ψ Φ s α P x hΨ hP hrun (k + 1) (by omega)
  have hfb := nfb_fb_ineq Ψ Φ L s P hΨ hΦc hΦd hL hs hsL.le hP (extrap α x k) (x k)
    (Ψ (x (k + 1))).toReal (Ψ (x k)).toReal
    (by rw [← hrun k (by omega)]; exact (EReal.coe_toReal hk1f (hΨ.1 _)).symm)
    (EReal.coe_toReal hkf (hΨ.1 _)).ge
  rw [← hrun k (by omega)] at hfb
  have e : extrap α x k - x k = (((k:ℝ) - 1) / ((k:ℝ) + α - 1)) • (x k - x (k - 1)) := by
    unfold extrap; abel
  rw [e, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hfb
  have h2 := mul_le_mul_of_nonneg_left hfb (by positivity : (0:ℝ) ≤ 2 * s)
  have k1 : ∀ X : ℝ, 2 * s * (1 / (2 * s) * X) = X := fun X => by field_simp
  simp only [mul_add, k1] at h2
  linarith

theorem nfb_analysis
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : ℝ≥0) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * (L : ℝ) < 1)
    (hP : IsProx s Ψ P) (hα : 3 < α)
    (hrun : IsAccelFBRun Φ P α s x)
    (xstar : H) (hxstar : ∀ y, theta Ψ Φ xstar ≤ theta Ψ Φ y) :
    Tendsto (fun n : ℕ => ((n:ℝ) + α) ^ 2 *
      ((Ψ (x (n + 2))).toReal + Φ (x (n + 2)) - ((Ψ xstar).toReal + Φ xstar))) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ((n:ℝ) + α) ^ 2 * ‖x (n + 2) - x (n + 1)‖ ^ 2) atTop (𝓝 0) ∧
    ∃ l, Tendsto (fun n : ℕ => ‖zSeq α x (n + 2) - xstar‖ ^ 2) atTop (𝓝 l) := by
  have hsf := nfb_star_fin Ψ Φ hΨ.1 hΨ.2.1 xstar hxstar
  have hθ : ∀ n : ℕ, 0 ≤ (Ψ (x (n + 2))).toReal + Φ (x (n + 2)) - ((Ψ xstar).toReal + Φ xstar) := by
    intro n
    have := nfb_theta_le Ψ Φ xstar (x (n + 2)) hsf (hΨ.1 _)
      (nfb_iter_fin Ψ Φ s α P x hΨ hP hrun (n + 2) (by omega)) (hΨ.1 _) (hxstar _)
    linarith
  apply DiscreteEnergy.limits_of_energy_recursions s α hs hα _ _ _ hθ (fun n => sq_nonneg _) (fun n => sq_nonneg _)
  · intro n
    have h := nfb_energy_step Ψ Φ L s α P x hΨ hΦc hΦd hL hs hsL.le hP (by linarith) hrun xstar hsf (n + 2)
      (by omega) (nfb_iter_fin Ψ Φ s α P x hΨ hP hrun (n + 2) (by omega))
    have c1 : (((n + 2 : ℕ) : ℝ) + α - 1) = (n:ℝ) + α + 1 := by push_cast; ring
    have c2 : (((n + 2 : ℕ) : ℝ) + α - 2) = (n:ℝ) + α := by push_cast; ring
    have c3 : (((n + 2 : ℕ) : ℝ)) = (n:ℝ) + 2 := by push_cast; ring
    rw [c1, c2, c3] at h
    exact h
  · intro n
    have h := nfb_step_decr Ψ Φ L s α P x hΨ hΦc hΦd hL hs hsL hP (by linarith) hrun (n + 2) (by omega)
      (nfb_iter_fin Ψ Φ s α P x hΨ hP hrun (n + 2) (by omega))
    have c1 : (((n + 2 : ℕ) : ℝ) + α - 1) = (n:ℝ) + α + 1 := by push_cast; ring
    have c2 : (((n + 2 : ℕ) : ℝ) - 1) = (n:ℝ) + 1 := by push_cast; ring
    rw [c1, c2] at h
    have e : n + 2 - 1 = n + 1 := by omega
    rw [e] at h
    have e3 : n + 1 + 2 = n + 2 + 1 := by omega
    have e4 : n + 1 + 1 = n + 2 := by omega
    beta_reduce
    rw [e3, e4]
    linarith

lemma nr_theta_fin {H : Type*} (Ψ : H → EReal) (Φ : H → ℝ) (u : H) (hu : Ψ u ≠ ⊤)
    (hb : Ψ u ≠ ⊥) : theta Ψ Φ u = (((Ψ u).toReal + Φ u : ℝ) : EReal) := by
  unfold theta; rw [EReal.coe_add, EReal.coe_toReal hu hb]

theorem theorem_1_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : NNReal) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * L < 1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Ψ P)
    (hrun : IsAccelFBRun Φ P α s x)
    (hα : 3 < α)
    (hS : ∃ xstar : H, ∀ y, theta Ψ Φ xstar ≤ theta Ψ Φ y) :
    Tendsto (fun k : ℕ => (((k : ℝ) ^ 2 : ℝ) : EReal) * (theta Ψ Φ (x k) - ⨅ y, theta Ψ Φ y))
        atTop (𝓝 0) ∧
      Tendsto (fun k : ℕ => (k : ℝ) * ‖x (k + 1) - x k‖) atTop (𝓝 0) := by
  obtain ⟨xstar, hxstar⟩ := hS
  have hinf : ⨅ y, theta Ψ Φ y = theta Ψ Φ xstar := le_antisymm (iInf_le _ _) (le_iInf hxstar)
  rw [hinf]
  have hsf := nfb_star_fin Ψ Φ hΨ.1 hΨ.2.1 xstar hxstar
  obtain ⟨h1, h2, -⟩ := nfb_analysis Ψ Φ L s α P x hΨ hΦc hΦd hL hs hsL hP hα hrun xstar hxstar
  constructor
  · set f : ℕ → ℝ := fun k => (k : ℝ) ^ 2 *
      ((Ψ (x k)).toReal + Φ (x k) - ((Ψ xstar).toReal + Φ xstar)) with hf
    have hfl : Tendsto f atTop (𝓝 0) := by
      rw [← tendsto_add_atTop_iff_nat 2]
      refine squeeze_zero (fun n => ?_) (fun n => ?_) h1
      · have := nfb_theta_le Ψ Φ xstar (x (n + 2)) hsf (hΨ.1 _)
          (nfb_iter_fin Ψ Φ s α P x hΨ hP hrun (n + 2) (by omega)) (hΨ.1 _) (hxstar _)
        simp only [hf]; apply mul_nonneg (sq_nonneg _); linarith
      · have := nfb_theta_le Ψ Φ xstar (x (n + 2)) hsf (hΨ.1 _)
          (nfb_iter_fin Ψ Φ s α P x hΨ hP hrun (n + 2) (by omega)) (hΨ.1 _) (hxstar _)
        simp only [hf]
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        push_cast
        have : (0:ℝ) ≤ n := by positivity
        nlinarith
    have hc := EReal.tendsto_coe.2 hfl
    rw [EReal.coe_zero] at hc
    refine hc.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with k hk
    rw [nr_theta_fin Ψ Φ _ (nfb_iter_fin Ψ Φ s α P x hΨ hP hrun k hk) (hΨ.1 _),
      nr_theta_fin Ψ Φ _ hsf (hΨ.1 _), ← EReal.coe_sub, ← EReal.coe_mul]
  · rw [← tendsto_add_atTop_iff_nat 1]
    have hq := (Real.continuous_sqrt.tendsto 0).comp h2
    rw [Real.sqrt_zero] at hq
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hq
    simp only [Function.comp]
    have e1 : n + 1 + 1 = n + 2 := by omega
    rw [e1]
    rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ ((n + 1 : ℕ) : ℝ) * ‖x (n + 2) - x (n + 1)‖)]
    apply Real.sqrt_le_sqrt
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    push_cast
    have : (0:ℝ) ≤ n := by positivity
    nlinarith

end

section
open Filter Topology InnerProductSpace
open Filter Topology InnerProductSpace NNReal
open NesterovFB.Rates

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : NNReal) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * L < 1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Ψ P)
    (hrun : IsAccelFBRun Φ P α s x)
    (hα : 3 < α)
    (hS : ∃ xstar : H, ∀ y, theta Ψ Φ xstar ≤ theta Ψ Φ y) :
    Tendsto (fun k : ℕ => (((k : ℝ) ^ 2 : ℝ) : EReal) * (theta Ψ Φ (x k) - ⨅ y, theta Ψ Φ y))
        atTop (𝓝 0) ∧
      Tendsto (fun k : ℕ => (k : ℝ) * ‖x (k + 1) - x k‖) atTop (𝓝 0) := by
  exact theorem_1_core Ψ Φ L s α P x hΨ hΦc hΦd hL hs hsL hP hrun hα hS

end
