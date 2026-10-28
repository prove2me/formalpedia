-- Prove2me | solution 2 for NesterovFB.Weak.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T10:57:17.989041+00:00
-- url     : https://prove2.me/submissions/3aa0e31b-0646-4e61-af97-d66f6daccca2

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_NesterovFB_Weak_Algorithm
import Theorems.Thm_Gradient_descent_lemma_gradient
import Theorems.Thm_Gradient_convex_first_order_gradient
import Theorems.Thm_ProxOperator_ne_top
import Theorems.Thm_DiscreteEnergy_limits_of_energy_recursions
import Theorems.Thm_Real_le_of_le_add_mul_of_mem_Ioc

-- carved verbatim out of submission e3454a9c-3502-4c6b-9794-7eebefc4332c, lines 947-961

section
open Filter Topology NNReal
open InnerProductSpace
open NesterovFB
open NesterovFB.Weak
open ThreeOpSplitting.ConvexRates NesterovFB.Rates

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
    (hs : 0 < s) (hsL : s * (L : ℝ) < 1)
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
    (hs : 0 < s) (hsL : s * (L : ℝ) < 1)
    (hP : IsProx s Ψ P) (hα : 3 < α)
    (hrun : IsAccelFBRun Φ P α s x)
    (xstar : H) (hsf : Ψ xstar ≠ ⊤) (k : ℕ) (hk : 2 ≤ k) :
    2 * s / (α - 1) * ((k:ℝ) + α - 1) ^ 2 *
        ((Ψ (x (k + 1))).toReal + Φ (x (k + 1)) - ((Ψ xstar).toReal + Φ xstar))
      + (α - 1) * ‖zSeq α x (k + 1) - xstar‖ ^ 2
      + 2 * s / (α - 1) * ((α - 3) * k + (α - 2) ^ 2) *
        ((Ψ (x k)).toReal + Φ (x k) - ((Ψ xstar).toReal + Φ xstar)) ≤
    2 * s / (α - 1) * ((k:ℝ) + α - 2) ^ 2 *
        ((Ψ (x k)).toReal + Φ (x k) - ((Ψ xstar).toReal + Φ xstar))
      + (α - 1) * ‖zSeq α x k - xstar‖ ^ 2 := by
  have hk1 : (2:ℝ) ≤ k := by exact_mod_cast hk
  set T : ℝ := (k:ℝ) + α - 1 with hT
  have hT0 : 0 < T := by linarith
  set τ : ℝ := (α - 1) / T with hτ
  have hτT : τ * T = α - 1 := by rw [hτ]; field_simp
  have hτ0 : 0 ≤ τ := div_nonneg (by linarith) hT0.le
  have hτ1 : τ ≤ 1 := (div_le_one hT0).2 (by linarith)
  have hkf : Ψ (x k) ≠ ⊤ := nfb_iter_fin Ψ Φ s α P x hΨ hP hrun k hk
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
    (hP : IsProx s Ψ P) (hα : 3 < α)
    (hrun : IsAccelFBRun Φ P α s x) (k : ℕ) (hk : 2 ≤ k) :
    2 * s * ((Ψ (x (k + 1))).toReal + Φ (x (k + 1))) + ‖x (k + 1) - x k‖ ^ 2 ≤
      2 * s * ((Ψ (x k)).toReal + Φ (x k)) +
        (((k:ℝ) - 1) / ((k:ℝ) + α - 1)) ^ 2 * ‖x k - x (k - 1)‖ ^ 2 := by
  have hkf : Ψ (x k) ≠ ⊤ := nfb_iter_fin Ψ Φ s α P x hΨ hP hrun k hk
  have hk1f : Ψ (x (k + 1)) ≠ ⊤ := nfb_iter_fin Ψ Φ s α P x hΨ hP hrun (k + 1) (by omega)
  have hfb := nfb_fb_ineq Ψ Φ L s P hΨ hΦc hΦd hL hs hsL hP (extrap α x k) (x k)
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
    have h := nfb_energy_step Ψ Φ L s α P x hΨ hΦc hΦd hL hs hsL hP hα hrun xstar hsf (n + 2)
      (by omega)
    have c1 : (((n + 2 : ℕ) : ℝ) + α - 1) = (n:ℝ) + α + 1 := by push_cast; ring
    have c2 : (((n + 2 : ℕ) : ℝ) + α - 2) = (n:ℝ) + α := by push_cast; ring
    have c3 : (((n + 2 : ℕ) : ℝ)) = (n:ℝ) + 2 := by push_cast; ring
    rw [c1, c2, c3] at h
    exact h
  · intro n
    have h := nfb_step_decr Ψ Φ L s α P x hΨ hΦc hΦd hL hs hsL hP hα hrun (n + 2) (by omega)
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

theorem nfb_lims
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : ℝ≥0) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * (L : ℝ) < 1)
    (hP : IsProx s Ψ P) (hα : 3 < α)
    (hrun : IsAccelFBRun Φ P α s x)
    (xstar : H) (hxstar : ∀ y, theta Ψ Φ xstar ≤ theta Ψ Φ y) :
    ∃ l : ℝ, Tendsto (fun k => ‖zSeq α x k - xstar‖) atTop (𝓝 l) ∧
      Tendsto (fun k => ‖x k - xstar‖) atTop (𝓝 l) := by
  obtain ⟨_, hd, l, hz⟩ := nfb_analysis Ψ Φ L s α P x hΨ hΦc hΦd hL hs hsL hP hα hrun xstar hxstar
  have hz' : Tendsto (fun n : ℕ => ‖zSeq α x (n + 2) - xstar‖) atTop (𝓝 (Real.sqrt l)) := by
    have := hz.sqrt
    refine this.congr (fun n => ?_)
    exact Real.sqrt_sq (norm_nonneg _)
  have hα1 : (0:ℝ) < α - 1 := by linarith
  have hd' : Tendsto (fun n : ℕ => ((n:ℝ) + α) * ‖x (n + 2) - x (n + 1)‖) atTop (𝓝 0) := by
    have := hd.sqrt
    rw [Real.sqrt_zero] at this
    refine this.congr (fun n => ?_)
    rw [← mul_pow, Real.sqrt_sq]
    have : (0:ℝ) ≤ n := by positivity
    have : (0:ℝ) ≤ (n:ℝ) + α := by linarith
    positivity
  have hdiff : Tendsto (fun n : ℕ => ‖x (n + 2) - xstar‖ - ‖zSeq α x (n + 2) - xstar‖) atTop
      (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ => ((n:ℝ) + α) * ‖x (n + 2) - x (n + 1)‖ / (α - 1)) atTop
        (𝓝 0) := by simpa using hd'.div_const (α - 1)
    apply squeeze_zero_norm _ hb
    intro n
    rw [Real.norm_eq_abs]
    refine (abs_norm_sub_norm_le _ _).trans ?_
    have e : x (n + 2) - xstar - (zSeq α x (n + 2) - xstar) =
        -((((n:ℝ) + 1) / (α - 1)) • (x (n + 2) - x (n + 1))) := by
      unfold zSeq
      have e1 : n + 2 - 1 = n + 1 := by omega
      have e2 : (((n + 2 : ℕ) : ℝ) - 1) = (n:ℝ) + 1 := by push_cast; ring
      rw [e1, e2]; abel
    rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hα1]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    linarith
  refine ⟨Real.sqrt l, ?_, ?_⟩
  · exact (Filter.tendsto_add_atTop_iff_nat 2).1 hz'
  · apply (Filter.tendsto_add_atTop_iff_nat 2).1
    have := hz'.add hdiff
    rw [add_zero] at this
    refine this.congr (fun n => ?_)
    ring

lemma nfb_real_ulim_exists (f : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |f k| ≤ M) (U : Ultrafilter ℕ) :
    ∃ a, Tendsto f U (𝓝 a) := by
  have hc : IsCompact (Set.Icc (-M) M) := isCompact_Icc
  obtain ⟨a, -, ha⟩ := hc.ultrafilter_le_nhds (U.map f) (by
    rw [Filter.le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
    exact Filter.univ_mem' (fun k => abs_le.1 (hM k)))
  exact ⟨a, ha⟩

lemma nfb_exists_ulim {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) (M : ℝ) (hM : ∀ k, ‖u k‖ ≤ M) (U : Ultrafilter ℕ) :
    ∃ w : H, ∀ y, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 (inner ℝ w y)) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hb : ∀ y k, |inner ℝ (u k) y| ≤ M * ‖y‖ := fun y k =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM k) (norm_nonneg _))
  have hex : ∀ y, ∃ a, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 a) :=
    fun y => nfb_real_ulim_exists _ _ (hb y) U
  set L : H → ℝ := fun y => limUnder (U : Filter ℕ) (fun k => inner ℝ (u k) y) with hL
  have hLt : ∀ y, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 (L y)) :=
    fun y => tendsto_nhds_limUnder (hex y)
  have hadd : ∀ y y', L (y + y') = L y + L y' := by
    intro y y'
    have h1 := hLt (y + y')
    have h2 := (hLt y).add (hLt y')
    simp only [inner_add_right] at h1
    exact tendsto_nhds_unique h1 h2
  have hsmul : ∀ (c : ℝ) y, L (c • y) = c * L y := by
    intro c y
    have h1 := hLt (c • y)
    have h2 := (hLt y).const_mul c
    simp only [real_inner_smul_right] at h1
    exact tendsto_nhds_unique h1 h2
  let Ll : H →ₗ[ℝ] ℝ :=
    { toFun := L, map_add' := hadd, map_smul' := fun c y => by simp [hsmul] }
  have hbd : ∀ y, ‖Ll y‖ ≤ M * ‖y‖ := by
    intro y
    show |L y| ≤ M * ‖y‖
    have := (hLt y)
    have hmem : ∀ᶠ k in (U : Filter ℕ), inner ℝ (u k) y ∈ Set.Icc (-(M * ‖y‖)) (M * ‖y‖) :=
      Filter.Eventually.of_forall (fun k => abs_le.1 (hb y k))
    exact abs_le.2 (isClosed_Icc.mem_of_tendsto this hmem)
  let Lc : StrongDual ℝ H := Ll.mkContinuous M hbd
  refine ⟨(InnerProductSpace.toDual ℝ H).symm Lc, fun y => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  exact hLt y

lemma nfb_weak_of_ulim {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) (M : ℝ) (hM : ∀ k, ‖u k‖ ≤ M) (w0 : H)
    (h : ∀ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ atTop → ∀ w : H,
      (∀ y, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 (inner ℝ w y))) → w = w0) :
    ThreeOpSplitting.Convergence.WeakTendsto u w0 := by
  intro y
  rw [tendsto_iff_ultrafilter]
  intro U hU
  obtain ⟨w, hw⟩ := nfb_exists_ulim u M hM U
  have := h U hU w hw
  subst this
  exact hw y

lemma nfb_opial_unique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (z : ℕ → H) (w1 w2 : H) (U1 U2 : Ultrafilter ℕ)
    (h1 : (U1 : Filter ℕ) ≤ atTop) (h2 : (U2 : Filter ℕ) ≤ atTop)
    (hw1 : ∀ y, Tendsto (fun k => inner ℝ (z k) y) U1 (𝓝 (inner ℝ w1 y)))
    (hw2 : ∀ y, Tendsto (fun k => inner ℝ (z k) y) U2 (𝓝 (inner ℝ w2 y)))
    (hc1 : ∃ d, Tendsto (fun k => ‖z k - w1‖) atTop (𝓝 d))
    (hc2 : ∃ d, Tendsto (fun k => ‖z k - w2‖) atTop (𝓝 d)) : w1 = w2 := by
  obtain ⟨d1, hd1⟩ := hc1
  obtain ⟨d2, hd2⟩ := hc2
  set v := w1 - w2 with hv
  have hg : Tendsto (fun k => ‖z k - w2‖ ^ 2 - ‖z k - w1‖ ^ 2) atTop (𝓝 (d2 ^ 2 - d1 ^ 2)) :=
    (hd2.pow 2).sub (hd1.pow 2)
  have hid : ∀ k, ‖z k - w2‖ ^ 2 - ‖z k - w1‖ ^ 2 =
      2 * inner ℝ (z k) v - 2 * inner ℝ w1 v + ‖v‖ ^ 2 := by
    intro k
    have e : z k - w2 = (z k - w1) + v := by rw [hv]; abel
    rw [e, norm_add_sq_real, inner_sub_left]; ring
  simp only [hid] at hg
  have g1 : Tendsto (fun k => 2 * inner ℝ (z k) v - 2 * inner ℝ w1 v + ‖v‖ ^ 2) U1
      (𝓝 (2 * inner ℝ w1 v - 2 * inner ℝ w1 v + ‖v‖ ^ 2)) :=
    (((hw1 v).const_mul 2).sub tendsto_const_nhds).add tendsto_const_nhds
  have g2 : Tendsto (fun k => 2 * inner ℝ (z k) v - 2 * inner ℝ w1 v + ‖v‖ ^ 2) U2
      (𝓝 (2 * inner ℝ w2 v - 2 * inner ℝ w1 v + ‖v‖ ^ 2)) :=
    (((hw2 v).const_mul 2).sub tendsto_const_nhds).add tendsto_const_nhds
  have e1 := tendsto_nhds_unique g1 (hg.mono_left h1)
  have e2 := tendsto_nhds_unique g2 (hg.mono_left h2)
  have e3 : inner ℝ w2 v - inner ℝ w1 v = -‖v‖ ^ 2 := by
    rw [← inner_sub_left, ← real_inner_self_eq_norm_sq, hv, ← inner_neg_left, neg_sub]
  have : ‖v‖ ^ 2 = 0 := by nlinarith
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  rw [norm_eq_zero, hv, sub_eq_zero] at this
  exact this

lemma nfb_ereal_add_le (e : EReal) (a c : ℝ) : e + (a : EReal) ≤ (c : EReal) ↔ e ≤ ((c - a : ℝ) : EReal) := by
  induction e using EReal.rec with
  | bot => simp
  | top => rw [EReal.top_add_coe]; simp only [top_le_iff, EReal.coe_ne_top]
  | coe r =>
    rw [← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

lemma nfb_sublevel_closed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ψ : H → EReal) (Φ : H → ℝ) (hΨ : IsProperClosedConvex Ψ) (hΦ : Continuous Φ) (c : ℝ) :
    IsClosed {u | theta Ψ Φ u ≤ (c : EReal)} := by
  have hlsc : LowerSemicontinuous (fun u => Ψ u + ((Φ u : ℝ) : EReal)) := by
    apply LowerSemicontinuous.add' hΨ.2.2.1
    · exact (continuous_coe_real_ereal.comp hΦ).lowerSemicontinuous
    · intro u
      apply EReal.continuousAt_add
      · right; exact EReal.coe_ne_bot _
      · right; exact EReal.coe_ne_top _
  exact hlsc.isClosed_preimage (c : EReal)

lemma nfb_sublevel_convex {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ψ : H → EReal) (Φ : H → ℝ) (hΨ : IsProperClosedConvex Ψ) (hΦc : ConvexOn ℝ Set.univ Φ)
    (c : ℝ) : Convex ℝ {u | theta Ψ Φ u ≤ (c : EReal)} := by
  intro u hu v hv a b ha hb hab
  obtain rfl : a = 1 - b := by linarith
  simp only [Set.mem_setOf_eq, theta] at hu hv ⊢
  rw [nfb_ereal_add_le] at hu hv ⊢
  have h1 := nfb_epi Ψ hΨ u v _ _ b hu hv hb (by linarith)
  have h2 : Φ ((1 - b) • u + b • v) ≤ (1 - b) * Φ u + b * Φ v := by
    have := hΦc.2 (Set.mem_univ u) (Set.mem_univ v) ha hb hab
    simpa only [smul_eq_mul] using this
  refine h1.trans ?_
  rw [EReal.coe_le_coe_iff]
  nlinarith

lemma nfb_cluster_min
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : ℝ≥0) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * (L : ℝ) < 1)
    (hP : IsProx s Ψ P) (hα : 3 < α)
    (hrun : IsAccelFBRun Φ P α s x)
    (xstar : H) (hxstar : ∀ y, theta Ψ Φ xstar ≤ theta Ψ Φ y)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (w : H)
    (hw : ∀ y, Tendsto (fun k => inner ℝ (x k) y) U (𝓝 (inner ℝ w y))) :
    ∀ y, theta Ψ Φ w ≤ theta Ψ Φ y := by
  have hsf := nfb_star_fin Ψ Φ hΨ.1 hΨ.2.1 xstar hxstar
  suffices h : theta Ψ Φ w ≤ theta Ψ Φ xstar from fun y => h.trans (hxstar y)
  by_contra hlt
  push_neg at hlt
  set Fs := (Ψ xstar).toReal + Φ xstar with hFs
  have hts : theta Ψ Φ xstar = (Fs : EReal) := by
    unfold theta; rw [hFs, EReal.coe_add, EReal.coe_toReal hsf (hΨ.1 _)]
  rw [hts] at hlt
  obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  rw [EReal.coe_lt_coe_iff] at hc1
  set C := {u | theta Ψ Φ u ≤ (c : EReal)} with hC
  have hCc : IsClosed C := nfb_sublevel_closed Ψ Φ hΨ hΦd.continuous c
  have hCv : Convex ℝ C := nfb_sublevel_convex Ψ Φ hΨ hΦc c
  have hxs : xstar ∈ C := by
    show theta Ψ Φ xstar ≤ (c : EReal); rw [hts]; exact_mod_cast hc1.le
  have hwC : w ∉ C := fun h => absurd h (not_le.2 hc2)
  -- eventually iterates in C
  obtain ⟨hθ, -, -⟩ := nfb_analysis Ψ Φ L s α P x hΨ hΦc hΦd hL hs hsL hP hα hrun xstar hxstar
  have hθ' : Tendsto (fun n : ℕ => (Ψ (x (n + 2))).toReal + Φ (x (n + 2)) - Fs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => ?_) (fun n => ?_) hθ
    · have := nfb_theta_le Ψ Φ xstar (x (n + 2)) hsf (hΨ.1 _)
        (nfb_iter_fin Ψ Φ s α P x hΨ hP hrun (n + 2) (by omega)) (hΨ.1 _) (hxstar _)
      linarith
    · have h0 : 0 ≤ (Ψ (x (n + 2))).toReal + Φ (x (n + 2)) - Fs := by
        have := nfb_theta_le Ψ Φ xstar (x (n + 2)) hsf (hΨ.1 _)
          (nfb_iter_fin Ψ Φ s α P x hΨ hP hrun (n + 2) (by omega)) (hΨ.1 _) (hxstar _)
        linarith
      have h1 : (1:ℝ) ≤ ((n:ℝ) + α) ^ 2 := by
        have : (0:ℝ) ≤ n := by positivity
        nlinarith
      nlinarith
  have hev : ∀ᶠ n in atTop, (Ψ (x (n + 2))).toReal + Φ (x (n + 2)) - Fs < c - Fs :=
    hθ'.eventually (gt_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hevC : ∀ᶠ k in atTop, x k ∈ C := by
    rw [eventually_atTop]
    refine ⟨N + 2, fun k hk => ?_⟩
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    have := hN n (by omega)
    show theta Ψ Φ (x (n + 2)) ≤ (c : EReal)
    unfold theta
    rw [← EReal.coe_toReal (nfb_iter_fin Ψ Φ s α P x hΨ hP hrun (n + 2) (by omega)) (hΨ.1 _),
      ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith
  -- projection
  obtain ⟨q, hqC, hq⟩ := exists_norm_eq_iInf_of_complete_convex ⟨xstar, hxs⟩ hCc.isComplete hCv w
  have hvi := (norm_eq_iInf_iff_real_inner_le_zero hCv hqC).1 hq
  have hev2 : ∀ᶠ k in (U : Filter ℕ), inner ℝ (x k) (w - q) - inner ℝ q (w - q) ≤ 0 := by
    apply hU
    filter_upwards [hevC] with k hk
    have := hvi (x k) hk
    rw [real_inner_comm, inner_sub_left] at this
    exact this
  have hlim : Tendsto (fun k => inner ℝ (x k) (w - q) - inner ℝ q (w - q)) U
      (𝓝 (inner ℝ w (w - q) - inner ℝ q (w - q))) := (hw (w - q)).sub tendsto_const_nhds
  have hle := le_of_tendsto hlim hev2
  rw [← inner_sub_left, real_inner_self_eq_norm_sq] at hle
  have : ‖w - q‖ = 0 := by nlinarith [norm_nonneg (w - q)]
  rw [norm_eq_zero, sub_eq_zero] at this
  exact hwC (this ▸ hqC)

theorem thm3_core
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : ℝ≥0) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * (L : ℝ) < 1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Ψ P)
    (hα : 3 < α)
    (hrun : NesterovFB.Rates.IsAccelFBRun Φ P α s x)
    (hS : ∃ xstar, ∀ y, NesterovFB.Rates.theta Ψ Φ xstar ≤ NesterovFB.Rates.theta Ψ Φ y) :
    ∃ xbar : H, (∀ y, NesterovFB.Rates.theta Ψ Φ xbar ≤ NesterovFB.Rates.theta Ψ Φ y) ∧
      ThreeOpSplitting.Convergence.WeakTendsto x xbar := by
  obtain ⟨xstar, hxstar⟩ := hS
  obtain ⟨l, -, hl⟩ := nfb_lims Ψ Φ L s α P x hΨ hΦc hΦd hL hs hsL hP hα hrun xstar hxstar
  obtain ⟨B, hB⟩ := hl.bddAbove_range
  have hM : ∀ k, ‖x k‖ ≤ B + ‖xstar‖ := by
    intro k
    have h1 : ‖x k - xstar‖ ≤ B := hB ⟨k, rfl⟩
    have h2 := norm_le_insert' (x k) xstar
    linarith
  obtain ⟨U0, hU0⟩ := (atTop : Filter ℕ).exists_ultrafilter_le
  obtain ⟨w0, hw0⟩ := nfb_exists_ulim x _ hM U0
  have hmin0 := nfb_cluster_min Ψ Φ L s α P x hΨ hΦc hΦd hL hs hsL hP hα hrun xstar hxstar
    U0 hU0 w0 hw0
  refine ⟨w0, hmin0, nfb_weak_of_ulim x _ hM w0 (fun U hU w hw => ?_)⟩
  have hmin := nfb_cluster_min Ψ Φ L s α P x hΨ hΦc hΦd hL hs hsL hP hα hrun xstar hxstar
    U hU w hw
  obtain ⟨l1, -, h1⟩ := nfb_lims Ψ Φ L s α P x hΨ hΦc hΦd hL hs hsL hP hα hrun w hmin
  obtain ⟨l2, -, h2⟩ := nfb_lims Ψ Φ L s α P x hΨ hΦc hΦd hL hs hsL hP hα hrun w0 hmin0
  exact nfb_opial_unique x w w0 U U0 hU hU0 hw hw0 ⟨l1, h1⟩ ⟨l2, h2⟩

end

section
open Filter Topology NNReal
open InnerProductSpace
open NesterovFB.Weak

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : ℝ≥0) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * (L : ℝ) < 1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Ψ P)
    (hα : 3 < α)
    (hrun : NesterovFB.Rates.IsAccelFBRun Φ P α s x)
    (hS : ∃ xstar, ∀ y, NesterovFB.Rates.theta Ψ Φ xstar ≤ NesterovFB.Rates.theta Ψ Φ y) :
    ∃ xbar : H, (∀ y, NesterovFB.Rates.theta Ψ Φ xbar ≤ NesterovFB.Rates.theta Ψ Φ y) ∧
      ThreeOpSplitting.Convergence.WeakTendsto x xbar := by
  exact thm3_core Ψ Φ L s α P x hΨ hΦc hΦd hL hs hsL hP hα hrun hS

end
