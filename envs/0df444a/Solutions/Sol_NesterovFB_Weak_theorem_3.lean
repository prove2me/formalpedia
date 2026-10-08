-- Prove2me | solution 1 for NesterovFB.Weak.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T01:21:42.802165+00:00
-- url     : https://prove2.me/submissions/e3454a9c-3502-4c6b-9794-7eebefc4332c

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_NesterovFB_Weak_Algorithm
open Filter Topology NNReal
open InnerProductSpace

namespace NesterovFB.Weak

open ThreeOpSplitting.ConvexRates NesterovFB.Rates

lemma nfb_line_deriv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : H → ℝ) (hd : Differentiable ℝ h) (x v : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => h (x + s • v)) ⟪gradient h (x + t • v), v⟫_ℝ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hf := (hd (x + t • v)).hasFDerivAt
  have := hf.comp_hasDerivAt t hl
  have e : fderiv ℝ h (x + t • v) v = ⟪gradient h (x + t • v), v⟫_ℝ := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  rw [← e]; exact this

lemma nfb_grad_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : H → ℝ) (hc : ConvexOn ℝ Set.univ h) (hd : Differentiable ℝ h) (x y : H) :
    h x + ⟪gradient h x, y - x⟫_ℝ ≤ h y := by
  have hder := nfb_line_deriv h hd x (y - x) 0
  simp only [zero_smul, add_zero] at hder
  have hs := hder.tendsto_slope_zero_right
  simp only [zero_add, smul_eq_mul, zero_smul, add_zero] at hs
  have hle : ∀ t ∈ Set.Ioo (0:ℝ) 1, t⁻¹ * (h (x + t • (y - x)) - h x) ≤ h y - h x := by
    intro t ht
    have hconv := hc.2 (Set.mem_univ x) (Set.mem_univ y) (by linarith [ht.2] : (0:ℝ) ≤ 1 - t)
      ht.1.le (by ring)
    have e : (1 - t) • x + t • y = x + t • (y - x) := by module
    rw [e, smul_eq_mul, smul_eq_mul] at hconv
    rw [inv_mul_le_iff₀ ht.1]
    linarith
  have := le_of_tendsto hs (by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    exact hle t ht)
  linarith

lemma nfb_descent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : H → ℝ) (hd : Differentiable ℝ h) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ x y : H, ‖gradient h x - gradient h y‖ ≤ L * ‖x - y‖) (x y : H) :
    h y ≤ h x + ⟪gradient h x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  set v := y - x with hv
  set ψ : ℝ → ℝ := fun t => h (x + t • v) - t * ⟪gradient h x, v⟫_ℝ - L / 2 * t ^ 2 * ‖v‖ ^ 2
    with hψ
  have hψd : ∀ t, HasDerivAt ψ (⟪gradient h (x + t • v), v⟫_ℝ - ⟪gradient h x, v⟫_ℝ
      - L * t * ‖v‖ ^ 2) t := by
    intro t
    have h1 := nfb_line_deriv h hd x v t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient h x, v⟫_ℝ) ⟪gradient h x, v⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient h x, v⟫_ℝ
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖v‖ ^ 2) (L * t * ‖v‖ ^ 2) t := by
      have hp : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
      have := (hp.const_mul (L / 2)).mul_const (‖v‖ ^ 2)
      exact this.congr_deriv (by ring)
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hψd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hψd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hψd t).deriv]
      have hcs : ⟪gradient h (x + t • v) - gradient h x, v⟫_ℝ ≤
          ‖gradient h (x + t • v) - gradient h x‖ * ‖v‖ := real_inner_le_norm _ _
      have hlip := hL (x + t • v) x
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1] at hlip
      rw [inner_sub_left] at hcs
      have := mul_le_mul_of_nonneg_right hlip (norm_nonneg v)
      nlinarith
  have h01 := hanti ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [hψ, zero_smul, add_zero, zero_mul, sub_zero, one_smul, one_mul, one_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h01
  rw [hv, add_sub_cancel] at h01
  linarith

lemma nfb_real_limit_le {A B C : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → A ≤ B + t * C) : A ≤ B := by
  have ht : Tendsto (fun t : ℝ => B + t * C) (𝓝[>] 0) (𝓝 (B + 0 * C)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
  rw [zero_mul, add_zero] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t htt
  exact h t htt.1 htt.2.le

lemma nfb_prox_fin {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (f : H → EReal) (P : H → H) (hf : IsProperClosedConvex f) (hP : IsProx γ f P)
    (x : H) : f (P x) ≠ ⊤ := by
  obtain ⟨hbot, ⟨x0, hx0⟩, _, _⟩ := hf
  intro htop
  have h1 := hP x x0
  rw [htop, EReal.top_add_coe, ← EReal.coe_toReal hx0 (hbot x0), ← EReal.coe_add] at h1
  exact absurd h1 (not_le.2 (EReal.coe_lt_top _))

lemma nfb_prox_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (hγ : 0 < γ) (f : H → EReal) (P : H → H) (hf : IsProperClosedConvex f)
    (hP : IsProx γ f P) (x y : H) (a b : ℝ) (ha : f (P x) = a) (hb : f y ≤ b) :
    ⟪x - P x, y - P x⟫_ℝ ≤ γ * (b - a) := by
  obtain ⟨hbot, _, _, hconv⟩ := hf
  have key : γ * (a - b) ≤ ⟪P x - x, y - P x⟫_ℝ := by
    have h := nfb_real_limit_le (A := a - b) (B := ⟪P x - x, y - P x⟫_ℝ / γ)
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

/-- Forward-backward inequality. -/
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
  have h2 := nfb_descent Φ hd L L.2 hLip y p
  have h3 := nfb_grad_ineq Φ hΦc hd y z
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
  exact nfb_prox_fin s Ψ P hΨ hP _

/-- norm identity for extrapolation -/
lemma nfb_extrap_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u d : H) (β : ℝ) :
    ‖u + β • d‖ ^ 2 = ‖u‖ ^ 2 + β * (‖u‖ ^ 2 - ‖u - d‖ ^ 2) + (β + β ^ 2) * ‖d‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  ring

theorem delta_core
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : ℝ≥0) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * (L : ℝ) < 1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Ψ P)
    (hα : 3 < α)
    (hrun : NesterovFB.Rates.IsAccelFBRun Φ P α s x)
    (xstar : H) (hxstar : ∀ y, NesterovFB.Rates.theta Ψ Φ xstar ≤ NesterovFB.Rates.theta Ψ Φ y) :
    ∀ k : ℕ, 1 ≤ k →
      deltaSeq α x xstar (k + 1) - deltaSeq α x xstar k ≤
        2 * ((k : ℝ) + α - 1) * ‖x k - x (k - 1)‖ ^ 2 := by
  intro k hk
  have hsf := nfb_star_fin Ψ Φ hΨ.1 hΨ.2.1 xstar hxstar
  have hnf : Ψ (x (k + 1)) ≠ ⊤ := nfb_iter_fin Ψ Φ s α P x hΨ hP hrun (k + 1) (by omega)
  have hmin := nfb_theta_le Ψ Φ xstar (x (k + 1)) hsf (hΨ.1 _) hnf (hΨ.1 _) (hxstar _)
  have hfb := nfb_fb_ineq Ψ Φ L s P hΨ hΦc hΦd hL hs hsL hP (extrap α x k) xstar
    (Ψ (x (k + 1))).toReal (Ψ xstar).toReal
    (by rw [← hrun k hk]; exact (EReal.coe_toReal hnf (hΨ.1 _)).symm)
    (EReal.coe_toReal hsf (hΨ.1 _)).ge
  rw [← hrun k hk] at hfb
  have hsq : ‖x (k + 1) - xstar‖ ^ 2 ≤ ‖extrap α x k - xstar‖ ^ 2 := by
    have hc : 0 < 1 / (2 * s) := by positivity
    nlinarith
  set β := ((k : ℝ) - 1) / ((k : ℝ) + α - 1) with hβ
  have hT : 0 < (k : ℝ) + α - 1 := by linarith
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hβ0 : 0 ≤ β := div_nonneg (by linarith) hT.le
  have hβ1 : β ≤ 1 := (div_le_one hT).2 (by linarith)
  have e : extrap α x k - xstar = (x k - xstar) + β • (x k - x (k - 1)) := by
    unfold extrap; rw [← hβ]; abel
  rw [e, nfb_extrap_sq] at hsq
  have e2 : x k - xstar - (x k - x (k - 1)) = x (k - 1) - xstar := by abel
  rw [e2] at hsq
  unfold deltaSeq
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, add_sub_cancel_right]
  set A := ‖x (k + 1) - xstar‖ ^ 2
  set B := ‖x k - xstar‖ ^ 2
  set C := ‖x (k - 1) - xstar‖ ^ 2
  set D := ‖x k - x (k - 1)‖ ^ 2
  have hD : 0 ≤ D := sq_nonneg _
  have hTβ : ((k : ℝ) + α - 1) * β = (k : ℝ) - 1 := by rw [hβ]; field_simp
  have h1 : ((k : ℝ) + α - 1) * A ≤ ((k : ℝ) + α - 1) * (B + β * (B - C) + (β + β ^ 2) * D) :=
    mul_le_mul_of_nonneg_left hsq hT.le
  have h2 : ((k : ℝ) - 1) * (1 + β) * D ≤ 2 * ((k : ℝ) + α - 1) * D := by
    apply mul_le_mul_of_nonneg_right _ hD
    nlinarith
  have h3 : ((k : ℝ) + α - 1) * (B + β * (B - C) + (β + β ^ 2) * D) =
      ((k : ℝ) + α - 1) * B + (((k : ℝ) + α - 1) * β) * (B - C)
        + (((k : ℝ) + α - 1) * β) * (1 + β) * D := by ring
  rw [h3, hTβ] at h1
  linarith


lemma nfb_epi {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ψ : H → EReal) (hΨ : IsProperClosedConvex Ψ) (u v : H) (a b t : ℝ)
    (ha : Ψ u ≤ a) (hb : Ψ v ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ψ ((1 - t) • u + t • v) ≤ (((1 - t) * a + t * b : ℝ) : EReal) := by
  have hm1 : (u, a) ∈ {p : H × ℝ | Ψ p.1 ≤ (p.2 : EReal)} := ha
  have hm2 : (v, b) ∈ {p : H × ℝ | Ψ p.1 ≤ (p.2 : EReal)} := hb
  have hc := hΨ.2.2.2 hm1 hm2 (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
  simpa only [Set.mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
    smul_eq_mul] using hc

/-- Energy step. -/
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


lemma nfb_telescope (u v : ℕ → ℝ) (h : ∀ n, u (n + 1) + v n ≤ u n) :
    ∀ N, (∑ i ∈ Finset.range N, v i) + u N ≤ u 0 := by
  intro N
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ]; linarith [h N]

lemma nfb_conv_of_incr (u w : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hw0 : ∀ n, 0 ≤ w n)
    (hw : Summable w) (h : ∀ n, u (n + 1) ≤ u n + w n) : ∃ l, Tendsto u atTop (𝓝 l) := by
  set g : ℕ → ℝ := fun n => u n - ∑ i ∈ Finset.range n, w i with hg
  have hanti : Antitone g := by
    apply antitone_nat_of_succ_le
    intro n; simp only [hg, Finset.sum_range_succ]; linarith [h n]
  have hbdd : BddBelow (Set.range g) := by
    refine ⟨-(∑' i, w i), ?_⟩
    rintro _ ⟨n, rfl⟩
    have := hw.sum_le_tsum (Finset.range n) (fun i _ => hw0 i)
    simp only [hg]; linarith [hu n]
  have hgt := tendsto_atTop_ciInf hanti hbdd
  have hst := hw.hasSum.tendsto_sum_nat
  refine ⟨_, (hgt.add hst).congr (fun n => ?_)⟩
  simp only [hg]; ring

lemma nfb_not_summable_shift (α : ℝ) (hα : 1 ≤ α) (c : ℝ) (hc : 0 < c) (h : ℕ → ℝ)
    (N : ℕ) (hh : ∀ n, N ≤ n → c / ((n:ℝ) + α) ≤ h n) (h0 : ∀ n, 0 ≤ h n) :
    ¬ Summable h := by
  intro hs
  have hs' : Summable (fun n => h (n + N)) := (_root_.summable_nat_add_iff N).2 hs
  have hb : Summable (fun n : ℕ => c / α * (1 / (((n + (N + 1) : ℕ)) : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs'
    have h1 := hh (n + N) (by omega)
    refine le_trans ?_ h1
    push_cast
    rw [mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0:ℝ) ≤ n + N := by positivity
    have h5 : (n:ℝ) + N + α ≤ α * ((n:ℝ) + (N + 1)) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h5 hc.le]
  have hb2 : Summable (fun n : ℕ => 1 / (((n + (N + 1) : ℕ)) : ℝ)) := by
    have := hb.mul_left (α / c)
    refine this.congr (fun n => ?_)
    field_simp
  have := (_root_.summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) (N + 1)).1 hb2
  exact Real.not_summable_one_div_natCast this

lemma nfb_lim_zero (α : ℝ) (hα : 1 ≤ α) (G h : ℕ → ℝ) (l : ℝ) (hG : Tendsto G atTop (𝓝 l))
    (hG0 : ∀ n, 0 ≤ G n) (hh0 : ∀ n, 0 ≤ h n) (hs : Summable h)
    (hGh : ∀ n, G n = ((n:ℝ) + α) * h n) : l = 0 := by
  have hl0 : 0 ≤ l := ge_of_tendsto' hG hG0
  by_contra hne
  have hl : 0 < l := lt_of_le_of_ne hl0 (Ne.symm hne)
  have hev : ∀ᶠ n in atTop, l / 2 < G n := hG.eventually (lt_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  apply nfb_not_summable_shift α hα (l / 2) (by linarith) h N _ hh0 hs
  intro n hn
  have := hN n hn
  rw [hGh n] at this
  have hpos : (0:ℝ) < n + α := by positivity
  rw [div_le_iff₀ hpos]; linarith

/-- The abstract real analysis of the energies. -/
theorem nfb_real_core (s α : ℝ) (hs : 0 < s) (hα : 3 < α) (θ dd ez : ℕ → ℝ)
    (hθ : ∀ n, 0 ≤ θ n) (hdd : ∀ n, 0 ≤ dd n) (hez : ∀ n, 0 ≤ ez n)
    (hE : ∀ n : ℕ, 2 * s / (α - 1) * ((n:ℝ) + α + 1) ^ 2 * θ (n + 1) + (α - 1) * ez (n + 1)
        + 2 * s / (α - 1) * ((α - 3) * ((n:ℝ) + 2) + (α - 2) ^ 2) * θ n ≤
        2 * s / (α - 1) * ((n:ℝ) + α) ^ 2 * θ n + (α - 1) * ez n)
    (hS : ∀ n : ℕ, 2 * s * θ (n + 1) + dd (n + 1) ≤
        2 * s * θ n + (((n:ℝ) + 1) / ((n:ℝ) + α + 1)) ^ 2 * dd n) :
    Tendsto (fun n : ℕ => ((n:ℝ) + α) ^ 2 * θ n) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ((n:ℝ) + α) ^ 2 * dd n) atTop (𝓝 0) ∧
    ∃ l, Tendsto ez atTop (𝓝 l) := by
  have hα1 : (0:ℝ) < α - 1 := by linarith
  set e : ℕ → ℝ := fun n => 2 * s / (α - 1) * ((n:ℝ) + α) ^ 2 * θ n + (α - 1) * ez n with he
  have he0 : ∀ n, 0 ≤ e n := fun n => by
    have := hθ n; have := hez n; simp only [he]; positivity
  set c : ℝ := 2 * s * (α - 3) / (α - 1) with hc
  have hc0 : 0 < c := by rw [hc]; apply div_pos _ hα1; nlinarith
  have hEstep : ∀ n : ℕ, e (n + 1) + c * (((n:ℝ) + α) * θ n) ≤ e n := by
    intro n
    have h1 := hE n
    have h2 : c * (((n:ℝ) + α) * θ n) ≤
        2 * s / (α - 1) * ((α - 3) * ((n:ℝ) + 2) + (α - 2) ^ 2) * θ n := by
      rw [hc]
      have hq : 2 * s * (α - 3) / (α - 1) * (((n:ℝ) + α) * θ n) =
          2 * s / (α - 1) * ((α - 3) * ((n:ℝ) + α)) * θ n := by ring
      rw [hq]
      apply mul_le_mul_of_nonneg_right _ (hθ n)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    simp only [he]; push_cast at h1 ⊢
    linarith
  have hsumA : ∀ N, ∑ i ∈ Finset.range N, c * (((i:ℝ) + α) * θ i) ≤ e 0 := by
    intro N
    have := nfb_telescope e _ hEstep N
    linarith [he0 N]
  set a : ℕ → ℝ := fun n => ((n:ℝ) + α) * θ n with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n => by have := hθ n; simp only [ha]; positivity
  have hsa : Summable a := by
    apply summable_of_sum_range_le ha0 (c := e 0 / c)
    intro N
    rw [le_div_iff₀ hc0, Finset.sum_mul]
    have := hsumA N
    simp only [ha]
    calc ∑ i ∈ Finset.range N, ((i:ℝ) + α) * θ i * c
        = ∑ i ∈ Finset.range N, c * (((i:ℝ) + α) * θ i) := by
          apply Finset.sum_congr rfl; intro i _; ring
      _ ≤ e 0 := this
  set G : ℕ → ℝ := fun n => ((n:ℝ) + α) ^ 2 * (2 * s * θ n + dd n) with hG
  have hG0 : ∀ n, 0 ≤ G n := fun n => by
    have := hθ n; have := hdd n; simp only [hG]; positivity
  have hGstep : ∀ n : ℕ, G (n + 1) + (α - 1) * (((n:ℝ) + α) * dd n) ≤ G n + 6 * s * a n := by
    intro n
    have h1 := hS n
    have hT : (0:ℝ) < (n:ℝ) + α + 1 := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ((n:ℝ) + α + 1))
    have e3 : ((n:ℝ) + α + 1) ^ 2 * (2 * s * θ n + (((n:ℝ) + 1) / ((n:ℝ) + α + 1)) ^ 2 * dd n)
        = ((n:ℝ) + α + 1) ^ 2 * (2 * s * θ n) + ((n:ℝ) + 1) ^ 2 * dd n := by
      field_simp
    rw [e3] at h2
    simp only [hG, ha]; push_cast
    have hdn := hdd n
    have hθn := hθ n
    have k1 : (α - 1) * (((n:ℝ) + α) * dd n) ≤ (α - 1) * (2 * (n:ℝ) + α + 1) * dd n := by
      have : (α - 1) * (((n:ℝ) + α)) ≤ (α - 1) * (2 * (n:ℝ) + α + 1) := by
        apply mul_le_mul_of_nonneg_left _ hα1.le; have : (0:ℝ) ≤ n := by positivity
        linarith
      nlinarith
    have k2 : 2 * s * (2 * (n:ℝ) + 2 * α + 1) * θ n ≤ 6 * s * (((n:ℝ) + α) * θ n) := by
      have : (0:ℝ) ≤ n := by positivity
      have : 2 * s * (2 * (n:ℝ) + 2 * α + 1) ≤ 6 * s * ((n:ℝ) + α) := by nlinarith
      nlinarith
    nlinarith
  set b : ℕ → ℝ := fun n => ((n:ℝ) + α) * dd n with hb
  have hb0 : ∀ n, 0 ≤ b n := fun n => by have := hdd n; simp only [hb]; positivity
  have hsb : Summable b := by
    apply summable_of_sum_range_le hb0 (c := (G 0 + 6 * s * ∑' i, a i) / (α - 1))
    intro N
    rw [le_div_iff₀ hα1, Finset.sum_mul]
    have h1 := nfb_telescope G (fun n => (α - 1) * b n - 6 * s * a n)
      (fun n => by have := hGstep n; simp only [hb]; linarith) N
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
    have h2 := hsa.sum_le_tsum (Finset.range N) (fun i _ => ha0 i)
    have h3 : ∑ i ∈ Finset.range N, b i * (α - 1) = (α - 1) * ∑ i ∈ Finset.range N, b i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [h3]
    have := hG0 N
    nlinarith
  obtain ⟨lG, hlG⟩ := nfb_conv_of_incr G (fun n => 6 * s * a n) hG0
    (fun n => by have := ha0 n; positivity) (hsa.mul_left _)
    (fun n => by have := hGstep n; have := hb0 n; simp only [hb] at *; nlinarith)
  have hlG0 : lG = 0 := by
    apply nfb_lim_zero α (by linarith) G (fun n => 2 * s * a n + b n) lG hlG hG0
      (fun n => by have := ha0 n; have := hb0 n; positivity) ((hsa.mul_left _).add hsb)
    intro n; simp only [hG, ha, hb]; ring
  rw [hlG0] at hlG
  refine ⟨?_, ?_, ?_⟩
  · have hup : ∀ n : ℕ, ((n:ℝ) + α) ^ 2 * θ n ≤ G n / (2 * s) := by
      intro n
      rw [le_div_iff₀ (by positivity)]
      simp only [hG]
      have := hdd n
      have : (0:ℝ) ≤ ((n:ℝ) + α) ^ 2 * dd n := by positivity
      nlinarith
    have hlim : Tendsto (fun n => G n / (2 * s)) atTop (𝓝 0) := by
      simpa using hlG.div_const (2 * s)
    exact squeeze_zero (fun n => by have := hθ n; positivity) hup hlim
  · have hup : ∀ n : ℕ, ((n:ℝ) + α) ^ 2 * dd n ≤ G n := by
      intro n
      simp only [hG]
      have := hθ n
      have : (0:ℝ) ≤ ((n:ℝ) + α) ^ 2 * (2 * s * θ n) := by positivity
      nlinarith
    exact squeeze_zero (fun n => by have := hdd n; positivity) hup hlG
  · have hanti : Antitone e := by
      apply antitone_nat_of_succ_le
      intro n; have := hEstep n; have := ha0 n
      have : 0 ≤ c * (((n:ℝ) + α) * θ n) := by positivity
      linarith
    have hbdd : BddBelow (Set.range e) := ⟨0, by rintro _ ⟨n, rfl⟩; exact he0 n⟩
    have het := tendsto_atTop_ciInf hanti hbdd
    have hθl : Tendsto (fun n : ℕ => ((n:ℝ) + α) ^ 2 * θ n) atTop (𝓝 0) := by
      have hup : ∀ n : ℕ, ((n:ℝ) + α) ^ 2 * θ n ≤ G n / (2 * s) := by
        intro n
        rw [le_div_iff₀ (by positivity)]
        simp only [hG]
        have := hdd n
        have : (0:ℝ) ≤ ((n:ℝ) + α) ^ 2 * dd n := by positivity
        nlinarith
      have hlim : Tendsto (fun n => G n / (2 * s)) atTop (𝓝 0) := by
        simpa using hlG.div_const (2 * s)
      exact squeeze_zero (fun n => by have := hθ n; positivity) hup hlim
    refine ⟨_, ((het.sub (hθl.const_mul (2 * s / (α - 1)))).div_const (α - 1)).congr (fun n => ?_)⟩
    simp only [he]
    field_simp
    ring


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
  apply nfb_real_core s α hs hα _ _ _ hθ (fun n => sq_nonneg _) (fun n => sq_nonneg _)
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

theorem zSeq_core
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : ℝ≥0) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * (L : ℝ) < 1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Ψ P)
    (hα : 3 < α)
    (hrun : NesterovFB.Rates.IsAccelFBRun Φ P α s x)
    (xstar : H) (hxstar : ∀ y, NesterovFB.Rates.theta Ψ Φ xstar ≤ NesterovFB.Rates.theta Ψ Φ y) :
    ∃ l : ℝ, Tendsto (fun k => ‖NesterovFB.Rates.zSeq α x k - xstar‖) atTop (𝓝 l) := by
  obtain ⟨l, h1, -⟩ := nfb_lims Ψ Φ L s α P x hΨ hΦc hΦd hL hs hsL hP hα hrun xstar hxstar
  exact ⟨l, h1⟩

theorem dist_core
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : ℝ≥0) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * (L : ℝ) < 1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Ψ P)
    (hα : 3 < α)
    (hrun : NesterovFB.Rates.IsAccelFBRun Φ P α s x)
    (xstar : H) (hxstar : ∀ y, NesterovFB.Rates.theta Ψ Φ xstar ≤ NesterovFB.Rates.theta Ψ Φ y) :
    ∃ l : ℝ, Tendsto (fun k => ‖x k - xstar‖) atTop (𝓝 l) := by
  obtain ⟨l, -, h2⟩ := nfb_lims Ψ Φ L s α P x hΨ hΦc hΦd hL hs hsL hP hα hrun xstar hxstar
  exact ⟨l, h2⟩

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

/-- Weak cluster points are minimizers. -/
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

end NesterovFB.Weak

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
