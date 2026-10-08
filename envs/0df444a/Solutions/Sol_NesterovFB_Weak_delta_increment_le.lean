-- Prove2me | solution 1 for NesterovFB.Weak.delta_increment_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T01:08:25.371985+00:00
-- url     : https://prove2.me/submissions/c2a6adbe-b12f-4bc9-81f3-e8ea83f2bc92

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
    (xstar : H) (hxstar : ∀ y, NesterovFB.Rates.theta Ψ Φ xstar ≤ NesterovFB.Rates.theta Ψ Φ y) :
    ∀ k : ℕ, 1 ≤ k →
      deltaSeq α x xstar (k + 1) - deltaSeq α x xstar k ≤
        2 * ((k : ℝ) + α - 1) * ‖x k - x (k - 1)‖ ^ 2 := by
  exact delta_core Ψ Φ L s α P x hΨ hΦc hΦd hL hs hsL hP hα hrun xstar hxstar
