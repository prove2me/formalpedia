-- Prove2me | solution 1 for NAGFlow.PredCorr.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T21:38:16.912154+00:00
-- url     : https://prove2.me/submissions/23449cd5-7acb-4045-85e4-ec8a2e0eebf6

import Mathlib
import Definitions.Def_NAGFlow_PredCorr_Setting

namespace RRAux_NAGFlow_PredCorr_theorem_5_1

lemma descent {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ x, HasGradientAt f (gradf x) x) (hlip : ∀ x y, ‖gradf x - gradf y‖ ≤ L * ‖x - y‖)
    (x y : V) : f y ≤ f x + inner ℝ (gradf x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  set h := y - x
  let φ : ℝ → ℝ := fun t => f (x + t • h) - t * inner ℝ (gradf x) h - L / 2 * t ^ 2 * ‖h‖ ^ 2
  have hd : ∀ t, HasDerivAt φ (inner ℝ (gradf (x + t • h)) h - inner ℝ (gradf x) h
      - L * t * ‖h‖ ^ 2) t := by
    intro t
    have hl : HasDerivAt (fun s : ℝ => x + s • h) h t := by
      exact (((hasDerivAt_id t).smul_const h).const_add x).congr_deriv (one_smul ℝ h)
    have h1 := (hg (x + t • h)).hasFDerivAt.comp_hasDerivAt t hl
    rw [InnerProductSpace.toDual_apply_apply] at h1
    have h2 := (hasDerivAt_id t).mul_const (inner ℝ (gradf x) h)
    have h3 := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖h‖ ^ 2)
    exact ((h1.sub h2).sub h3).congr_deriv (by simp only [Nat.cast_ofNat, one_mul]; ring)
  have hanti : AntitoneOn φ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd t).deriv]
      have e1 : inner ℝ (gradf (x + t • h)) h - inner ℝ (gradf x) h
          = inner ℝ (gradf (x + t • h) - gradf x) h := by rw [inner_sub_left]
      have e2 := real_inner_le_norm (gradf (x + t • h) - gradf x) h
      have e3 := hlip (x + t • h) x
      have e4 : ‖x + t • h - x‖ = t * ‖h‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le]
      rw [e4] at e3
      have e5 := mul_le_mul_of_nonneg_right e3 (norm_nonneg h)
      nlinarith
  have := hanti (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
  simp only [φ, zero_smul, add_zero, zero_mul, sub_zero, one_smul, one_mul, one_pow, mul_one] at this
  have hy : x + h = y := by simp [h]
  rw [hy] at this
  have : (0:ℝ) ^ 2 = 0 := by norm_num
  simp_all
  linarith

lemma sqrt_step (s s' a sL sg : ℝ) (hs : 0 < s) (hss : s ≤ s') (hsL : 0 < sL) (hsg : 0 ≤ sg)
    (h : (s' - s) * (s' + s) = a * s ^ 2) (hk : sL * a * s ^ 2 ≥ sg * s') :
    2 * sL * (s' - s) ≥ sg := by
  by_contra hc
  push Not at hc
  have hs' : 0 < s' := lt_of_lt_of_le hs hss
  have h1 : 2 * sL * (s' - s) * s' < sg * s' := mul_lt_mul_of_pos_right hc hs'
  have h2 : sL * ((s' - s) * (s' + s)) ≤ sL * ((s' - s) * (2 * s')) := by
    apply mul_le_mul_of_nonneg_left _ hsL.le
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    linarith
  nlinarith

lemma rates (μ L : ℝ) (hL : 0 < L) (hμ : 0 ≤ μ) (α γ : ℕ → ℝ) (hγ0 : 0 < γ 0)
    (hα : ∀ k, 0 < α k) (hge : ∀ k, (γ (k + 1) - γ k) / α k = μ - γ (k + 1))
    (hstep : ∀ k, L * α k ^ 2 = γ k * (1 + α k)) (Λ : ℕ → ℝ)
    (h86 : ∀ k, Λ (k + 1) ≤ Λ k / (1 + α k)) (h0 : 0 ≤ Λ 0) :
    (∀ k : ℕ, Λ k ≤ Λ 0 * min (4 * L / (Real.sqrt (γ 0) * k + 2 * Real.sqrt L) ^ 2)
        ((1 + Real.sqrt (min (γ 0) μ / L)) ^ (-(k : ℤ)))) ∧
    (∀ k : ℕ, 1 ≤ k → Λ k ≤ (L / γ 0 * Λ 0) *
        min (4 / (k : ℝ) ^ 2) ((1 + Real.sqrt (min (γ 0) μ / L)) ^ (1 - (k : ℤ)))) := by
  -- the parameter recursion in product form
  have hrec : ∀ k, γ (k + 1) * (1 + α k) = γ k + α k * μ := by
    intro k; have := hge k; rw [div_eq_iff (hα k).ne'] at this; linarith
  set m := min (γ 0) μ with hm
  set r : ℕ → ℝ := fun k => ∏ i ∈ Finset.range k, (1 + α i) with hr
  have hr0 : r 0 = 1 := by simp [r]
  have hrs : ∀ k, r (k + 1) = r k * (1 + α k) := fun k => Finset.prod_range_succ _ k
  have hrpos : ∀ k, 0 < r k := fun k =>
    Finset.prod_pos (fun i _ => by linarith [hα i])
  -- Λ k ≤ Λ 0 / r k
  have hΛ : ∀ k, Λ k ≤ Λ 0 / r k := by
    intro k
    induction k with
    | zero => simp [hr0]
    | succ k ih =>
      calc Λ (k + 1) ≤ Λ k / (1 + α k) := h86 k
        _ ≤ (Λ 0 / r k) / (1 + α k) :=
            div_le_div_of_nonneg_right ih (by linarith [hα k])
        _ = Λ 0 / r (k + 1) := by rw [hrs, div_div]
  -- γ k ≥ m, γ k > 0, γ k ≥ γ0 / r k
  have hγm : ∀ k, m ≤ γ k := by
    intro k
    induction k with
    | zero => exact min_le_left _ _
    | succ k ih =>
      have h1 := hrec k
      have hmμ : m ≤ μ := min_le_right _ _
      have hak := hα k
      by_contra hc; push Not at hc
      nlinarith
  have hmpos : 0 ≤ m := le_min hγ0.le hμ
  have hγr : ∀ k, γ 0 / r k ≤ γ k := by
    intro k
    induction k with
    | zero => simp [hr0]
    | succ k ih =>
      have h1 := hrec k
      have hak := hα k
      rw [hrs, ← div_div, div_le_iff₀ (by linarith)]
      nlinarith
  -- α k ≥ ŝ
  set sh := Real.sqrt (m / L) with hsh
  have hαs : ∀ k, sh ≤ α k := by
    intro k
    have h1 := hstep k
    have hγk := hγm k
    have hak := hα k
    have : m / L ≤ α k ^ 2 := by
      rw [div_le_iff₀ hL]; nlinarith
    calc sh ≤ Real.sqrt (α k ^ 2) := Real.sqrt_le_sqrt this
      _ = α k := Real.sqrt_sq hak.le
  have hsh0 : 0 ≤ sh := Real.sqrt_nonneg _
  have hgeo : ∀ k, (1 + sh) ^ k ≤ r k := by
    intro k
    induction k with
    | zero => simp [hr0]
    | succ k ih =>
      rw [pow_succ, hrs]
      exact mul_le_mul ih (by linarith [hαs k]) (by linarith) (hrpos k).le
  have hgeo1 : ∀ k, (1 + α 0) * (1 + sh) ^ k ≤ r (k + 1) := by
    intro k
    induction k with
    | zero => simp [hrs, hr0]
    | succ k ih =>
      rw [pow_succ, hrs (k + 1), ← mul_assoc]
      exact mul_le_mul ih (by linarith [hαs (k + 1)]) (by linarith) (hrpos _).le
  -- the square-root growth
  set sL := Real.sqrt L
  set sg := Real.sqrt (γ 0)
  have hsL : 0 < sL := Real.sqrt_pos.mpr hL
  have hsg : 0 < sg := Real.sqrt_pos.mpr hγ0
  have hsLsq : sL ^ 2 = L := Real.sq_sqrt hL.le
  have hsgsq : sg ^ 2 = γ 0 := Real.sq_sqrt hγ0.le
  have hsqrt : ∀ k, sg * k + 2 * sL ≤ 2 * sL * Real.sqrt (r k) := by
    intro k
    induction k with
    | zero => simp [hr0]
    | succ k ih =>
      set s := Real.sqrt (r k)
      set s' := Real.sqrt (r (k + 1))
      have hsq : s ^ 2 = r k := Real.sq_sqrt (hrpos k).le
      have hsq' : s' ^ 2 = r (k + 1) := Real.sq_sqrt (hrpos _).le
      have hs : 0 < s := Real.sqrt_pos.mpr (hrpos k)
      have hak := hα k
      have hss : s ≤ s' := Real.sqrt_le_sqrt (by rw [hrs]; nlinarith [hrpos k])
      have hdiff : (s' - s) * (s' + s) = α k * s ^ 2 := by
        have : (s' - s) * (s' + s) = s' ^ 2 - s ^ 2 := by ring
        rw [this, hsq, hsq', hrs]; ring
      have hk : sL * α k * s ^ 2 ≥ sg * s' := by
        have hs' : 0 ≤ s' := Real.sqrt_nonneg _
        apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
        rw [mul_pow, mul_pow, mul_pow, hsLsq, hsgsq, hsq', hsq, hrs]
        have h1 := hstep k
        have h2 := hγr k
        rw [div_le_iff₀ (hrpos k)] at h2
        have h3 : γ 0 * (1 + α k) ≤ γ k * r k * (1 + α k) :=
          mul_le_mul_of_nonneg_right h2 (by linarith)
        have h4 : L * α k ^ 2 * r k = γ k * (1 + α k) * r k := by rw [h1]
        nlinarith [hrpos k]
      have := sqrt_step s s' (α k) sL sg hs hss hsL hsg.le hdiff hk
      push_cast
      linarith
  have hlam1 : ∀ k : ℕ, 1 / r k ≤ 4 * L / (sg * k + 2 * sL) ^ 2 := by
    intro k
    have h1 := hsqrt k
    have hpos : 0 < sg * k + 2 * sL := by positivity
    have hsq : Real.sqrt (r k) ^ 2 = r k := Real.sq_sqrt (hrpos k).le
    rw [div_le_div_iff₀ (hrpos k) (by positivity)]
    have h2 : (sg * k + 2 * sL) ^ 2 ≤ (2 * sL * Real.sqrt (r k)) ^ 2 :=
      pow_le_pow_left₀ hpos.le h1 2
    rw [mul_pow, mul_pow, hsq, hsLsq] at h2
    linarith
  constructor
  · intro k
    calc Λ k ≤ Λ 0 / r k := hΛ k
      _ = Λ 0 * (1 / r k) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ h0
        apply le_min (hlam1 k)
        rw [zpow_neg, zpow_natCast, inv_eq_one_div]
        exact one_div_le_one_div_of_le (by positivity) (hgeo k)
  · intro k hk
    have hC : 0 ≤ L / γ 0 * Λ 0 := by positivity
    rw [mul_min_of_nonneg _ _ hC]
    apply le_min
    · calc Λ k ≤ Λ 0 * (1 / r k) := by rw [mul_one_div]; exact hΛ k
        _ ≤ Λ 0 * (4 * L / (sg * k + 2 * sL) ^ 2) := mul_le_mul_of_nonneg_left (hlam1 k) h0
        _ ≤ L / γ 0 * Λ 0 * (4 / (k : ℝ) ^ 2) := by
          have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
          have : 4 * L / (sg * k + 2 * sL) ^ 2 ≤ L / γ 0 * (4 / (k : ℝ) ^ 2) := by
            rw [div_le_iff₀ (by positivity)]
            have : L / γ 0 * (4 / (k : ℝ) ^ 2) * (sg * k + 2 * sL) ^ 2
                = 4 * L * ((sg * k + 2 * sL) ^ 2 / (sg ^ 2 * k ^ 2)) := by
              rw [hsgsq]; field_simp
            rw [this]
            have : 1 ≤ (sg * k + 2 * sL) ^ 2 / (sg ^ 2 * k ^ 2) := by
              rw [one_le_div (by positivity)]
              nlinarith [mul_nonneg (mul_nonneg hsg.le hkpos.le) hsL.le]
            nlinarith
          nlinarith
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hz : (1 + sh) ^ (1 - ((j + 1 : ℕ) : ℤ)) = 1 / (1 + sh) ^ j := by
        rw [show (1 : ℤ) - ((j + 1 : ℕ) : ℤ) = -(j : ℤ) by push_cast; ring, zpow_neg,
          zpow_natCast, inv_eq_one_div]
      rw [hz]
      have hγL : γ 0 ≤ L * (1 + α 0) := by
        have h1 := hstep 0
        have h2 := hα 0
        nlinarith
      calc Λ (j + 1) ≤ Λ 0 / r (j + 1) := hΛ _
        _ ≤ Λ 0 / ((1 + α 0) * (1 + sh) ^ j) :=
            div_le_div_of_nonneg_left h0 (by have := hα 0; positivity) (hgeo1 j)
        _ ≤ L / γ 0 * Λ 0 * (1 / (1 + sh) ^ j) := by
            rw [div_mul_eq_div_div, mul_one_div]
            have hp : 0 < (1 + sh) ^ j := by positivity
            apply div_le_div_of_nonneg_right _ hp.le
            rw [div_le_iff₀ (by linarith [hα 0])]
            have : L / γ 0 * Λ 0 * (1 + α 0) = Λ 0 * (L * (1 + α 0) / γ 0) := by ring
            rw [this]
            have : 1 ≤ L * (1 + α 0) / γ 0 := by rw [one_le_div hγ0]; exact hγL
            nlinarith


lemma gamma_pos (μ : ℝ) (hμ : 0 ≤ μ) (α γ : ℕ → ℝ) (hγ0 : 0 < γ 0) (hα : ∀ k, 0 < α k)
    (hge : ∀ k, (γ (k + 1) - γ k) / α k = μ - γ (k + 1)) : ∀ k, 0 < γ k := by
  intro k
  induction k with
  | zero => exact hγ0
  | succ k ih =>
    have hak := hα k
    have h := hge k
    rw [div_eq_iff hak.ne'] at h
    nlinarith

-- scalar core of the predictor-corrector Lyapunov step
lemma key (a b g g' μ L Fx Fx' Fy fs iGd iGp iGq pq nq np nd qd : ℝ)
    (hg : 0 < g) (ha : 0 < a) (hμ : 0 ≤ μ) (hg' : (1 + a) * g' = g + a * μ)
    (hb : b * (1 + a) = a) (hst : L * a ^ 2 = g * (1 + a))
    (Desc : Fx' ≤ Fy + b * iGd + L / 2 * (b ^ 2 * nd))
    (C1 : Fx ≥ Fy + a * (iGd + iGp))
    (C2 : fs - Fy + (iGp + iGq) ≥ μ / 2 * (np + 2 * pq + nq))
    (hd : g * qd = a * μ * pq - a * iGq)
    (hnp : 0 ≤ np) (hnd : 0 ≤ nd) :
    Fx' - fs + g' / 2 * nq ≤ (Fx - fs + g / 2 * (nq - 2 * qd + nd)) / (1 + a) := by
  have h1a : 0 < 1 + a := by linarith
  rw [le_div_iff₀ h1a]
  have hLb : L * b ^ 2 * (1 + a) = g := by
    have : (L * b ^ 2 * (1 + a) - g) * (1 + a) = 0 := by
      have : L * b ^ 2 * (1 + a) * (1 + a) = L * a ^ 2 := by
        linear_combination L * (b * (1 + a) + a) * hb
      linear_combination this + hst
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have e1 := mul_le_mul_of_nonneg_left Desc h1a.le
  have e2 := mul_le_mul_of_nonneg_left C2 ha.le
  have e3 := mul_nonneg (mul_nonneg ha.le hμ) hnp
  have e4 : (1 + a) * g' * nq = (g + a * μ) * nq := by rw [hg']
  have e5 : L * b ^ 2 * (1 + a) * nd = g * nd := by rw [hLb]
  have e6 : (1 + a) * (b * iGd) = a * iGd := by linear_combination iGd * hb
  nlinarith

end RRAux_NAGFlow_PredCorr_theorem_5_1

open NAGFlow.PredCorr in
theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ L : ℝ) (hf : IsS11 f gradf μ L)
    (xstar : V) (hxstar : ∀ y, f xstar ≤ f y)
    (α γ : ℕ → ℝ) (hγ : IsGammaRun μ α γ)
    (hstep : ∀ k, L * α k ^ 2 = γ k * (1 + α k))
    (x y v : ℕ → V) (hrun : IsPCRun gradf μ α γ x y v) :
    (∀ k : ℕ, lyap f xstar x v γ (k + 1) ≤ lyap f xstar x v γ k / (1 + α k)) ∧
      (∀ k : ℕ, lyap f xstar x v γ k ≤
        lyap f xstar x v γ 0 *
          min (4 * L / (Real.sqrt (γ 0) * k + 2 * Real.sqrt L) ^ 2)
            ((1 + Real.sqrt (min (γ 0) μ / L)) ^ (-(k : ℤ)))) ∧
      (∀ k : ℕ, 1 ≤ k → lyap f xstar x v γ k ≤
        (L / γ 0 * (f (x 0) - f xstar) + L / 2 * ‖v 0 - xstar‖ ^ 2) *
          min (4 / (k : ℝ) ^ 2) ((1 + Real.sqrt (min (γ 0) μ / L)) ^ (1 - (k : ℤ)))) := by
  have hμ := hf.mu_nonneg
  have hL := hf.L_pos
  have hγp := RRAux_NAGFlow_PredCorr_theorem_5_1.gamma_pos μ hμ α γ hγ.gamma0_pos hγ.alpha_pos
    hγ.gamma_eq
  have h86 : ∀ k : ℕ, lyap f xstar x v γ (k + 1) ≤ lyap f xstar x v γ k / (1 + α k) := by
    intro k
    have ha := hγ.alpha_pos k
    have hg := hγp k
    have hge := hγ.gamma_eq k
    have hst := hstep k
    have hye := hrun.y_eq k
    have hve := hrun.v_eq k
    have hxe := hrun.x_eq k
    set a := α k
    set g := γ k
    set g' := γ (k + 1)
    set x' := x (k + 1)
    set v' := v (k + 1)
    set x0 := x k
    set v0 := v k
    set y0 := y k
    set G := gradf y0
    have hg' : (1 + a) * g' = g + a * μ := by
      rw [div_eq_iff ha.ne'] at hge; linarith
    have hy : y0 - x0 = a • (v0 - y0) := by
      have := congrArg (fun w => a • w) hye
      simpa only [smul_smul, mul_one_div_cancel ha.ne', one_smul] using this
    have hx : x' - x0 = a • (v' - x') := by
      have := congrArg (fun w => a • w) hxe
      simpa only [smul_smul, mul_one_div_cancel ha.ne', one_smul] using this
    have hv : g • (v' - v0) = (a * μ) • (y0 - v') - a • G := by
      have := congrArg (fun w => (a * g) • w) hve
      simp only [smul_sub, smul_smul] at this
      have e1 : a * g * (1 / a) = g := by field_simp
      have e2 : a * g * (μ / g) = a * μ := by field_simp
      have e3 : a * g * (1 / g) = a := by field_simp
      rw [e1, e2, e3] at this
      simp only [smul_sub]; exact this
    set b := a / (1 + a) with hbdef
    have hb : b * (1 + a) = a := by rw [hbdef]; field_simp
    set p := y0 - v'
    set q := v' - xstar
    set d := v' - v0
    have hxy : x' - y0 = b • d := by
      have h1 : (1 + a) • (x' - y0) = a • d := by
        simp only [d]; linear_combination (norm := module) hx - hy
      have h2 : x' - y0 = (1 + a)⁻¹ • ((1 + a) • (x' - y0)) := by
        rw [smul_smul, inv_mul_cancel₀ (by linarith), one_smul]
      rw [h2, h1, smul_smul, hbdef, div_eq_inv_mul]
    have hxy2 : x0 - y0 = a • (d + p) := by
      simp only [d, p]; linear_combination (norm := module) -hy
    have hvq : v0 - xstar = q - d := by simp only [q, d]; abel
    have hsq : xstar - y0 = -(p + q) := by simp only [p, q]; abel
    have Desc := RRAux_NAGFlow_PredCorr_theorem_5_1.descent f gradf L hL.le hf.hasGrad
      hf.grad_lip y0 x'
    rw [hxy, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at Desc
    have C1 := hf.mu_convex x0 y0
    rw [hxy2, real_inner_smul_right, inner_add_right] at C1
    have C2 := hf.mu_convex xstar y0
    rw [hsq, inner_neg_right, inner_add_right, norm_neg, norm_add_sq_real] at C2
    have hd : g * inner ℝ q d = a * μ * inner ℝ p q - a * inner ℝ G q := by
      have := congrArg (fun w => inner ℝ w q) hv
      simp only [inner_sub_left, real_inner_smul_left] at this
      rw [← real_inner_comm q d]; exact this
    have C1' : f x0 ≥ f y0 + a * (inner ℝ G d + inner ℝ G p) := by
      have := mul_nonneg (div_nonneg hμ (by norm_num : (0:ℝ) ≤ 2))
        (sq_nonneg ‖a • (d + p)‖)
      linarith
    show f x' - f xstar + g' / 2 * ‖q‖ ^ 2
      ≤ (f x0 - f xstar + g / 2 * ‖v0 - xstar‖ ^ 2) / (1 + a)
    rw [hvq, norm_sub_sq_real q d]
    exact RRAux_NAGFlow_PredCorr_theorem_5_1.key a b g g' μ L (f x0) (f x') (f y0) (f xstar)
      (inner ℝ G d) (inner ℝ G p) (inner ℝ G q) (inner ℝ p q) (‖q‖ ^ 2) (‖p‖ ^ 2) (‖d‖ ^ 2)
      (inner ℝ q d) hg ha hμ hg' hb hst Desc C1' (by linarith) hd (sq_nonneg _) (sq_nonneg _)
  have h0 : 0 ≤ lyap f xstar x v γ 0 := by
    show 0 ≤ f (x 0) - f xstar + γ 0 / 2 * ‖v 0 - xstar‖ ^ 2
    have := hxstar (x 0)
    have := hγ.gamma0_pos
    positivity
  obtain ⟨r87, r88⟩ := RRAux_NAGFlow_PredCorr_theorem_5_1.rates μ L hL hμ α γ hγ.gamma0_pos
    hγ.alpha_pos hγ.gamma_eq hstep (lyap f xstar x v γ) h86 h0
  refine ⟨h86, r87, fun k hk => ?_⟩
  have hC : L / γ 0 * (f (x 0) - f xstar) + L / 2 * ‖v 0 - xstar‖ ^ 2
      = L / γ 0 * lyap f xstar x v γ 0 := by
    show _ = L / γ 0 * (f (x 0) - f xstar + γ 0 / 2 * ‖v 0 - xstar‖ ^ 2)
    have := hγ.gamma0_pos.ne'
    field_simp
  rw [hC]
  exact r88 k hk

#print axioms solution
