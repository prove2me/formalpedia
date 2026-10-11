-- Prove2me | solution 1 for NAGFlow.APGM.theorem_7_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T21:54:39.040748+00:00
-- url     : https://prove2.me/submissions/310189a8-f31a-4d79-8482-797541e7b5d7

import Mathlib
import Definitions.Def_NAGFlow_APGM_Setting

namespace RRAux_NAGFlow_APGM_theorem_7_2

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


lemma small_le (c K : ℝ) (hK : 0 ≤ K) (h : ∀ t : ℝ, 0 < t → t ≤ 1 → c ≤ K * t) : c ≤ 0 := by
  by_contra hc
  push Not at hc
  rcases hK.lt_or_eq with hKp | hK0
  · have ht : 0 < min 1 (c / (2 * K)) := lt_min one_pos (by positivity)
    have h1 := h _ ht (min_le_left _ _)
    have h2 : K * min 1 (c / (2 * K)) ≤ K * (c / (2 * K)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hK
    have h3 : K * (c / (2 * K)) = c / 2 := by field_simp
    linarith
  · have := h 1 one_pos le_rfl
    rw [← hK0] at this; linarith

lemma prox_ineq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (g : V → ℝ) (D : Set V) (hconv : ConvexOn ℝ D g) (L : ℝ) (hL : 0 < L) (z x' : V)
    (hp : NAGFlow.APGM.IsProx g D (1 / L) z x') (u : V) (hu : u ∈ D) :
    g x' - g u ≤ L * inner ℝ (u - x') (x' - z) := by
  obtain ⟨hx'D, hmin⟩ := hp
  have hcoef : 1 / (2 * (1 / L)) = L / 2 := by field_simp
  rw [hcoef] at hmin
  apply sub_nonpos.mp
  apply small_le _ (L / 2 * ‖u - x'‖ ^ 2) (by positivity)
  intro t ht ht1
  have hmem : (1 - t) • x' + t • u ∈ D := hconv.1 hx'D hu (by linarith) ht.le (by ring)
  have hg := hconv.2 hx'D hu (by linarith : (0:ℝ) ≤ 1 - t) ht.le (by ring)
  simp only [smul_eq_mul] at hg
  have hm := hmin _ hmem
  have e : (1 - t) • x' + t • u - z = (x' - z) + t • (u - x') := by module
  rw [e, norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_right, real_inner_comm] at hm
  have : t * (g x' - g u - L * inner ℝ (u - x') (x' - z)) ≤ t * (L / 2 * ‖u - x'‖ ^ 2 * t) := by
    nlinarith
  have := le_of_mul_le_mul_left this ht
  linarith

-- the composite-gradient inequality at a prox-gradient point
lemma apgm_point {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : V → ℝ) (gradh : V → V) (μ L : ℝ) (hh : NAGFlow.PredCorr.IsS11 h gradh μ L)
    (g : V → ℝ) (D : Set V) (hconv : ConvexOn ℝ D g)
    (descent : ∀ a b, h b ≤ h a + inner ℝ (gradh a) (b - a) + L / 2 * ‖b - a‖ ^ 2)
    (y x' : V) (hx : NAGFlow.APGM.IsSf gradh g D (1 / L) y x') (u : V) (hu : u ∈ D) :
    h x' + g x' ≤ h u + g u + inner ℝ (L • (y - x')) (y - u) - ‖L • (y - x')‖ ^ 2 / (2 * L)
      - μ / 2 * ‖u - y‖ ^ 2 := by
  have hL := hh.L_pos
  have hP := prox_ineq g D hconv L hL _ x' hx u hu
  have hD := descent y x'
  have hC := hh.mu_convex u y
  set e := x' - y with he
  set r := u - y with hr
  set N := gradh y
  have e1 : u - x' = r - e := by simp only [r, e]; abel
  have e2 : x' - (y - (1 / L) • N) = e + (1 / L) • N := by simp only [e]; abel
  rw [e1, e2] at hP
  simp only [inner_sub_left, inner_add_right, real_inner_smul_right] at hP
  have e3 : y - x' = -e := by simp only [e]; abel
  have e4 : y - u = -r := by simp only [r]; abel
  rw [e3, e4, smul_neg, norm_neg, inner_neg_left, inner_neg_right, real_inner_smul_left,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← real_inner_self_eq_norm_sq e]
  have hrr := real_inner_comm r N
  have hee := real_inner_comm e N
  have hre := real_inner_comm r e
  have hLL : L * (1 / L) = 1 := by field_simp
  have hLL2 : L ^ 2 * inner ℝ e e / (2 * L) = L / 2 * inner ℝ e e := by field_simp
  rw [← real_inner_self_eq_norm_sq e] at hD
  rw [hLL2]
  have hP' : g x' - g u ≤ L * inner ℝ r e - L * inner ℝ e e + inner ℝ r N - inner ℝ e N := by
    calc _ ≤ _ := hP
      _ = _ := by field_simp; ring
  rw [hre]
  linarith


-- scalar core of the APGM Lyapunov step (116)
lemma key (a c c' μ L Fx Fx' fs iGd iGp iGq pq nq np nd qd nG : ℝ)
    (hc : 0 < c) (ha : 0 < a) (hμ : 0 ≤ μ) (hL : 0 < L) (hc' : (1 + a) * c' = c + a * μ)
    (hst : L * a ^ 2 = c * (1 + a))
    (P1 : Fx' ≤ Fx - a * (iGd + iGp) - nG / (2 * L))
    (P2 : Fx' ≤ fs + (iGp + iGq) - nG / (2 * L) - μ / 2 * (np + 2 * pq + nq))
    (hd : c * qd = a * μ * pq - a * iGq)
    (Y : 0 ≤ c ^ 2 * nd + 2 * (c * (a * iGd)) + a ^ 2 * nG)
    (hnp : 0 ≤ np) :
    Fx' - fs + c' / 2 * nq ≤ (Fx - fs + c / 2 * (nq - 2 * qd + nd)) / (1 + a) := by
  have h1a : 0 < 1 + a := by linarith
  rw [le_div_iff₀ h1a]
  have hY : 0 ≤ c * nd + 2 * a * iGd + (1 + a) * (nG / L) := by
    have e : (1 + a) * (nG / L) = a ^ 2 / c * nG := by
      field_simp; linear_combination (-nG) * hst
    rw [e]
    have : c * nd + 2 * a * iGd + a ^ 2 / c * nG
        = (c ^ 2 * nd + 2 * (c * (a * iGd)) + a ^ 2 * nG) / c := by
      field_simp
    rw [this]; exact div_nonneg Y hc.le
  have e2 := mul_le_mul_of_nonneg_left P2 ha.le
  have e3 := mul_nonneg (mul_nonneg ha.le hμ) hnp
  have e4 : (1 + a) * c' * nq = (c + a * μ) * nq := by rw [hc']
  have e5 : nG / (2 * L) = (nG / L) / 2 := by ring
  nlinarith

end RRAux_NAGFlow_APGM_theorem_7_2

open NAGFlow.APGM in
theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : V → ℝ) (gradh : V → V) (μ L : ℝ) (hh : NAGFlow.PredCorr.IsS11 h gradh μ L)
    (g : V → ℝ) (D : Set V) (hg : IsProperClosedConvex g D)
    (xstar : V) (hxstar : xstar ∈ D) (hmin : ∀ z ∈ D, (h + g) xstar ≤ (h + g) z)
    (α γ : ℕ → ℝ) (x y w v : ℕ → V) (hrun : IsAPGMRun gradh g D μ L α γ x y w v)
    (hx0 : x 0 ∈ D) :
    (∀ k : ℕ, NAGFlow.PredCorr.lyap (h + g) xstar x v γ (k + 1) ≤ NAGFlow.PredCorr.lyap (h + g) xstar x v γ k / (1 + α k)) ∧
      (∀ k : ℕ, NAGFlow.PredCorr.lyap (h + g) xstar x v γ k ≤
        NAGFlow.PredCorr.lyap (h + g) xstar x v γ 0 *
          min (4 * L / (Real.sqrt (γ 0) * k + 2 * Real.sqrt L) ^ 2)
            ((1 + Real.sqrt (min (γ 0) μ / L)) ^ (-(k : ℤ)))) ∧
      (∀ k : ℕ, 1 ≤ k → NAGFlow.PredCorr.lyap (h + g) xstar x v γ k ≤
        (L / γ 0 * ((h + g) (x 0) - (h + g) xstar) + L / 2 * ‖v 0 - xstar‖ ^ 2) *
          min (4 / (k : ℝ) ^ 2) ((1 + Real.sqrt (min (γ 0) μ / L)) ^ (1 - (k : ℤ)))) := by
  have hμ := hh.mu_nonneg
  have hL := hh.L_pos
  have hge : ∀ k, (γ (k + 1) - γ k) / α k = μ - γ (k + 1) := by
    intro k
    have ha := hrun.alpha_pos k
    rw [div_eq_iff ha.ne', hrun.gamma_eq k]
    field_simp
    ring
  have hγp : ∀ k, 0 < γ k := by
    intro k
    induction k with
    | zero => exact hrun.gamma0_pos
    | succ k ih =>
      rw [hrun.gamma_eq k]
      have := hrun.alpha_pos k
      have := mul_nonneg hμ this.le
      positivity
  have hxD : ∀ k, x k ∈ D := by
    intro k
    cases k with
    | zero => exact hx0
    | succ k => exact (hrun.x_eq k).1
  have hdesc := RRAux_NAGFlow_APGM_theorem_7_2.descent h gradh L hL.le hh.hasGrad hh.grad_lip
  have h86 : ∀ k : ℕ, NAGFlow.PredCorr.lyap (h + g) xstar x v γ (k + 1)
      ≤ NAGFlow.PredCorr.lyap (h + g) xstar x v γ k / (1 + α k) := by
    intro k
    have ha := hrun.alpha_pos k
    have hc := hγp k
    have hc'p := hγp (k + 1)
    have hgam := hrun.gamma_eq k
    have hst := hrun.step_rel k
    have hye := hrun.y_eq k
    have hwe := hrun.w_eq k
    have hve := hrun.v_eq k
    have hxk := hrun.x_eq k
    have hx0D := hxD k
    set a := α k
    set c := γ k
    set c' := γ (k + 1)
    set x' := x (k + 1)
    set v' := v (k + 1)
    set x0 := x k
    set v0 := v k
    set y0 := y k
    set w0 := w k
    have hc' : (1 + a) * c' = c + a * μ := by
      rw [hgam]; field_simp
    have hcμ : 0 < c + μ * a := by have := mul_nonneg hμ ha.le; linarith
    have hy1 : (1 + a) • y0 = x0 + a • v0 := by
      rw [hye, smul_smul, mul_one_div_cancel (by linarith), one_smul]
    have hw1 : (c + μ * a) • w0 = c • v0 + (μ * a) • y0 := by
      rw [hwe, smul_smul, mul_one_div_cancel hcμ.ne', one_smul]
    have hsc : (c + μ * a) * (c / c') * (1 / a) = L * a := by
      have e : c + μ * a = c' * (1 + a) := by linarith
      rw [e]
      field_simp
      linear_combination -hst
    have hv1 : (c + μ * a) • v' = c • v0 + (μ * a) • y0 + (L * a) • (x' - y0) := by
      rw [hve, smul_add, hw1, smul_smul, smul_smul, hsc]
    have hv : c • (v' - v0) = (a * μ) • (y0 - v') - a • (L • (y0 - x')) := by
      linear_combination (norm := module) hv1
    have P1 := RRAux_NAGFlow_APGM_theorem_7_2.apgm_point h gradh μ L hh g D hg.convex hdesc
      y0 x' hxk x0 hx0D
    have P2 := RRAux_NAGFlow_APGM_theorem_7_2.apgm_point h gradh μ L hh g D hg.convex hdesc
      y0 x' hxk xstar hxstar
    set G := L • (y0 - x')
    set p := y0 - v'
    set q := v' - xstar
    set d := v' - v0
    have hyx : y0 - x0 = (-a) • (d + p) := by
      simp only [d, p]; linear_combination (norm := module) hy1
    have hyq : y0 - xstar = p + q := by simp only [p, q]; abel
    have hvq : v0 - xstar = q - d := by simp only [q, d]; abel
    rw [hyx, real_inner_smul_right, inner_add_right] at P1
    rw [hyq, inner_add_right, norm_sub_rev, hyq, norm_add_sq_real] at P2
    have hd : c * inner ℝ q d = a * μ * inner ℝ p q - a * inner ℝ G q := by
      have := congrArg (fun z => inner ℝ z q) hv
      simp only [inner_sub_left, real_inner_smul_left] at this
      rw [← real_inner_comm q d]; exact this
    have Y : 0 ≤ c ^ 2 * ‖d‖ ^ 2 + 2 * (c * (a * inner ℝ G d)) + a ^ 2 * ‖G‖ ^ 2 := by
      have := sq_nonneg ‖c • d + a • G‖
      rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
        mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
        real_inner_comm] at this
      linarith
    have P1' : h x' + g x' ≤ h x0 + g x0 - a * (inner ℝ G d + inner ℝ G p) - ‖G‖ ^ 2 / (2 * L) := by
      have := mul_nonneg (div_nonneg hμ (by norm_num : (0:ℝ) ≤ 2)) (sq_nonneg ‖x0 - y0‖)
      linarith
    show h x' + g x' - (h xstar + g xstar) + c' / 2 * ‖q‖ ^ 2
      ≤ (h x0 + g x0 - (h xstar + g xstar) + c / 2 * ‖v0 - xstar‖ ^ 2) / (1 + a)
    rw [hvq, norm_sub_sq_real q d]
    exact RRAux_NAGFlow_APGM_theorem_7_2.key a c c' μ L (h x0 + g x0) (h x' + g x')
      (h xstar + g xstar) (inner ℝ G d) (inner ℝ G p) (inner ℝ G q) (inner ℝ p q) (‖q‖ ^ 2)
      (‖p‖ ^ 2) (‖d‖ ^ 2) (inner ℝ q d) (‖G‖ ^ 2) hc ha hμ hL hc' hst P1' (by linarith) hd Y
      (sq_nonneg _)
  have h0 : 0 ≤ NAGFlow.PredCorr.lyap (h + g) xstar x v γ 0 := by
    show 0 ≤ (h + g) (x 0) - (h + g) xstar + γ 0 / 2 * ‖v 0 - xstar‖ ^ 2
    have := hmin (x 0) hx0
    have := hrun.gamma0_pos
    have : 0 ≤ (h + g) (x 0) - (h + g) xstar := by linarith
    positivity
  obtain ⟨r87, r88⟩ := RRAux_NAGFlow_APGM_theorem_7_2.rates μ L hL hμ α γ hrun.gamma0_pos
    hrun.alpha_pos hge hrun.step_rel (NAGFlow.PredCorr.lyap (h + g) xstar x v γ) h86 h0
  refine ⟨h86, r87, fun k hk => ?_⟩
  have hC : L / γ 0 * ((h + g) (x 0) - (h + g) xstar) + L / 2 * ‖v 0 - xstar‖ ^ 2
      = L / γ 0 * NAGFlow.PredCorr.lyap (h + g) xstar x v γ 0 := by
    show _ = L / γ 0 * ((h + g) (x 0) - (h + g) xstar + γ 0 / 2 * ‖v 0 - xstar‖ ^ 2)
    have := hrun.gamma0_pos.ne'
    field_simp
  rw [hC]
  exact r88 k hk

#print axioms solution
