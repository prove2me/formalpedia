-- Prove2me | solution 1 for NAGFlow.AFB.theorem_7_3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T22:00:12.138192+00:00
-- url     : https://prove2.me/submissions/79402728-60d2-4984-9a68-e17330e23a2b

import Mathlib
import Definitions.Def_NAGFlow_AFB_Setting

namespace RRAux_NAGFlow_AFB_theorem_7_3

lemma descentOn {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (L : ℝ) (hL : 0 ≤ L) (Q : Set V) (hQ : Convex ℝ Q)
    (hg : ∀ x ∈ Q, HasGradientWithinAt f (gradf x) Q x)
    (hlip : ∀ x ∈ Q, ∀ y ∈ Q, ‖gradf x - gradf y‖ ≤ L * ‖x - y‖)
    (x y : V) (hx : x ∈ Q) (hy : y ∈ Q) :
    f y ≤ f x + inner ℝ (gradf x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  set h := y - x
  let φ : ℝ → ℝ := fun t => f (x + t • h) - t * inner ℝ (gradf x) h - L / 2 * t ^ 2 * ‖h‖ ^ 2
  have hmaps : Set.MapsTo (fun s : ℝ => x + s • h) (Set.Icc 0 1) Q := by
    intro s hs
    have := hQ hx hy (by linarith [hs.2] : (0:ℝ) ≤ 1 - s) hs.1 (by ring)
    convert this using 1
    simp only [h]; module
  have hd : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt φ (inner ℝ (gradf (x + t • h)) h
      - inner ℝ (gradf x) h - L * t * ‖h‖ ^ 2) (Set.Icc 0 1) t := by
    intro t ht
    have hl : HasDerivWithinAt (fun s : ℝ => x + s • h) h (Set.Icc 0 1) t :=
      ((((hasDerivAt_id t).smul_const h).const_add x).congr_deriv (one_smul ℝ h)).hasDerivWithinAt
    have h1 := (hg _ (hmaps ht)).hasFDerivWithinAt.comp_hasDerivWithinAt t hl hmaps
    rw [InnerProductSpace.toDual_apply_apply] at h1
    have h2 := ((hasDerivAt_id t).mul_const (inner ℝ (gradf x) h)).hasDerivWithinAt
      (s := Set.Icc 0 1)
    have h3 := (((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖h‖ ^ 2)).hasDerivWithinAt
      (s := Set.Icc 0 1)
    exact ((h1.sub h2).sub h3).congr_deriv (by simp only [Nat.cast_ofNat, one_mul]; ring)
  have hanti : AntitoneOn φ (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    · exact fun t ht => (hd t ht).continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hd t (Set.Ioo_subset_Icc_self ht)).mono (by rw [interior_Icc]; exact Set.Ioo_subset_Icc_self)
    · intro t ht
      rw [interior_Icc] at ht
      have e2 := real_inner_le_norm (gradf (x + t • h) - gradf x) h
      have e3 := hlip (x + t • h) (hmaps (Set.Ioo_subset_Icc_self ht)) x hx
      have e4 : ‖x + t • h - x‖ = t * ‖h‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le]
      rw [e4] at e3
      have e5 := mul_le_mul_of_nonneg_right e3 (norm_nonneg h)
      rw [inner_sub_left] at e2
      nlinarith
  have := hanti (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
  simp only [φ, zero_smul, add_zero, zero_mul, sub_zero, one_smul, one_mul, one_pow, mul_one] at this
  have hy' : x + h = y := by simp [h]
  rw [hy'] at this
  have : (0:ℝ) ^ 2 = 0 := by norm_num
  simp_all
  linarith

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

lemma argmin_strong {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (g : V → ℝ) (K : Set V) (hg : ConvexOn ℝ K g) (κ : ℝ) (hκ : 0 ≤ κ) (G w v' : V)
    (hv' : v' ∈ K)
    (hmin : ∀ u ∈ K, g v' + inner ℝ G v' + κ * ‖v' - w‖ ^ 2 ≤ g u + inner ℝ G u + κ * ‖u - w‖ ^ 2)
    (u : V) (hu : u ∈ K) :
    g v' + inner ℝ G v' + κ * ‖v' - w‖ ^ 2 + κ * ‖u - v'‖ ^ 2
      ≤ g u + inner ℝ G u + κ * ‖u - w‖ ^ 2 := by
  have hexp : ‖u - w‖ ^ 2 = ‖v' - w‖ ^ 2 + 2 * inner ℝ (v' - w) (u - v') + ‖u - v'‖ ^ 2 := by
    rw [show u - w = (v' - w) + (u - v') by abel, norm_add_sq_real]
  have hlin : inner ℝ G u = inner ℝ G v' + inner ℝ G (u - v') := by
    rw [inner_sub_right]; ring
  rw [hexp, hlin]
  have key : g v' + κ * ‖u - v'‖ ^ 2 - g u - inner ℝ G (u - v') - 2 * κ * inner ℝ (v' - w) (u - v')
      - κ * ‖u - v'‖ ^ 2 ≤ 0 := by
    apply small_le _ (κ * ‖u - v'‖ ^ 2) (by positivity)
    intro t ht ht1
    have hmem : (1 - t) • v' + t • u ∈ K := hg.1 hv' hu (by linarith) ht.le (by ring)
    have hgt := hg.2 hv' hu (by linarith : (0:ℝ) ≤ 1 - t) ht.le (by ring)
    simp only [smul_eq_mul] at hgt
    have hm := hmin _ hmem
    have e'' : (1 - t) • v' + t • u = v' + t • (u - v') := by module
    rw [e''] at hgt
    have e : (1 - t) • v' + t • u - w = (v' - w) + t • (u - v') := by module
    have e' : (1 - t) • v' + t • u = v' + t • (u - v') := by module
    rw [e, norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_smul_right, e', inner_add_right, real_inner_smul_right] at hm
    have : t * (g v' + κ * ‖u - v'‖ ^ 2 - g u - inner ℝ G (u - v')
        - 2 * κ * inner ℝ (v' - w) (u - v') - κ * ‖u - v'‖ ^ 2)
        ≤ t * (κ * ‖u - v'‖ ^ 2 * t) := by nlinarith
    exact le_of_mul_le_mul_left this ht
  linarith

lemma s45 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (c m : ℝ) (hm : 0 ≤ m) (v y w v' xs : V) (hw : (c + m) • w = c • v + m • y) :
    (c + m) * ‖w - xs‖ ^ 2 + c * ‖v' - v‖ ^ 2
      ≤ c * ‖v - xs‖ ^ 2 + m * ‖y - xs‖ ^ 2 + (c + m) * ‖v' - w‖ ^ 2 := by
  have e1 : v - xs = (v - w) + (w - xs) := by abel
  have e2 : y - xs = (y - w) + (w - xs) := by abel
  have e3 : v' - v = (v' - w) - (v - w) := by abel
  have hc : c • (v - w) + m • (y - w) = 0 := by linear_combination (norm := module) -hw
  have i1 := congrArg (fun z => inner ℝ z (w - xs)) hc
  have i2 := congrArg (fun z => inner ℝ (v' - w) z) hc
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_zero_left, inner_zero_right] at i1 i2
  have hsq := mul_nonneg hm (sq_nonneg ‖(v' - w) - (y - w)‖)
  rw [norm_sub_sq_real (v' - w) (y - w)] at hsq
  rw [e1, e2, e3, norm_add_sq_real (v - w) (w - xs), norm_add_sq_real (y - w) (w - xs),
    norm_sub_sq_real (v' - w) (v - w)]
  nlinarith

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


-- scalar core of the semi-AFB Lyapunov step (121)
lemma key (a b c c' μ L κ Hx Hx' Hy Hs Gx Gx' Gv' Gs iGd iGvy iGsy iGv's iGv' iGs
    nd nyq nv'w nv's nws nvs : ℝ)
    (hc : 0 < c) (ha : 0 < a) (hμ : 0 ≤ μ) (hc' : (1 + a) * c' = c + a * μ)
    (hb : b * (1 + a) = a) (hst : L * a ^ 2 = c * (1 + a)) (hκ : 2 * a * κ = c + μ * a)
    (D1 : Hx' ≤ Hy + b * iGd + L / 2 * (b ^ 2 * nd))
    (Gc : (1 + a) * Gx' ≤ Gx + a * Gv')
    (C1 : Hx ≥ Hy + -a * iGvy)
    (C2 : Hs ≥ Hy + iGsy + μ / 2 * nyq)
    (hrel : iGv's = iGd + iGvy - iGsy)
    (hlin : iGv' - iGs = iGv's)
    (S3 : Gv' + iGv' + κ * nv'w + κ * nv's ≤ Gs + iGs + κ * nws)
    (S45 : (c + μ * a) * nws + c * nd ≤ c * nvs + μ * a * nyq + (c + μ * a) * nv'w) :
    Hx' + Gx' - (Hs + Gs) + c' / 2 * nv's ≤ (Hx + Gx - (Hs + Gs) + c / 2 * nvs) / (1 + a) := by
  have h1a : 0 < 1 + a := by linarith
  rw [le_div_iff₀ h1a]
  have hLb : L * b ^ 2 * (1 + a) = c := by
    have : (L * b ^ 2 * (1 + a) - c) * (1 + a) = 0 := by
      have : L * b ^ 2 * (1 + a) * (1 + a) = L * a ^ 2 := by
        linear_combination L * (b * (1 + a) + a) * hb
      linear_combination this + hst
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have e1 := mul_le_mul_of_nonneg_left D1 h1a.le
  have e2 := mul_le_mul_of_nonneg_left C2 ha.le
  have e3 := mul_le_mul_of_nonneg_left S3 ha.le
  have e4 : (1 + a) * c' * nv's = (c + a * μ) * nv's := by rw [hc']
  have e5 : L * b ^ 2 * (1 + a) * nd = c * nd := by rw [hLb]
  have e6 : (1 + a) * (b * iGd) = a * iGd := by linear_combination iGd * hb
  have k1 : a * (κ * nv'w) = (c + μ * a) / 2 * nv'w := by linear_combination nv'w / 2 * hκ
  have k2 : a * (κ * nv's) = (c + μ * a) / 2 * nv's := by linear_combination nv's / 2 * hκ
  have k3 : a * (κ * nws) = (c + μ * a) / 2 * nws := by linear_combination nws / 2 * hκ
  nlinarith

end RRAux_NAGFlow_AFB_theorem_7_3

open NAGFlow.AFB in
theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : V → ℝ) (gradh : V → V) (g : V → ℝ) (D Q : Set V) (μ L : ℝ)
    (hprob : IsAFBProblem h gradh g D Q μ L)
    (α γ : ℕ → ℝ) (x y w v : ℕ → V) (hrun : IsAFBRun gradh g D Q μ L α γ x y w v)
    (xstar : V) (hxstar : IsMinimizer h g D Q xstar) (hx0D : x 0 ∈ D) :
    (∀ k : ℕ, lyap h g xstar x v γ (k + 1) ≤ lyap h g xstar x v γ k / (1 + α k)) ∧
      (∀ k : ℕ, lyap h g xstar x v γ k ≤
        lyap h g xstar x v γ 0 *
          min (4 * L / (Real.sqrt (γ 0) * k + 2 * Real.sqrt L) ^ 2)
            ((1 + Real.sqrt (min (γ 0) μ / L)) ^ (-(k : ℤ)))) ∧
      (∀ k : ℕ, 1 ≤ k → lyap h g xstar x v γ k ≤
        (L / γ 0 * (fObj h g (x 0) - fObj h g xstar) + L / 2 * ‖v 0 - xstar‖ ^ 2) *
          min (4 / (k : ℝ) ^ 2) ((1 + Real.sqrt (min (γ 0) μ / L)) ^ (1 - (k : ℤ)))) := by
  have hc := hprob.h_class
  have hμ := hc.mu_nonneg
  have hL := hc.L_pos
  have hQ := hprob.Q_convex
  have hD : Convex ℝ D := hprob.g_convex.1
  have hQD : Convex ℝ (Q ∩ D) := hQ.inter hD
  have hgQD : ConvexOn ℝ (Q ∩ D) g := hprob.g_convex.subset Set.inter_subset_right hQD
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
  -- convex combinations with weights 1/(1+a), a/(1+a)
  have hcomb : ∀ (S : Set V), Convex ℝ S → ∀ a : ℝ, 0 < a → ∀ p q : V, p ∈ S → q ∈ S →
      (1 / (1 + a)) • (p + a • q) ∈ S := by
    intro S hS a ha p q hp hq
    have e : (1 / (1 + a)) • (p + a • q) = (1 / (1 + a)) • p + (a / (1 + a)) • q := by
      rw [smul_add, smul_smul]; congr 2; ring
    rw [e]
    exact hS hp hq (by positivity) (by positivity) (by field_simp)
  have hvQ : ∀ k, v k ∈ Q := by
    intro k
    cases k with
    | zero => exact hrun.v0_mem
    | succ k => exact (hrun.v_mem k).1
  have hxQD : ∀ k, x k ∈ Q ∩ D := by
    intro k
    induction k with
    | zero => exact ⟨hrun.x0_mem, hx0D⟩
    | succ k ih =>
      rw [hrun.x_eq k]
      exact hcomb _ hQD _ (hrun.alpha_pos k) _ _ ih (hrun.v_mem k)
  have hyQ : ∀ k, y k ∈ Q := by
    intro k
    rw [hrun.y_eq k]
    exact hcomb _ hQ _ (hrun.alpha_pos k) _ _ (hxQD k).1 (hvQ k)
  have h86 : ∀ k : ℕ, lyap h g xstar x v γ (k + 1) ≤ lyap h g xstar x v γ k / (1 + α k) := by
    intro k
    have ha := hrun.alpha_pos k
    have hck := hγp k
    have hgam := hrun.gamma_eq k
    have hst := hrun.step_rel k
    have hye := hrun.y_eq k
    have hwe := hrun.w_eq k
    have hxe := hrun.x_eq k
    have hmin := hrun.v_argmin k
    have hv'QD := hrun.v_mem k
    have hx0 := hxQD k
    have hx'Q := (hxQD (k + 1)).1
    have hy0 := hyQ k
    set a := α k
    set c := γ k
    set c' := γ (k + 1)
    set x' := x (k + 1)
    set v' := v (k + 1)
    set x0 := x k
    set v0 := v k
    set y0 := y k
    set w0 := w k
    set G := gradh y0
    have hc' : (1 + a) * c' = c + a * μ := by
      rw [hgam]; field_simp
    have hcμ : 0 < c + μ * a := by have := mul_nonneg hμ ha.le; linarith
    have hy1 : (1 + a) • y0 = x0 + a • v0 := by
      rw [hye, smul_smul, mul_one_div_cancel (by linarith), one_smul]
    have hw1 : (c + μ * a) • w0 = c • v0 + (μ * a) • y0 := by
      rw [hwe, smul_smul, mul_one_div_cancel hcμ.ne', one_smul]
    have hx1 : (1 + a) • x' = x0 + a • v' := by
      rw [hxe, smul_smul, mul_one_div_cancel (by linarith), one_smul]
    set b := a / (1 + a) with hbdef
    have hb : b * (1 + a) = a := by rw [hbdef]; field_simp
    set d := v' - v0
    have hxy : x' - y0 = b • d := by
      have h1 : (1 + a) • (x' - y0) = a • d := by
        simp only [d]; linear_combination (norm := module) hx1 - hy1
      have h2 : x' - y0 = (1 + a)⁻¹ • ((1 + a) • (x' - y0)) := by
        rw [smul_smul, inv_mul_cancel₀ (by linarith), one_smul]
      rw [h2, h1, smul_smul, hbdef, div_eq_inv_mul]
    have hxy2 : x0 - y0 = (-a) • (v0 - y0) := by
      linear_combination (norm := module) -hy1
    -- descent of h on Q
    have D1 := RRAux_NAGFlow_AFB_theorem_7_3.descentOn h gradh L hL.le Q hQ hc.hasGrad
      hc.grad_lip y0 x' hy0 hx'Q
    rw [hxy, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at D1
    -- convexity of g on D
    have Gc : (1 + a) * g x' ≤ g x0 + a * g v' := by
      have e : x' = (1 / (1 + a)) • x0 + (a / (1 + a)) • v' := by
        rw [hxe, smul_add, smul_smul]; congr 2; ring
      have := hprob.g_convex.2 hx0.2 hv'QD.2 (by positivity : (0:ℝ) ≤ 1 / (1 + a))
        (by positivity : (0:ℝ) ≤ a / (1 + a)) (by field_simp)
      rw [← e] at this
      simp only [smul_eq_mul] at this
      have h1a : (0:ℝ) < 1 + a := by linarith
      have := mul_le_mul_of_nonneg_left this h1a.le
      have e2 : (1 + a) * (1 / (1 + a) * g x0 + a / (1 + a) * g v') = g x0 + a * g v' := by
        field_simp
      linarith
    -- μ-convexity of h at y
    have C1 := hc.mu_convex x0 hx0.1 y0 hy0
    rw [hxy2, real_inner_smul_right] at C1
    have C1' : h x0 ≥ h y0 + -a * inner ℝ G (v0 - y0) := by
      have := mul_nonneg (div_nonneg hμ (by norm_num : (0:ℝ) ≤ 2))
        (sq_nonneg ‖(-a) • (v0 - y0)‖)
      linarith
    have C2 := hc.mu_convex xstar hxstar.1.1 y0 hy0
    have C2' : h xstar ≥ h y0 + inner ℝ G (xstar - y0) + μ / 2 * ‖y0 - xstar‖ ^ 2 := by
      rw [norm_sub_rev] at C2; linarith
    have hrel : inner ℝ G (v' - xstar)
        = inner ℝ G d + inner ℝ G (v0 - y0) - inner ℝ G (xstar - y0) := by
      rw [← inner_add_right, ← inner_sub_right]; congr 1; simp only [d]; abel
    have hlin : inner ℝ G v' - inner ℝ G xstar = inner ℝ G (v' - xstar) := by
      rw [inner_sub_right]
    -- optimality of v'
    set κ := (c + μ * a) / (2 * a) with hκdef
    have hκ0 : 0 ≤ κ := by positivity
    have hκ : 2 * a * κ = c + μ * a := by rw [hκdef]; field_simp
    have S3 := RRAux_NAGFlow_AFB_theorem_7_3.argmin_strong g (Q ∩ D) hgQD κ hκ0 G w0 v' hv'QD
      (fun u hu => by have := hmin u hu; simp only [afbObj] at this; exact this) xstar hxstar.1
    rw [norm_sub_rev xstar v', norm_sub_rev xstar w0] at S3
    have S45 := RRAux_NAGFlow_AFB_theorem_7_3.s45 c (μ * a) (mul_nonneg hμ ha.le) v0 y0 w0 v'
      xstar hw1
    show h x' + g x' - (h xstar + g xstar) + c' / 2 * ‖v' - xstar‖ ^ 2
      ≤ (h x0 + g x0 - (h xstar + g xstar) + c / 2 * ‖v0 - xstar‖ ^ 2) / (1 + a)
    exact RRAux_NAGFlow_AFB_theorem_7_3.key a b c c' μ L κ (h x0) (h x') (h y0) (h xstar)
      (g x0) (g x') (g v') (g xstar) (inner ℝ G d) (inner ℝ G (v0 - y0))
      (inner ℝ G (xstar - y0)) (inner ℝ G (v' - xstar)) (inner ℝ G v') (inner ℝ G xstar)
      (‖d‖ ^ 2) (‖y0 - xstar‖ ^ 2) (‖v' - w0‖ ^ 2) (‖v' - xstar‖ ^ 2) (‖w0 - xstar‖ ^ 2)
      (‖v0 - xstar‖ ^ 2) hck ha hμ hc' hb hst hκ D1 Gc C1' C2' hrel hlin S3 S45
  have h0 : 0 ≤ lyap h g xstar x v γ 0 := by
    show 0 ≤ fObj h g (x 0) - fObj h g xstar + γ 0 / 2 * ‖v 0 - xstar‖ ^ 2
    have := hxstar.2 (x 0) (hxQD 0)
    have := hrun.gamma0_pos
    have : 0 ≤ fObj h g (x 0) - fObj h g xstar := by linarith
    positivity
  obtain ⟨r87, r88⟩ := RRAux_NAGFlow_AFB_theorem_7_3.rates μ L hL hμ α γ hrun.gamma0_pos
    hrun.alpha_pos hge hrun.step_rel (lyap h g xstar x v γ) h86 h0
  refine ⟨h86, r87, fun k hk => ?_⟩
  have hC : L / γ 0 * (fObj h g (x 0) - fObj h g xstar) + L / 2 * ‖v 0 - xstar‖ ^ 2
      = L / γ 0 * lyap h g xstar x v γ 0 := by
    show _ = L / γ 0 * (fObj h g (x 0) - fObj h g xstar + γ 0 / 2 * ‖v 0 - xstar‖ ^ 2)
    have := hrun.gamma0_pos.ne'
    field_simp
  rw [hC]
  exact r88 k hk

#print axioms solution
