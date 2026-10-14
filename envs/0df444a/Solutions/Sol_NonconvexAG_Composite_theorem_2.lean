-- Prove2me | solution 1 for NonconvexAG.Composite.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:19:25.700991+00:00
-- url     : https://prove2.me/submissions/e3efa040-9ef4-4414-9690-769c5424a507

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Composite_ProxMap
import Definitions.Def_NonconvexAG_Composite_AGRun

namespace RRAux_NonconvexAG_Composite_theorem_2

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


section
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

lemma prox3 (X : F → ℝ) (K : Set F) (hX : ConvexOn ℝ K X) (c : ℝ) (hc : 0 < c) (G w v' : F)
    (hv' : v' ∈ K)
    (hmin : ∀ u ∈ K, inner ℝ G v' + ‖v' - w‖ ^ 2 / (2 * c) + X v'
      ≤ inner ℝ G u + ‖u - w‖ ^ 2 / (2 * c) + X u) (u : F) (hu : u ∈ K) :
    inner ℝ G v' + ‖v' - w‖ ^ 2 / (2 * c) + X v' + ‖u - v'‖ ^ 2 / (2 * c)
      ≤ inner ℝ G u + ‖u - w‖ ^ 2 / (2 * c) + X u := by
  have := argmin_strong X K hX (1 / (2 * c)) (by positivity) G w v' hv'
    (fun u hu => by
      have := hmin u hu
      rw [one_div_mul_eq_div, one_div_mul_eq_div]; linarith) u hu
  rw [one_div_mul_eq_div, one_div_mul_eq_div, one_div_mul_eq_div] at this
  linarith

lemma neg_grad (f : F → ℝ) (G x : F) (hg : HasGradientAt f G x) :
    HasGradientAt (fun z => -f z) (-G) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  have := hg.neg
  rwa [← map_neg] at this

lemma upper (f : F → ℝ) (gf : F → F) (L : ℝ) (hL : 0 ≤ L) (hg : ∀ x, HasGradientAt f (gf x) x)
    (hl : ∀ x y, ‖gf x - gf y‖ ≤ L * ‖x - y‖) (x y : F) :
    f y ≤ f x + inner ℝ (gf x) (y - x) + L / 2 * ‖y - x‖ ^ 2 :=
  descentOn f gf L hL Set.univ convex_univ (fun x _ => hasGradientWithinAt_iff_hasFDerivWithinAt.2
      (hasGradientAt_iff_hasFDerivAt.1 (hg x)).hasFDerivWithinAt)
    (fun x _ y _ => hl x y) x y (Set.mem_univ _) (Set.mem_univ _)

lemma lower (f : F → ℝ) (gf : F → F) (L : ℝ) (hL : 0 ≤ L) (hg : ∀ x, HasGradientAt f (gf x) x)
    (hl : ∀ x y, ‖gf x - gf y‖ ≤ L * ‖x - y‖) (x y : F) :
    f x + inner ℝ (gf x) (y - x) ≤ f y + L / 2 * ‖y - x‖ ^ 2 := by
  have := upper (fun z => -f z) (fun z => -gf z) L hL (fun z => neg_grad f (gf z) z (hg z))
    (fun a b => by rw [← neg_sub', norm_neg]; exact hl a b) x y
  simp only [inner_neg_left] at this
  linarith

lemma conv_grad_at (h : F → ℝ) (hc : ConvexOn ℝ Set.univ h) (G x : F) (hg : HasGradientAt h G x)
    (y : F) : h x + inner ℝ G (y - x) ≤ h y := by
  have hg' : ConvexOn ℝ Set.univ (h ∘ AffineMap.lineMap (k := ℝ) x y) := by
    have := hc.comp_affineMap (AffineMap.lineMap (k := ℝ) x y)
    simpa using this
  have e : (h ∘ AffineMap.lineMap (k := ℝ) x y) = fun t : ℝ => h (x + t • (y - x)) := by
    funext t; simp [AffineMap.lineMap_apply, add_comm]
  rw [e] at hg'
  have hl : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y - x)).const_add x
  have hfx : HasFDerivAt h (InnerProductSpace.toDual ℝ F G) (x + (0:ℝ) • (y - x)) := by
    simpa using hg.hasFDerivAt
  have hd := hfx.comp_hasDerivAt (0:ℝ) hl
  rw [InnerProductSpace.toDual_apply_apply] at hd
  have := hg'.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  rw [slope_def_field] at this
  have e1 : x + (1:ℝ) • (y - x) = y := by rw [one_smul]; abel
  simp only [e1, zero_smul, add_zero, sub_zero, div_one] at this
  linarith

lemma frac_num (al lm be q : ℝ) (hal : 0 < al) (hlm : 0 < lm) (hbe : 0 < be) (hab : al * lm ≤ be)
    (hq : 0 ≤ q) : al ^ 2 * q / (2 * be) ≤ al * (q / (2 * lm)) := by
  rw [div_le_iff₀ (by positivity)]
  have e : al * (q / (2 * lm)) * (2 * be) = al * q * be / lm := by field_simp
  rw [e, le_div_iff₀ hlm]
  have := mul_le_mul_of_nonneg_left hab (by positivity : 0 ≤ al * q)
  nlinarith

lemma step (f h X : F → ℝ) (gf gh : F → F) (Lf Lh : ℝ) (K : Set F) (hX : ConvexOn ℝ K X)
    (hfg : ∀ x, HasGradientAt f (gf x) x) (hfl : ∀ x y, ‖gf x - gf y‖ ≤ Lf * ‖x - y‖) (hLf : 0 ≤ Lf)
    (hhg : ∀ x, HasGradientAt h (gh x) x) (hhl : ∀ x y, ‖gh x - gh y‖ ≤ Lh * ‖x - y‖) (hLh : 0 ≤ Lh)
    (hhc : ConvexOn ℝ Set.univ h)
    (a0 y0 md xk agk xs : F) (al lm be : ℝ) (hal0 : 0 < al) (hal1 : al ≤ 1) (hlm : 0 < lm)
    (hbe : 0 < be) (hab : al * lm ≤ be) (hmd : md = (1 - al) • a0 + al • y0)
    (hxkK : xk ∈ K) (hagK : agk ∈ K) (hxsK : xs ∈ K)
    (hbar : (1 - al) • a0 + al • xk ∈ K)
    (hXbar : X ((1 - al) • a0 + al • xk) ≤ (1 - al) * X a0 + al * X xk)
    (hxk : ∀ u ∈ K, inner ℝ (gf md + gh md) xk + ‖xk - y0‖ ^ 2 / (2 * lm) + X xk
      ≤ inner ℝ (gf md + gh md) u + ‖u - y0‖ ^ 2 / (2 * lm) + X u)
    (hag : ∀ u ∈ K, inner ℝ (gf md + gh md) agk + ‖agk - md‖ ^ 2 / (2 * be) + X agk
      ≤ inner ℝ (gf md + gh md) u + ‖u - md‖ ^ 2 / (2 * be) + X u) :
    f agk + h agk + X agk
      ≤ (1 - al) * (f a0 + h a0 + X a0 + Lf / 2 * ‖a0 - md‖ ^ 2)
        + al * (f xs + h xs + X xs + Lf / 2 * ‖xs - md‖ ^ 2)
        - (1 / (2 * be) - (Lf + Lh) / 2) * ‖agk - md‖ ^ 2
        + al / (2 * lm) * (‖xs - y0‖ ^ 2 - ‖xs - xk‖ ^ 2) := by
  set g := gf md + gh md with hg
  set xb := (1 - al) • a0 + al • xk with hxb
  have F1 := prox3 X K hX lm hlm g y0 xk hxkK hxk xs hxsK
  have F2 := hag xb hbar
  have F3 : ‖xb - md‖ ^ 2 = al ^ 2 * ‖xk - y0‖ ^ 2 := by
    have : xb - md = al • (xk - y0) := by rw [hxb, hmd]; module
    rw [this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have F4 := frac_num al lm be (‖xk - y0‖ ^ 2) hal0 hlm hbe hab (by positivity)
  have F5 : inner ℝ g xb = (1 - al) * inner ℝ g a0 + al * inner ℝ g xk := by
    rw [hxb, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have F6 := upper f gf Lf hLf hfg hfl md agk
  have F6' := upper h gh Lh hLh hhg hhl md agk
  have F7 := lower f gf Lf hLf hfg hfl md a0
  have F7' := lower f gf Lf hLf hfg hfl md xs
  have F8 := conv_grad_at h hhc (gh md) md (hhg md) a0
  have F8' := conv_grad_at h hhc (gh md) md (hhg md) xs
  have hal' : 0 ≤ 1 - al := by linarith
  have G7 := mul_le_mul_of_nonneg_left F7 hal'
  have G7' := mul_le_mul_of_nonneg_left F7' hal0.le
  have G8 := mul_le_mul_of_nonneg_left F8 hal'
  have G8' := mul_le_mul_of_nonneg_left F8' hal0.le
  have G1 := mul_le_mul_of_nonneg_left F1 hal0.le
  rw [F3] at F2
  simp only [hg, inner_add_left, inner_sub_right] at G7 G7' G8 G8' G1 F2 F5 F6 F6' ⊢
  rw [F5] at F2
  have e1 : al / (2 * lm) * (‖xs - y0‖ ^ 2 - ‖xs - xk‖ ^ 2)
      = al * (‖xs - y0‖ ^ 2 / (2 * lm)) - al * (‖xs - xk‖ ^ 2 / (2 * lm)) := by ring
  have e2 : (1 / (2 * be) - (Lf + Lh) / 2) * ‖agk - md‖ ^ 2
      = ‖agk - md‖ ^ 2 / (2 * be) - Lf / 2 * ‖agk - md‖ ^ 2 - Lh / 2 * ‖agk - md‖ ^ 2 := by ring
  rw [e1, e2]
  linarith

lemma err (a0 y0 xs md : F) (al Lf M : ℝ) (hal0 : 0 ≤ al) (hal1 : al ≤ 1) (hLf : 0 ≤ Lf)
    (ha0 : ‖a0‖ ≤ M) (hy0 : ‖y0‖ ≤ M) (hmd : md = (1 - al) • a0 + al • y0) :
    (1 - al) * (Lf / 2 * ‖a0 - md‖ ^ 2) + al * (Lf / 2 * ‖xs - md‖ ^ 2)
      ≤ al * Lf * (‖xs‖ ^ 2 + 2 * M ^ 2) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans ha0
  have e1 : a0 - md = al • (a0 - y0) := by rw [hmd]; module
  have h1 : ‖a0 - y0‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith)
  have h1' : ‖a0 - md‖ ^ 2 ≤ al ^ 2 * (4 * M ^ 2) := by
    rw [e1, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith
  have h2 : ‖md‖ ≤ M := by
    rw [hmd]
    calc ‖(1 - al) • a0 + al • y0‖ ≤ ‖(1 - al) • a0‖ + ‖al • y0‖ := norm_add_le _ _
      _ = (1 - al) * ‖a0‖ + al * ‖y0‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hal0]
      _ ≤ (1 - al) * M + al * M := by
        have := mul_le_mul_of_nonneg_left ha0 (by linarith : 0 ≤ 1 - al)
        have := mul_le_mul_of_nonneg_left hy0 hal0
        linarith
      _ = M := by ring
  have h3 : ‖xs - md‖ ^ 2 ≤ 2 * ‖xs‖ ^ 2 + 2 * M ^ 2 := by
    have := norm_sub_le xs md
    have h4 : ‖md‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    nlinarith [sq_nonneg (‖xs‖ - ‖md‖), norm_nonneg (xs - md), norm_nonneg xs, norm_nonneg md]
  have k1 : (1 - al) * (Lf / 2 * ‖a0 - md‖ ^ 2) ≤ (1 - al) * (Lf / 2 * (al ^ 2 * (4 * M ^ 2))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1' (by linarith)) (by linarith)
  have k2 : al * (Lf / 2 * ‖xs - md‖ ^ 2) ≤ al * (Lf / 2 * (2 * ‖xs‖ ^ 2 + 2 * M ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by linarith)) hal0
  have k3 : (1 - al) * (Lf / 2 * (al ^ 2 * (4 * M ^ 2))) ≤ al * Lf * M ^ 2 := by
    have : al * (1 - al) ≤ 1 / 2 := by nlinarith [sq_nonneg (al - 1 / 2)]
    have h5 : 0 ≤ al * Lf * M ^ 2 := by positivity
    have e : (1 - al) * (Lf / 2 * (al ^ 2 * (4 * M ^ 2))) = 2 * (al * (1 - al)) * (al * Lf * M ^ 2) := by
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_right this h5
    linarith
  have e2 : al * (Lf / 2 * (2 * ‖xs‖ ^ 2 + 2 * M ^ 2)) = al * Lf * ‖xs‖ ^ 2 + al * Lf * M ^ 2 := by
    ring
  have e3 : al * Lf * (‖xs‖ ^ 2 + 2 * M ^ 2) = al * Lf * ‖xs‖ ^ 2 + 2 * (al * Lf * M ^ 2) := by ring
  linarith

end

lemma tele_base (e1 b gsq lm D0 D1 LB : ℝ) (hlm : 0 < lm)
    (e0 : ℝ) (h : e1 ≤ (1 - 1) * e0 - b * gsq + 1 / (2 * lm) * (D0 - D1) + 1 * LB) :
    e1 / 1 + b / 1 * gsq ≤ (1 / (lm * 1) * D0 - 1 / (lm * 1) * D1) / 2 + LB / 1 := by
  have e : 1 / (2 * lm) * (D0 - D1) = (1 / (lm * 1) * D0 - 1 / (lm * 1) * D1) / 2 := by
    field_simp
  rw [div_one, div_one, div_one]
  linarith

lemma tele_step (e0 e1 al lm b gsq G0 G1 Dj Dj1 LB S C c0 : ℝ) (hal0 : 0 < al) (hal1 : al < 1)
    (hlm : 0 < lm) (hG0 : 0 < G0) (hG : G1 = (1 - al) * G0) (hDj : 0 ≤ Dj)
    (hrec : e1 ≤ (1 - al) * e0 - b * gsq + al / (2 * lm) * (Dj - Dj1) + al * LB)
    (hih : e0 / G0 + S ≤ (C - c0 * Dj) / 2 + LB / G0)
    (hc : al / (lm * G1) ≤ c0) :
    e1 / G1 + (S + b / G1 * gsq) ≤ (C - al / (lm * G1) * Dj1) / 2 + LB / G1 := by
  have hG1 : 0 < G1 := by rw [hG]; exact mul_pos (by linarith) hG0
  have ha1 : 1 - al ≠ 0 := by linarith
  have hG0' : G0 ≠ 0 := hG0.ne'
  have hlm' : lm ≠ 0 := hlm.ne'
  have h1 : e1 / G1 ≤ e0 / G0 - b / G1 * gsq + al / (lm * G1) / 2 * (Dj - Dj1) + al * LB / G1 := by
    rw [div_le_iff₀ hG1]
    have e : (e0 / G0 - b / G1 * gsq + al / (lm * G1) / 2 * (Dj - Dj1) + al * LB / G1) * G1
        = (1 - al) * e0 - b * gsq + al / (2 * lm) * (Dj - Dj1) + al * LB := by
      rw [hG]; field_simp; try ring
    rw [e]; exact hrec
  have h2 : al / (lm * G1) * Dj ≤ c0 * Dj := mul_le_mul_of_nonneg_right hc hDj
  have h3 : LB / G0 + al * LB / G1 = LB / G1 := by
    rw [hG]; field_simp; try ring
  have e4 : al / (lm * G1) / 2 * (Dj - Dj1) = al / (lm * G1) * Dj / 2 - al / (lm * G1) * Dj1 / 2 := by
    ring
  have e5 : (C - al / (lm * G1) * Dj1) / 2 = C / 2 - al / (lm * G1) * Dj1 / 2 := by ring
  have e6 : (C - c0 * Dj) / 2 = C / 2 - c0 * Dj / 2 := by ring
  rw [e4] at h1; rw [e5]; rw [e6] at hih
  linarith

lemma gm_num (be L q : ℝ) (hbe : 0 < be) :
    (1 / (2 * be) - L / 2) * q = be * (1 - L * be) / 2 * (q / be ^ 2) := by
  field_simp

end RRAux_NonconvexAG_Composite_theorem_2

open RRAux_NonconvexAG_Composite_theorem_2

open ConvexOptAlg.SmoothGD NonconvexAG.Composite in
theorem solution {n : ℕ} (f h : NonconvexAG.Smooth.E n → ℝ) (gf gh : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (K : Set (NonconvexAG.Smooth.E n)) (X : NonconvexAG.Smooth.E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n → ℝ → NonconvexAG.Smooth.E n) (hP : IsProxMap K X P)
    (α β lam : ℕ → ℝ) (hstep : NonconvexAG.Smooth.AGStepsizes α β lam) (x0 : NonconvexAG.Smooth.E n)
    (M : ℝ) (hA2 : Assumption2 P M) (hx0 : ‖x0‖ ≤ M)
    (N : ℕ) (hN : 1 ≤ N)
    (h29 : ∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ β k ∧ (Lf + Lh) * β k < 1)
    (h210 : ∀ k ∈ Finset.Icc 1 N, 2 ≤ k →
      α k / (lam k * NonconvexAG.Smooth.Gamma α k) ≤ α (k - 1) / (lam (k - 1) * NonconvexAG.Smooth.Gamma α (k - 1)))
    (xstar : NonconvexAG.Smooth.E n) (hxstar : xstar ∈ K)
    (hopt : ∀ u ∈ K, f xstar + h xstar + X xstar ≤ f u + h u + X u) :
    let Φ : NonconvexAG.Smooth.E n → ℝ := fun x => f x + h x + X x
    let gΨ : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n := fun x => gf x + gh x
    let xk : ℕ → NonconvexAG.Smooth.E n := xSeq gΨ P α β lam x0
    let xag : ℕ → NonconvexAG.Smooth.E n := xagSeq gΨ P α β lam x0
    let xmd : ℕ → NonconvexAG.Smooth.E n := xmdSeq gΨ P α β lam x0
    -- (2.44)
    (Finset.Icc 1 N).inf' (Finset.nonempty_Icc.mpr hN)
        (fun k => ‖gradMap P (xmd k) (gΨ (xmd k)) (β k)‖ ^ 2) ≤
      2 * (∑ k ∈ Finset.Icc 1 N, (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k * (1 - (Lf + Lh) * β k))⁻¹ *
        (‖x0 - xstar‖ ^ 2 / (2 * lam 1) + Lf / NonconvexAG.Smooth.Gamma α N * (‖xstar‖ ^ 2 + 2 * M ^ 2)) ∧
    -- (2.45)
    (Lf = 0 → Φ (xag N) - Φ xstar ≤ NonconvexAG.Smooth.Gamma α N * ‖x0 - xstar‖ ^ 2 / (2 * lam 1)) := by
  intro Φ gΨ xk xag xmd
  obtain ⟨hLf, hfg, hfl⟩ := hf
  obtain ⟨hLh, hhg, hhl⟩ := hh
  obtain ⟨hα1, hαk, hβ, hlam⟩ := hstep
  have hM : 0 ≤ M := (norm_nonneg _).trans hx0
  have hxrec : ∀ k, xk (k + 1) = P (xk k) (gΨ (xmd (k + 1))) (lam (k + 1)) := fun k => rfl
  have hagrec : ∀ k, xag (k + 1) = P (xmd (k + 1)) (gΨ (xmd (k + 1))) (β (k + 1)) := fun k => rfl
  have hmdrec : ∀ k, xmd (k + 1) = (1 - α (k + 1)) • xag k + α (k + 1) • xk k := fun k => rfl
  have hx00 : xk 0 = x0 := rfl
  have hag00 : xag 0 = x0 := rfl
  have hxK : ∀ k, xk (k + 1) ∈ K := fun k => (hP _ _ _ (hlam (k + 1) (by omega))).1
  have hagK : ∀ k, xag (k + 1) ∈ K := fun k => (hP _ _ _ (hβ (k + 1) (by omega))).1
  have hxM : ∀ k, ‖xk k‖ ≤ M := by
    intro k; cases k with
    | zero => exact hx0
    | succ j => exact hA2 _ _ _ (hlam _ (by omega))
  have hagM : ∀ k, ‖xag k‖ ≤ M := by
    intro k; cases k with
    | zero => exact hx0
    | succ j => exact hA2 _ _ _ (hβ _ (by omega))
  have hΓ1 : NonconvexAG.Smooth.Gamma α 1 = 1 := by simp [NonconvexAG.Smooth.Gamma]
  have hΓs : ∀ k, 1 ≤ k → NonconvexAG.Smooth.Gamma α (k + 1)
      = (1 - α (k + 1)) * NonconvexAG.Smooth.Gamma α k := by
    intro k hk
    simp only [NonconvexAG.Smooth.Gamma]
    rw [Finset.prod_Icc_succ_top (by omega)]; ring
  have hΓpos : ∀ k, 1 ≤ k → 0 < NonconvexAG.Smooth.Gamma α k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rw [hΓ1]; norm_num
    | succ k hk ih =>
      rw [hΓs k hk]
      have := hαk (k + 1) (by omega)
      exact mul_pos (by linarith) ih
  have hal : ∀ k, 1 ≤ k → 0 < α k ∧ α k ≤ 1 := by
    intro k hk
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · have : k = 1 := by omega
      subst this; rw [hα1]; norm_num
    · have := hαk k h2; exact ⟨this.1, this.2.le⟩
  -- one step
  have hrec : ∀ k, k + 1 ≤ N →
      f (xag (k + 1)) + h (xag (k + 1)) + X (xag (k + 1)) - (f xstar + h xstar + X xstar)
        ≤ (1 - α (k + 1)) * (f (xag k) + h (xag k) + X (xag k) - (f xstar + h xstar + X xstar))
          - β (k + 1) * (1 - (Lf + Lh) * β (k + 1)) / 2
            * ‖gradMap P (xmd (k + 1)) (gΨ (xmd (k + 1))) (β (k + 1))‖ ^ 2
          + α (k + 1) / (2 * lam (k + 1)) * (‖xstar - xk k‖ ^ 2 - ‖xstar - xk (k + 1)‖ ^ 2)
          + α (k + 1) * (Lf * (‖xstar‖ ^ 2 + 2 * M ^ 2)) := by
    intro k hk
    have hmem : k + 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨by omega, hk⟩
    obtain ⟨hab, _⟩ := h29 (k + 1) hmem
    obtain ⟨hal0, hal1⟩ := hal (k + 1) (by omega)
    have hbe := hβ (k + 1) (by omega)
    have hlm := hlam (k + 1) (by omega)
    have hbar : (1 - α (k + 1)) • xag k + α (k + 1) • xk (k + 1) ∈ K ∧
        X ((1 - α (k + 1)) • xag k + α (k + 1) • xk (k + 1))
          ≤ (1 - α (k + 1)) * X (xag k) + α (k + 1) * X (xk (k + 1)) := by
      rcases k with _ | j
      · rw [hα1]; simp only [sub_self, zero_smul, one_smul, zero_add, zero_mul, one_mul]
        exact ⟨hxK 0, le_rfl⟩
      · exact ⟨hX.1 (hagK j) (hxK (j + 1)) (by linarith) hal0.le (by ring),
          hX.2 (hagK j) (hxK (j + 1)) (by linarith) hal0.le (by ring)⟩
    have hs := step f h X gf gh Lf Lh K hX hfg hfl hLf hhg hhl hLh hhc (xag k) (xk k) (xmd (k + 1))
      (xk (k + 1)) (xag (k + 1)) xstar (α (k + 1)) (lam (k + 1)) (β (k + 1)) hal0 hal1 hlm hbe hab
      (hmdrec k) (hxK k) (hagK k) hxstar hbar.1 hbar.2
      (fun u hu => by rw [hxrec k]; exact (hP _ _ _ hlm).2 u hu)
      (fun u hu => by rw [hagrec k]; exact (hP _ _ _ hbe).2 u hu)
    have he := err (xag k) (xk k) xstar (xmd (k + 1)) (α (k + 1)) Lf M hal0.le hal1 hLf (hagM k)
      (hxM k) (hmdrec k)
    have hg : ‖gradMap P (xmd (k + 1)) (gΨ (xmd (k + 1))) (β (k + 1))‖ ^ 2
        = ‖xag (k + 1) - xmd (k + 1)‖ ^ 2 / β (k + 1) ^ 2 := by
      simp only [gradMap]
      rw [← hagrec k, norm_smul, mul_pow, norm_sub_rev, Real.norm_eq_abs, sq_abs]
      field_simp
    have hgm := gm_num (β (k + 1)) (Lf + Lh) (‖xag (k + 1) - xmd (k + 1)‖ ^ 2) hbe
    rw [← hg] at hgm
    have e1 : α (k + 1) * (Lf * (‖xstar‖ ^ 2 + 2 * M ^ 2))
        = α (k + 1) * Lf * (‖xstar‖ ^ 2 + 2 * M ^ 2) := by ring
    rw [e1]
    linarith
  -- telescoping
  have tele : ∀ j, 1 ≤ j → j ≤ N →
      (f (xag j) + h (xag j) + X (xag j) - (f xstar + h xstar + X xstar))
          / NonconvexAG.Smooth.Gamma α j
        + ∑ k ∈ Finset.Icc 1 j, β k * (1 - (Lf + Lh) * β k) / 2 / NonconvexAG.Smooth.Gamma α k
            * ‖gradMap P (xmd k) (gΨ (xmd k)) (β k)‖ ^ 2
        ≤ (1 / (lam 1 * 1) * ‖xstar - xk 0‖ ^ 2
            - α j / (lam j * NonconvexAG.Smooth.Gamma α j) * ‖xstar - xk j‖ ^ 2) / 2
          + Lf * (‖xstar‖ ^ 2 + 2 * M ^ 2) / NonconvexAG.Smooth.Gamma α j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro hN1
      have h0 := hrec 0 hN1
      rw [hα1] at h0
      rw [Finset.Icc_self, Finset.sum_singleton, hΓ1, hα1]
      exact tele_base _ _ _ (lam 1) _ _ _ (hlam 1 le_rfl) _ h0
    | succ j hj ih =>
      intro hjN
      have ih' := ih (by omega)
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1)]
      have hmem : j + 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨by omega, hjN⟩
      have hc := h210 (j + 1) hmem (by omega)
      simp only [Nat.add_sub_cancel] at hc
      have ha := hαk (j + 1) (by omega)
      exact tele_step _ _ (α (j + 1)) (lam (j + 1)) _ _ (NonconvexAG.Smooth.Gamma α j) _ _ _ _ _ _ _
        ha.1 ha.2 (hlam _ (by omega)) (hΓpos j hj) (hΓs j hj) (by positivity) (hrec j hjN) ih' hc
  have T := tele N hN le_rfl
  have hΓN := hΓpos N hN
  have hRN : 0 ≤ (f (xag N) + h (xag N) + X (xag N) - (f xstar + h xstar + X xstar))
      / NonconvexAG.Smooth.Gamma α N := by
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    exact div_nonneg (sub_nonneg.2 (hopt _ (hagK m))) hΓN.le
  have hcN : 0 ≤ α N / (lam N * NonconvexAG.Smooth.Gamma α N) * ‖xstar - xk N‖ ^ 2 := by
    obtain ⟨h1, _⟩ := hal N hN
    have := hlam N hN
    positivity
  have hD0 : ‖xstar - xk 0‖ ^ 2 = ‖x0 - xstar‖ ^ 2 := by rw [hx00, norm_sub_rev]
  have hterm : ∀ k ∈ Finset.Icc 1 N, 0 ≤ β k * (1 - (Lf + Lh) * β k) / 2 / NonconvexAG.Smooth.Gamma α k := by
    intro k hk
    have hk1 := (Finset.mem_Icc.1 hk).1
    have := (h29 k hk).2
    have := hβ k hk1
    have := hΓpos k hk1
    have : 0 ≤ 1 - (Lf + Lh) * β k := by linarith
    positivity
  have hS : ∑ k ∈ Finset.Icc 1 N, β k * (1 - (Lf + Lh) * β k) / 2 / NonconvexAG.Smooth.Gamma α k
            * ‖gradMap P (xmd k) (gΨ (xmd k)) (β k)‖ ^ 2
        ≤ ‖x0 - xstar‖ ^ 2 / (2 * lam 1) + Lf / NonconvexAG.Smooth.Gamma α N * (‖xstar‖ ^ 2 + 2 * M ^ 2) := by
    rw [hD0] at T
    have e : (1 / (lam 1 * 1) * ‖x0 - xstar‖ ^ 2) / 2 = ‖x0 - xstar‖ ^ 2 / (2 * lam 1) := by
      have := hlam 1 le_rfl; field_simp
    have e2 : Lf * (‖xstar‖ ^ 2 + 2 * M ^ 2) / NonconvexAG.Smooth.Gamma α N
        = Lf / NonconvexAG.Smooth.Gamma α N * (‖xstar‖ ^ 2 + 2 * M ^ 2) := by ring
    have e3 : (1 / (lam 1 * 1) * ‖x0 - xstar‖ ^ 2
            - α N / (lam N * NonconvexAG.Smooth.Gamma α N) * ‖xstar - xk N‖ ^ 2) / 2
        = (1 / (lam 1 * 1) * ‖x0 - xstar‖ ^ 2) / 2
          - α N / (lam N * NonconvexAG.Smooth.Gamma α N) * ‖xstar - xk N‖ ^ 2 / 2 := by ring
    rw [e3, e, e2] at T
    linarith
  refine ⟨?_, ?_⟩
  · set m := (Finset.Icc 1 N).inf' (Finset.nonempty_Icc.mpr hN)
        (fun k => ‖gradMap P (xmd k) (gΨ (xmd k)) (β k)‖ ^ 2) with hm
    set W := ∑ k ∈ Finset.Icc 1 N, (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k * (1 - (Lf + Lh) * β k)
      with hW
    have hWpos : 0 < W := by
      apply Finset.sum_pos _ (Finset.nonempty_Icc.mpr hN)
      intro k hk
      have hk1 := (Finset.mem_Icc.1 hk).1
      have := (h29 k hk).2
      have := hβ k hk1
      have := hΓpos k hk1
      have : 0 < 1 - (Lf + Lh) * β k := by linarith
      positivity
    have hle : ∑ k ∈ Finset.Icc 1 N, β k * (1 - (Lf + Lh) * β k) / 2 / NonconvexAG.Smooth.Gamma α k * m
        ≤ ∑ k ∈ Finset.Icc 1 N, β k * (1 - (Lf + Lh) * β k) / 2 / NonconvexAG.Smooth.Gamma α k
            * ‖gradMap P (xmd k) (gΨ (xmd k)) (β k)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ hk) (hterm k hk)
    have hsum : ∑ k ∈ Finset.Icc 1 N, β k * (1 - (Lf + Lh) * β k) / 2 / NonconvexAG.Smooth.Gamma α k * m
        = W / 2 * m := by
      rw [← Finset.sum_mul, hW, Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hsum] at hle
    have key : W / 2 * m ≤ ‖x0 - xstar‖ ^ 2 / (2 * lam 1)
        + Lf / NonconvexAG.Smooth.Gamma α N * (‖xstar‖ ^ 2 + 2 * M ^ 2) := hle.trans hS
    have key' : m ≤ (‖x0 - xstar‖ ^ 2 / (2 * lam 1)
          + Lf / NonconvexAG.Smooth.Gamma α N * (‖xstar‖ ^ 2 + 2 * M ^ 2)) / (W / 2) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    calc m ≤ (‖x0 - xstar‖ ^ 2 / (2 * lam 1)
          + Lf / NonconvexAG.Smooth.Gamma α N * (‖xstar‖ ^ 2 + 2 * M ^ 2)) / (W / 2) := key'
      _ = _ := by field_simp
  · intro hLf0
    have hSnn : 0 ≤ ∑ k ∈ Finset.Icc 1 N, β k * (1 - (Lf + Lh) * β k) / 2 / NonconvexAG.Smooth.Gamma α k
            * ‖gradMap P (xmd k) (gΨ (xmd k)) (β k)‖ ^ 2 :=
      Finset.sum_nonneg (fun k hk => mul_nonneg (hterm k hk) (sq_nonneg _))
    rw [hD0] at T
    have e : (1 / (lam 1 * 1) * ‖x0 - xstar‖ ^ 2) / 2 = ‖x0 - xstar‖ ^ 2 / (2 * lam 1) := by
      have := hlam 1 le_rfl; field_simp
    have e3 : (1 / (lam 1 * 1) * ‖x0 - xstar‖ ^ 2
            - α N / (lam N * NonconvexAG.Smooth.Gamma α N) * ‖xstar - xk N‖ ^ 2) / 2
        = (1 / (lam 1 * 1) * ‖x0 - xstar‖ ^ 2) / 2
          - α N / (lam N * NonconvexAG.Smooth.Gamma α N) * ‖xstar - xk N‖ ^ 2 / 2 := by ring
    rw [e3, e] at T
    have hR : (f (xag N) + h (xag N) + X (xag N) - (f xstar + h xstar + X xstar))
        / NonconvexAG.Smooth.Gamma α N ≤ ‖x0 - xstar‖ ^ 2 / (2 * lam 1) := by
      have : Lf * (‖xstar‖ ^ 2 + 2 * M ^ 2) / NonconvexAG.Smooth.Gamma α N = 0 := by
        rw [hLf0]; simp
      linarith
    rw [div_le_iff₀ hΓN] at hR
    show f (xag N) + h (xag N) + X (xag N) - (f xstar + h xstar + X xstar)
      ≤ NonconvexAG.Smooth.Gamma α N * ‖x0 - xstar‖ ^ 2 / (2 * lam 1)
    rw [mul_div_assoc, mul_comm]
    exact hR

#print axioms solution
