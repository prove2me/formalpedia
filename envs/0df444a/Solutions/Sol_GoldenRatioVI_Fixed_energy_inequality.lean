-- Prove2me | solution 1 for GoldenRatioVI.Fixed.energy_inequality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T16:29:27.164821+00:00
-- url     : https://prove2.me/submissions/06668ab2-3496-492e-b6d2-f340582bdefc

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_GoldenRatioVI_Fixed_IsGRAALRun
open scoped goldenRatio
open Filter Topology

namespace GoldenRatioVI.Fixed

lemma ereal_eq {e : EReal} (h1 : e ≠ ⊤) (h2 : e ≠ ⊥) : e = ((e.toReal : ℝ) : EReal) :=
  (EReal.coe_toReal h1 h2).symm

lemma real_limit_le' {A B C : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → A ≤ B + t * C) : A ≤ B := by
  have ht : Tendsto (fun t : ℝ => B + t * C) (𝓝[>] 0) (𝓝 (B + 0 * C)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
  rw [zero_mul, add_zero] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t htt
  exact h t htt.1 htt.2.le

/-- Prox points of a function with finite values `h x0` are finite. -/
lemma prox_fin {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {h : E → EReal}
    {x0 : E} (hx0 : h x0 ≠ ⊤) (hbot : ∀ x, h x ≠ ⊥) {z xbar : E}
    (hp : GoldenRatioVI.Shared.IsProxPoint h z xbar) : h xbar ≠ ⊤ := by
  intro htop
  have h1 := hp x0
  rw [htop, EReal.top_add_coe, ereal_eq hx0 (hbot x0), ← EReal.coe_add] at h1
  exact absurd h1 (not_le.2 (EReal.coe_lt_top _))

/-- Real form of the prox inequality (one direction), under a real convexity hypothesis. -/
lemma prox_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {h : E → EReal}
    (hconvR : ∀ x y : E, ∀ a b t : ℝ, h x = a → h y = b → 0 ≤ t → t ≤ 1 →
      h ((1 - t) • x + t • y) ≤ (((1 - t) * a + t * b : ℝ) : EReal))
    {z xbar : E} (hp : GoldenRatioVI.Shared.IsProxPoint h z xbar)
    (x : E) (a b : ℝ) (ha : h xbar = a) (hb : h x = b) :
    a - b ≤ inner ℝ (xbar - z) (x - xbar) := by
  apply real_limit_le' (C := ‖x - xbar‖ ^ 2 / 2)
  intro t ht0 ht1
  set xt := (1 - t) • xbar + t • x with hxt
  have hc := hconvR xbar x a b t ha hb ht0.le ht1
  have hq := hp xt
  rw [ha] at hq
  have hp2 : ((a + ‖xbar - z‖ ^ 2 / 2 : ℝ) : EReal) ≤
      (((1 - t) * a + t * b + ‖xt - z‖ ^ 2 / 2 : ℝ) : EReal) := by
    rw [EReal.coe_add, EReal.coe_add]
    exact hq.trans (add_le_add hc le_rfl)
  rw [EReal.coe_le_coe_iff] at hp2
  have hexp : xt - z = (xbar - z) + t • (x - xbar) := by rw [hxt]; module
  rw [hexp, norm_add_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs,
    abs_of_pos ht0] at hp2
  have key : t * (a - b) ≤ t * (inner ℝ (xbar - z) (x - xbar) + t * (‖x - xbar‖ ^ 2 / 2)) := by
    nlinarith
  exact le_of_mul_le_mul_left key ht0

lemma polar {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a b c : E) :
    2 * inner ℝ (a - b) (c - a) = ‖b - c‖ ^ 2 - ‖a - b‖ ^ 2 - ‖a - c‖ ^ 2 := by
  rw [show b - c = (b - a) + (a - c) by abel, norm_add_sq_real,
    show a - b = -(b - a) by abel, show c - a = -(a - c) by abel, inner_neg_left,
    inner_neg_right, norm_neg]
  ring

lemma affine_id {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u v : E) (c : ℝ) :
    ‖(1 + c) • u - c • v‖ ^ 2 = (1 + c) * ‖u‖ ^ 2 - c * ‖v‖ ^ 2 + c * (1 + c) * ‖u - v‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  ring

lemma final_alg (ph lam X Yb2 Yb1 W V U D1 D0 I1 I2 a0 a1 a2 a3 c G1 G2 Gs : ℝ)
    (hid : X = (1 + ph) * Yb2 - ph * Yb1 + ph * (1 + ph) * W)
    (P1 : 2 * I1 = Yb1 - V - X)
    (hI2 : ph * I2 = ph / 2 * (V - U - D1))
    (hV : (ph - 1) * V = ph * (1 + ph) * W)
    (pa : lam * G2 - lam * Gs ≤ I1 + lam * a1)
    (pb : lam * G1 - lam * G2 ≤ ph * I2 + lam * a0)
    (hgrad : lam * a1 + lam * a0 = lam * a2 + lam * c)
    (hneg : a2 = -a3)
    (hF1 : lam * (Gs - G1) ≤ lam * a3)
    (hcross : lam * c ≤ ph / 4 * (D0 + D1)) :
    (1 + ph) * Yb2 + ph / 2 * D1 ≤ (1 + ph) * Yb1 + ph / 2 * D0 - ph * U := by
  subst hneg
  linarith

set_option maxHeartbeats 1000000 in
theorem energy_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (F : E → E) (L lam : ℝ) (z zbar : ℕ → E)
    (hg : IsProperConvexLSC g) (hF : IsMonotoneOperatorOn F (effDom g))
    (hL : 0 < L) (hLip : ∀ u ∈ effDom g, ∀ v ∈ effDom g, ‖F u - F v‖ ≤ L * ‖u - v‖)
    (hlam : 0 < lam) (hlamL : lam ≤ φ / (2 * L))
    (hrun : IsGRAALRun g F lam z zbar) (hz1 : z 1 ∈ effDom g)
    (zs : E) (hzs : zs ∈ solutionSet g F) (k : ℕ) (hk : 2 ≤ k) :
    (1 + φ) * ‖zbar (k + 1) - zs‖ ^ 2 + φ / 2 * ‖z (k + 1) - z k‖ ^ 2 ≤
      (1 + φ) * ‖zbar k - zs‖ ^ 2 + φ / 2 * ‖z k - z (k - 1)‖ ^ 2
        - φ * ‖z k - zbar k‖ ^ 2 := by
  obtain ⟨hbot, ⟨x0, hx0⟩, hconv, _⟩ := hg
  obtain ⟨hbar, hprox⟩ := hrun
  have hφ : (φ : ℝ) ≠ 0 := Real.goldenRatio_ne_zero
  have hφpos : (0 : ℝ) < φ := Real.goldenRatio_pos
  have hsq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
  set h : E → EReal := fun x => (lam : EReal) * g x with hh
  -- values of h
  have hval : ∀ x (G : ℝ), g x = G → h x = ((lam * G : ℝ) : EReal) := by
    intro x G hG; simp only [hh, hG, EReal.coe_mul]
  have hbot' : ∀ x, h x ≠ ⊥ := by
    intro x
    by_cases hx : g x = ⊤
    · simp only [hh, hx, EReal.coe_mul_top_of_pos hlam]; exact top_ne_bot
    · rw [hval x _ (ereal_eq hx (hbot x))]; exact EReal.coe_ne_bot _
  have hfin_g : ∀ x, h x ≠ ⊤ → g x ≠ ⊤ := by
    intro x hx hgx
    apply hx; simp only [hh, hgx, EReal.coe_mul_top_of_pos hlam]
  have hgval : ∀ x (a : ℝ), h x = a → g x = ((a / lam : ℝ) : EReal) := by
    intro x a ha
    have h1 : g x ≠ ⊤ := hfin_g x (by rw [ha]; exact EReal.coe_ne_top _)
    have h2 := ereal_eq h1 (hbot x)
    rw [hval x _ h2, EReal.coe_eq_coe_iff] at ha
    rw [h2, EReal.coe_eq_coe_iff, ← ha]; field_simp
  have hconvR : ∀ x y : E, ∀ a b t : ℝ, h x = a → h y = b → 0 ≤ t → t ≤ 1 →
      h ((1 - t) • x + t • y) ≤ (((1 - t) * a + t * b : ℝ) : EReal) := by
    intro x y a b t ha hb ht0 ht1
    have gx := hgval x a ha
    have gy := hgval y b hb
    have hm1 : (x, a / lam) ∈ {p : E × ℝ | g p.1 ≤ (p.2 : EReal)} := by
      simp only [Set.mem_ofPred_eq]; rw [gx]
    have hm2 : (y, b / lam) ∈ {p : E × ℝ | g p.1 ≤ (p.2 : EReal)} := by
      simp only [Set.mem_ofPred_eq]; rw [gy]
    have hc := hconv hm1 hm2 (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
      smul_eq_mul] at hc
    have hne : g ((1 - t) • x + t • y) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hc
    have he := ereal_eq hne (hbot _)
    rw [hval _ _ he, EReal.coe_le_coe_iff]
    rw [he, EReal.coe_le_coe_iff] at hc
    have := mul_le_mul_of_nonneg_left hc hlam.le
    have e : lam * ((1 - t) * (a / lam) + t * (b / lam)) = (1 - t) * a + t * b := by
      field_simp
    linarith
  have hx0' : h x0 ≠ ⊤ := by
    rw [hval x0 _ (ereal_eq hx0 (hbot x0))]; exact EReal.coe_ne_top _
  -- finiteness of iterates
  have hdom : ∀ j, 1 ≤ j → z j ∈ effDom g := by
    intro j hj
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have : j = 1 := by omega
      subst this; exact hz1
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      exact hfin_g _ (prox_fin hx0' hbot' (hprox i (by omega)))
  have hsol := hzs
  obtain ⟨hzsdom, hsolv⟩ := hsol
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have d0 : z m ∈ effDom g := hdom m (by omega)
  have d1 : z (m + 1) ∈ effDom g := hdom (m + 1) (by omega)
  have d2 : z (m + 1 + 1) ∈ effDom g := hdom (m + 1 + 1) (by omega)
  -- real values
  set G1 := (g (z (m + 1))).toReal
  set G2 := (g (z (m + 1 + 1))).toReal
  set Gs := (g zs).toReal
  have eg1 : g (z (m + 1)) = G1 := ereal_eq d1 (hbot _)
  have eg2 : g (z (m + 1 + 1)) = G2 := ereal_eq d2 (hbot _)
  have egs : g zs = Gs := ereal_eq hzsdom (hbot _)
  -- prox inequalities
  have pa := prox_real hconvR (hprox (m + 1) (by omega)) zs (lam * G2) (lam * Gs)
    (hval _ _ eg2) (hval _ _ egs)
  have pb := prox_real hconvR (hprox m (by omega)) (z (m + 1 + 1)) (lam * G1) (lam * G2)
    (hval _ _ eg1) (hval _ _ eg2)
  -- solution + monotonicity
  have hs1 := hsolv (z (m + 1))
  rw [eg1, egs, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_nonneg] at hs1
  have hmono := hF _ d1 _ hzsdom
  have hlip := hLip _ d1 _ d0
  -- averaging: z1 - zb0 = φ (z1 - zb1)
  have hav : z (m + 1) - zbar m = φ • (z (m + 1) - zbar (m + 1)) := by
    have hb1 := hbar (m + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hb1
    have h1 : φ • zbar (m + 1) = (φ - 1) • z (m + 1) + zbar m := by
      rw [hb1, smul_smul, mul_inv_cancel₀ hφ, one_smul]
    rw [smul_sub, h1]; module
  -- the norm identity for z (m+2)
  have hz2 : z (m + 1 + 1) = (1 + φ) • zbar (m + 1 + 1) - φ • zbar (m + 1) := by
    have h := hbar (m + 1 + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h
    have h1 : φ • zbar (m + 1 + 1) = (φ - 1) • z (m + 1 + 1) + zbar (m + 1) := by
      rw [h, smul_smul, mul_inv_cancel₀ hφ, one_smul]
    have h2 : z (m + 1 + 1) = φ • ((φ - 1) • z (m + 1 + 1)) := by
      rw [smul_smul, show φ * (φ - 1) = 1 by nlinarith, one_smul]
    rw [h2, show (φ - 1) • z (m + 1 + 1) = φ • zbar (m + 1 + 1) - zbar (m + 1) by
      rw [h1]; abel, smul_sub, smul_smul, show φ * φ = 1 + φ by nlinarith]
  set z0 := z m
  set z1 := z (m + 1)
  set z2 := z (m + 1 + 1)
  set zb0 := zbar m
  set zb1 := zbar (m + 1)
  set zb2 := zbar (m + 1 + 1)
  -- norm identity: ‖z2 - zs‖² = (1+φ)‖zb2 - zs‖² - φ‖zb1 - zs‖² + (φ - 1)‖z2 - zb1‖²
  have hid : ‖z2 - zs‖ ^ 2 = (1 + φ) * ‖zb2 - zs‖ ^ 2 - φ * ‖zb1 - zs‖ ^ 2
      + φ * (1 + φ) * ‖zb2 - zb1‖ ^ 2 := by
    have e1 : z2 - zs = (1 + φ) • (zb2 - zs) - φ • (zb1 - zs) := by rw [hz2]; module
    have e2 : zb2 - zb1 = (zb2 - zs) - (zb1 - zs) := by abel
    rw [e1, e2]; exact affine_id _ _ _
  have hid2 : ‖z2 - zb1‖ ^ 2 = (1 + φ) ^ 2 * ‖zb2 - zb1‖ ^ 2 := by
    have e3 : z2 - zb1 = (1 + φ) • (zb2 - zb1) := by rw [hz2]; module
    rw [e3, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  -- polarization identities
  have P1 := polar z2 zb1 zs
  have P2 := polar z1 zb1 z2
  -- rewrite prox inequalities
  have pa' : lam * G2 - lam * Gs ≤ inner ℝ (z2 - zb1) (zs - z2)
      + lam * inner ℝ (F z1) (zs - z2) := by
    have : z2 - (zb1 - lam • F z1) = (z2 - zb1) + lam • F z1 := by abel
    rw [this, inner_add_left, real_inner_smul_left] at pa; exact pa
  have pb' : lam * G1 - lam * G2 ≤ φ * inner ℝ (z1 - zb1) (z2 - z1)
      + lam * inner ℝ (F z0) (z2 - z1) := by
    have : z1 - (zb0 - lam • F z0) = (z1 - zb0) + lam • F z0 := by abel
    rw [this, inner_add_left, real_inner_smul_left, hav, real_inner_smul_left] at pb; exact pb
  -- monotonicity + solution: ⟪F z1, z1 - zs⟫ ≥ Gs - G1
  have hF1 : Gs - G1 ≤ inner ℝ (F z1) (z1 - zs) := by
    rw [inner_sub_left] at hmono; linarith
  -- combine the gradient terms
  have hgrad : lam * inner ℝ (F z1) (zs - z2) + lam * inner ℝ (F z0) (z2 - z1) =
      lam * inner ℝ (F z1) (zs - z1) + lam * inner ℝ (F z1 - F z0) (z1 - z2) := by
    have e1 : zs - z2 = (zs - z1) + (z1 - z2) := by abel
    have e2 : z2 - z1 = -(z1 - z2) := by abel
    rw [e1, e2, inner_add_right, inner_neg_right, inner_sub_left]; ring
  have hneg : inner ℝ (F z1) (zs - z1) = - inner ℝ (F z1) (z1 - zs) := by
    rw [← inner_neg_right, neg_sub]
  -- Lipschitz bound on the cross term
  have hcs : inner ℝ (F z1 - F z0) (z1 - z2) ≤ ‖F z1 - F z0‖ * ‖z1 - z2‖ :=
    real_inner_le_norm _ _
  have hlamL' : lam * L ≤ φ / 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * L)] at hlamL; linarith
  have hcross : lam * inner ℝ (F z1 - F z0) (z1 - z2) ≤
      φ / 4 * (‖z1 - z0‖ ^ 2 + ‖z2 - z1‖ ^ 2) := by
    have n1 : ‖z1 - z2‖ = ‖z2 - z1‖ := norm_sub_rev _ _
    have hA : 0 ≤ ‖z1 - z0‖ := norm_nonneg _
    have hB : 0 ≤ ‖z2 - z1‖ := norm_nonneg _
    have step1 : lam * inner ℝ (F z1 - F z0) (z1 - z2) ≤ lam * (L * ‖z1 - z0‖) * ‖z2 - z1‖ := by
      rw [← n1]
      have := mul_le_mul_of_nonneg_right hlip (norm_nonneg (z1 - z2))
      nlinarith
    have step2 : lam * (L * ‖z1 - z0‖) * ‖z2 - z1‖ ≤ φ / 2 * (‖z1 - z0‖ * ‖z2 - z1‖) := by
      have := mul_le_mul_of_nonneg_right hlamL' (mul_nonneg hA hB)
      nlinarith
    nlinarith [sq_nonneg (‖z1 - z0‖ - ‖z2 - z1‖)]
  -- final assembly
  have n21 : ‖z2 - zb1‖ ^ 2 = ‖zb1 - z2‖ ^ 2 := by rw [norm_sub_rev]
  have n12 : ‖z1 - z2‖ ^ 2 = ‖z2 - z1‖ ^ 2 := by rw [norm_sub_rev]
  rw [← n21, n12] at P2
  have hI2 : φ * inner ℝ (z1 - zb1) (z2 - z1) =
      φ / 2 * (‖z2 - zb1‖ ^ 2 - ‖z1 - zb1‖ ^ 2 - ‖z2 - z1‖ ^ 2) := by
    rw [← P2]; ring
  have hV : (φ - 1) * ‖z2 - zb1‖ ^ 2 = φ * (1 + φ) * ‖zb2 - zb1‖ ^ 2 := by
    rw [hid2]; linear_combination (1 + φ) * ‖zb2 - zb1‖ ^ 2 * hsq
  have hF1' := mul_le_mul_of_nonneg_left hF1 hlam.le
  exact final_alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hid P1 hI2 hV pa' pb' hgrad hneg hF1' hcross

end GoldenRatioVI.Fixed

open GoldenRatioVI.Fixed

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (F : E → E) (L lam : ℝ) (z zbar : ℕ → E)
    (hg : IsProperConvexLSC g) (hF : IsMonotoneOperatorOn F (effDom g))
    (hL : 0 < L) (hLip : ∀ u ∈ effDom g, ∀ v ∈ effDom g, ‖F u - F v‖ ≤ L * ‖u - v‖)
    (hlam : 0 < lam) (hlamL : lam ≤ φ / (2 * L))
    (hrun : IsGRAALRun g F lam z zbar) (hz1 : z 1 ∈ effDom g)
    (zs : E) (hzs : zs ∈ solutionSet g F) (k : ℕ) (hk : 2 ≤ k) :
    (1 + φ) * ‖zbar (k + 1) - zs‖ ^ 2 + φ / 2 * ‖z (k + 1) - z k‖ ^ 2 ≤
      (1 + φ) * ‖zbar k - zs‖ ^ 2 + φ / 2 * ‖z k - z (k - 1)‖ ^ 2
        - φ * ‖z k - zbar k‖ ^ 2 := by
  exact energy_inequality g F L lam z zbar hg hF hL hLip hlam hlamL hrun hz1 zs hzs k hk
