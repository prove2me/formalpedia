-- Prove2me | solution 1 for GoldenRatioVI.Fixed.graal_converges
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T17:33:45.732031+00:00
-- url     : https://prove2.me/submissions/cdf3fb41-11e8-4e1c-8324-4516a48d06c4

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_GoldenRatioVI_Fixed_IsGRAALRun
open scoped goldenRatio
open Filter Topology InnerProductSpace

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


/-- Lower semicontinuity along a sequence with real upper bounds. -/
lemma lsc_bound {E : Type*} [TopologicalSpace E] (g : E → EReal) (hg : LowerSemicontinuous g)
    (a : ℕ → E) (zt : E) (ha : Tendsto a atTop (𝓝 zt)) (u : ℕ → ℝ) (l : ℝ)
    (hu : Tendsto u atTop (𝓝 l)) (hle : ∀ j, g (a j) ≤ (u j : EReal)) : g zt ≤ (l : EReal) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hly, hyg⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  have h1 : ∀ᶠ j in atTop, (y : EReal) < g (a j) := ha.eventually (hg zt y hyg)
  have hly' : l < y := EReal.coe_lt_coe_iff.1 hly
  have h2 : ∀ᶠ j in atTop, u j < y := hu.eventually (gt_mem_nhds hly')
  obtain ⟨j, hj1, hj2⟩ := (h1.and h2).exists
  have := lt_of_lt_of_le hj1 (hle j)
  rw [EReal.coe_lt_coe_iff] at this
  linarith

/-- The core convergence argument, assuming `z 1 ∈ dom g`. -/
theorem conv_core {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (F : E → E) (L lam : ℝ) (z zbar : ℕ → E)
    (hS : (solutionSet g F).Nonempty)
    (hg : IsProperConvexLSC g) (hF : IsMonotoneOperatorOn F (effDom g))
    (hL : 0 < L) (hLip : ∀ u ∈ effDom g, ∀ v ∈ effDom g, ‖F u - F v‖ ≤ L * ‖u - v‖)
    (hlam : 0 < lam) (hlamL : lam ≤ φ / (2 * L))
    (hrun : IsGRAALRun g F lam z zbar) (hz1 : z 1 ∈ effDom g) :
    ∃ zs ∈ solutionSet g F, Tendsto z atTop (𝓝 zs) ∧ Tendsto zbar atTop (𝓝 zs) := by
  have hφpos : (0 : ℝ) < φ := Real.goldenRatio_pos
  have hφ : (φ : ℝ) ≠ 0 := hφpos.ne'
  have hsq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
  obtain ⟨hbot, ⟨x0, hx0⟩, hconv, hlsc⟩ := hg
  have hg' : IsProperConvexLSC g := ⟨hbot, ⟨x0, hx0⟩, hconv, hlsc⟩
  obtain ⟨hbar, hprox⟩ := hrun
  have hrun' : IsGRAALRun g F lam z zbar := ⟨hbar, hprox⟩
  -- the function h = lam * g
  set h : E → EReal := fun x => (lam : EReal) * g x with hh
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
  have hdom : ∀ j, 1 ≤ j → z j ∈ effDom g := by
    intro j hj
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have : j = 1 := by omega
      subst this; exact hz1
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      exact hfin_g _ (prox_fin hx0' hbot' (hprox i (by omega)))
  -- real prox inequality: for x in dom, G(z_{m+1}) ≤ G(x) + ⟪...⟫ / lam
  have hproxR : ∀ m, 1 ≤ m → ∀ x, g x ≠ ⊤ →
      (g (z (m + 1))).toReal ≤ (g x).toReal +
        ⟪z (m + 1) - (zbar m - lam • F (z m)), x - z (m + 1)⟫_ℝ / lam := by
    intro m hm x hx
    have hd := hdom (m + 1) (by omega)
    have p := prox_real hconvR (hprox m hm) x (lam * (g (z (m + 1))).toReal)
      (lam * (g x).toReal) (hval _ _ (ereal_eq hd (hbot _))) (hval _ _ (ereal_eq hx (hbot _)))
    have key : (g (z (m + 1))).toReal - (g x).toReal ≤
        ⟪z (m + 1) - (zbar m - lam • F (z m)), x - z (m + 1)⟫_ℝ / lam := by
      rw [le_div_iff₀ hlam]; nlinarith
    linarith
  -- averaging identities
  have havg : ∀ k, 1 ≤ k → zbar k - zbar (k - 1) = (φ - 1) • (z k - zbar k) := by
    intro k hk
    have hb := hbar k hk
    have h1 : φ • zbar k = (φ - 1) • z k + zbar (k - 1) := by
      rw [hb, smul_smul, mul_inv_cancel₀ hφ, one_smul]
    have h2 : zbar (k - 1) = φ • zbar k - (φ - 1) • z k := by rw [h1]; abel
    rw [h2]; module
  -- Lyapunov function for a solution zs, indices shifted by 2
  obtain ⟨zs0, hzs0⟩ := hS
  set V : E → ℕ → ℝ := fun zs k =>
    (1 + φ) * ‖zbar (k + 2) - zs‖ ^ 2 + φ / 2 * ‖z (k + 2) - z (k + 1)‖ ^ 2 with hV
  have hVdesc : ∀ zs ∈ solutionSet g F, ∀ k,
      V zs (k + 1) + φ * ‖z (k + 2) - zbar (k + 2)‖ ^ 2 ≤ V zs k := by
    intro zs hzs k
    have he := energy_inequality g F L lam z zbar hg' hF hL hLip hlam hlamL hrun' hz1 zs hzs
      (k + 2) (by omega)
    simp only [hV]
    rw [show k + 2 - 1 = k + 1 by omega] at he
    rw [show k + 1 + 2 = k + 2 + 1 by ring, show k + 1 + 1 = k + 2 by ring]
    linarith
  have hV0 : ∀ zs k, 0 ≤ V zs k := fun zs k => by simp only [hV]; positivity
  have hVanti : ∀ zs ∈ solutionSet g F, Antitone (V zs) := by
    intro zs hzs
    apply antitone_nat_of_succ_le
    intro k
    have := hVdesc zs hzs k
    nlinarith [sq_nonneg ‖z (k + 2) - zbar (k + 2)‖]
  -- z - zbar → 0
  set D : ℕ → ℝ := fun k => ‖z (k + 2) - zbar (k + 2)‖ ^ 2 with hD
  have hDsum : Summable D := by
    apply summable_of_sum_range_le (c := V zs0 0 / φ) (fun k => sq_nonneg _)
    intro n
    rw [le_div_iff₀ hφpos]
    have htel : ∀ n, φ * ∑ i ∈ Finset.range n, D i ≤ V zs0 0 - V zs0 n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, mul_add]
        have := hVdesc zs0 hzs0 n
        simp only [hD]
        linarith
    have := htel n
    have := hV0 zs0 n
    linarith
  have hDlim : Tendsto D atTop (𝓝 0) := hDsum.tendsto_atTop_zero
  have hdiff : Tendsto (fun k => z (k + 2) - zbar (k + 2)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := hDlim.sqrt
    rw [Real.sqrt_zero] at this
    refine this.congr (fun k => ?_)
    simp only [hD]
    rw [Real.sqrt_sq (norm_nonneg _)]
  -- consecutive differences → 0
  have hstep : ∀ k, z (k + 3) - z (k + 2) = φ • (z (k + 3) - zbar (k + 3)) - (z (k + 2) - zbar (k + 2)) := by
    intro k
    have ha := havg (k + 3) (by omega)
    rw [show k + 3 - 1 = k + 2 by omega] at ha
    have e : z (k + 3) - z (k + 2) = (z (k + 3) - zbar (k + 3)) + (zbar (k + 3) - zbar (k + 2))
        - (z (k + 2) - zbar (k + 2)) := by abel
    rw [e, ha]; module
  have hconsec : Tendsto (fun k => z (k + 3) - z (k + 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => z (k + 3) - zbar (k + 3)) atTop (𝓝 0) := by
      have := hdiff.comp (tendsto_add_atTop_nat 1)
      refine this.congr (fun k => ?_)
      simp only [Function.comp]
    have := (h1.const_smul φ).sub hdiff
    rw [smul_zero, sub_zero] at this
    exact this.congr (fun k => (hstep k).symm)
  -- boundedness of zbar
  have hbd : ∀ k, zbar (k + 2) ∈ Metric.closedBall zs0 (Real.sqrt (V zs0 0 / (1 + φ))) := by
    intro k
    rw [Metric.mem_closedBall, dist_eq_norm]
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ (by positivity)]
    have h1 := (hVanti zs0 hzs0) (Nat.zero_le k)
    simp only [hV] at h1 ⊢
    nlinarith [sq_nonneg ‖z (k + 2) - z (k + 1)‖]
  obtain ⟨zt, _, ss, hss, hsslim⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hbd
  -- the corresponding subsequences
  have hsstop : Tendsto ss atTop atTop := hss.tendsto_atTop
  have hzb : Tendsto (fun j => zbar (ss j + 2)) atTop (𝓝 zt) := hsslim
  have hz2 : Tendsto (fun j => z (ss j + 2)) atTop (𝓝 zt) := by
    have := (hdiff.comp hsstop).add hzb
    rw [zero_add] at this
    refine this.congr (fun j => ?_)
    simp only [Function.comp]; abel
  have hz3 : Tendsto (fun j => z (ss j + 3)) atTop (𝓝 zt) := by
    have := (hconsec.comp hsstop).add hz2
    rw [zero_add] at this
    refine this.congr (fun j => ?_)
    simp only [Function.comp]; abel
  have hz1' : Tendsto (fun j => z (ss j + 1)) atTop (𝓝 zt) := by
    -- z (k+2) - z (k+1): use the shifted consecutive differences for k ≥ 1
    have hc2 : Tendsto (fun k => z (k + 2) - z (k + 1)) atTop (𝓝 0) := by
      have hV' : ∀ k, φ / 2 * ‖z (k + 2) - z (k + 1)‖ ^ 2 ≤ V zs0 k := by
        intro k; simp only [hV]; nlinarith [sq_nonneg ‖zbar (k + 2) - zs0‖]
      have hc : Tendsto (fun k => z ((k + 1) + 2) - z ((k + 1) + 1)) atTop (𝓝 0) := by
        refine hconsec.congr (fun k => ?_)
        rw [show k + 1 + 2 = k + 3 by ring, show k + 1 + 1 = k + 2 by ring]
      exact (tendsto_add_atTop_iff_nat 1).1 hc
    have := (hc2.comp hsstop).neg.add hz2
    rw [neg_zero, zero_add] at this
    refine this.congr (fun j => ?_)
    simp only [Function.comp]; abel
  -- zt is in the domain and is a solution
  have hdom0 := hzs0.1
  have hFz : ∀ j, ‖F (z (ss j + 2)) - F zs0‖ ≤ L * ‖z (ss j + 2) - zs0‖ :=
    fun j => hLip _ (hdom _ (by omega)) _ hdom0
  have hub : ∀ x, g x ≠ ⊤ → ∀ j, g (z (ss j + 3)) ≤
      (((g x).toReal + ⟪z (ss j + 3) - (zbar (ss j + 2) - lam • F (z (ss j + 2))),
        x - z (ss j + 3)⟫_ℝ / lam : ℝ) : EReal) := by
    intro x hx j
    have := hproxR (ss j + 2) (by omega) x hx
    have hd := hdom (ss j + 2 + 1) (by omega)
    rw [ereal_eq hd (hbot _), EReal.coe_le_coe_iff]
    exact this
  -- step A: zt ∈ dom g, using bounded F-values
  have hztdom : g zt ≠ ⊤ := by
    have hFb : Tendsto (fun j => F (z (ss j + 2)) - F zs0) atTop (𝓝 0) ∨ True := Or.inr trivial
    -- use x = zs0; bound the inner products
    set R := Real.sqrt (V zs0 0 / (1 + φ)) with hR
    have hbzb : ∀ j, ‖zbar (ss j + 2) - zs0‖ ≤ R := by
      intro j; have := hbd (ss j); rwa [Metric.mem_closedBall, dist_eq_norm] at this
    -- the sequence of upper bounds converges along a further subsequence? Instead use limsup:
    -- we bound it by a convergent sequence after showing F-values are bounded.
    have hbound : ∃ B : ℝ, ∀ j, (g (zs0)).toReal + ⟪z (ss j + 3) - (zbar (ss j + 2) - lam • F (z (ss j + 2))),
        zs0 - z (ss j + 3)⟫_ℝ / lam ≤ B := by
      -- all vectors involved are bounded
      have hconv1 := hz3.norm
      have hconv2 := hz2.norm
      have hconvb := hzb.norm
      obtain ⟨M3, hM3⟩ := hconv1.bddAbove_range
      obtain ⟨M2, hM2⟩ := hconv2.bddAbove_range
      obtain ⟨Mb, hMb⟩ := hconvb.bddAbove_range
      refine ⟨(g zs0).toReal + (M3 + Mb + lam * (L * (M2 + ‖zs0‖) + ‖F zs0‖)) * (‖zs0‖ + M3) / lam,
        fun j => ?_⟩
      have a3 : ‖z (ss j + 3)‖ ≤ M3 := hM3 ⟨j, rfl⟩
      have a2 : ‖z (ss j + 2)‖ ≤ M2 := hM2 ⟨j, rfl⟩
      have ab : ‖zbar (ss j + 2)‖ ≤ Mb := hMb ⟨j, rfl⟩
      have hFn : ‖F (z (ss j + 2))‖ ≤ L * (M2 + ‖zs0‖) + ‖F zs0‖ := by
        have := hFz j
        have t1 : ‖z (ss j + 2) - zs0‖ ≤ M2 + ‖zs0‖ := (norm_sub_le _ _).trans (by linarith)
        have t2 : ‖F (z (ss j + 2))‖ ≤ ‖F (z (ss j + 2)) - F zs0‖ + ‖F zs0‖ := by
          have := norm_add_le (F (z (ss j + 2)) - F zs0) (F zs0); rwa [sub_add_cancel] at this
        nlinarith
      have hv1 : ‖z (ss j + 3) - (zbar (ss j + 2) - lam • F (z (ss j + 2)))‖ ≤
          M3 + Mb + lam * (L * (M2 + ‖zs0‖) + ‖F zs0‖) := by
        calc ‖z (ss j + 3) - (zbar (ss j + 2) - lam • F (z (ss j + 2)))‖
            ≤ ‖z (ss j + 3)‖ + ‖zbar (ss j + 2) - lam • F (z (ss j + 2))‖ := norm_sub_le _ _
          _ ≤ ‖z (ss j + 3)‖ + (‖zbar (ss j + 2)‖ + ‖lam • F (z (ss j + 2))‖) :=
              add_le_add le_rfl (norm_sub_le _ _)
          _ ≤ M3 + (Mb + lam * (L * (M2 + ‖zs0‖) + ‖F zs0‖)) := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
              have := mul_le_mul_of_nonneg_left hFn hlam.le
              linarith
          _ = M3 + Mb + lam * (L * (M2 + ‖zs0‖) + ‖F zs0‖) := by ring
      have hv2 : ‖zs0 - z (ss j + 3)‖ ≤ ‖zs0‖ + M3 := (norm_sub_le _ _).trans (by linarith)
      have hcs := real_inner_le_norm (z (ss j + 3) - (zbar (ss j + 2) - lam • F (z (ss j + 2))))
        (zs0 - z (ss j + 3))
      have hprod := mul_le_mul hv1 hv2 (norm_nonneg _) (by
        have e1 : 0 ≤ M3 := le_trans (norm_nonneg _) a3
        have e2 : 0 ≤ Mb := le_trans (norm_nonneg _) ab
        have e3 : 0 ≤ L * (M2 + ‖zs0‖) + ‖F zs0‖ := le_trans (norm_nonneg _) hFn
        have e4 := mul_nonneg hlam.le e3
        linarith)
      have := div_le_div_of_nonneg_right (hcs.trans hprod) hlam.le
      linarith
    obtain ⟨B, hB⟩ := hbound
    have hle : ∀ j, g (z (ss j + 3)) ≤ (B : EReal) := by
      intro j
      exact (hub zs0 hdom0 j).trans (EReal.coe_le_coe_iff.2 (hB j))
    have := lsc_bound g hlsc _ zt hz3 (fun _ => B) B tendsto_const_nhds hle
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) this
  have hFlim : Tendsto (fun j => F (z (ss j + 2))) atTop (𝓝 (F zt)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 : Tendsto (fun j => L * ‖z (ss j + 2) - zt‖) atTop (𝓝 (L * 0)) :=
      (tendsto_iff_norm_sub_tendsto_zero.1 hz2).const_mul L
    rw [mul_zero] at h1
    exact squeeze_zero (fun j => norm_nonneg _)
      (fun j => hLip _ (hdom _ (by omega)) _ hztdom) h1
  have hzt_sol : zt ∈ solutionSet g F := by
    refine ⟨hztdom, fun x => ?_⟩
    by_cases hx : g x = ⊤
    · rw [hx, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _), ereal_eq hztdom (hbot zt),
        EReal.top_sub_coe]
      exact le_top
    · have hlim : Tendsto (fun j => (g x).toReal +
          ⟪z (ss j + 3) - (zbar (ss j + 2) - lam • F (z (ss j + 2))), x - z (ss j + 3)⟫_ℝ / lam)
          atTop (𝓝 ((g x).toReal + ⟪zt - (zt - lam • F zt), x - zt⟫_ℝ / lam)) := by
        apply tendsto_const_nhds.add
        apply Tendsto.div_const
        apply Tendsto.inner
        · exact hz3.sub (hzb.sub (hFlim.const_smul lam))
        · exact tendsto_const_nhds.sub hz3
      have hb := lsc_bound g hlsc _ zt hz3 _ _ hlim (hub x hx)
      have e : ⟪zt - (zt - lam • F zt), x - zt⟫_ℝ / lam = ⟪F zt, x - zt⟫_ℝ := by
        rw [sub_sub_cancel, real_inner_smul_left]; field_simp
      rw [e] at hb
      rw [ereal_eq hx (hbot x), ereal_eq hztdom (hbot zt)]
      rw [ereal_eq hztdom (hbot zt), EReal.coe_le_coe_iff] at hb
      rw [← EReal.coe_add, ← EReal.coe_sub, EReal.coe_nonneg]
      linarith
  -- convergence of the Lyapunov function for zt
  have hVt := hVanti zt hzt_sol
  have hVsub : Tendsto (fun j => V zt (ss j)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => ‖zbar (ss j + 2) - zt‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hzb
    have h2 : Tendsto (fun j => ‖z (ss j + 2) - z (ss j + 1)‖) atTop (𝓝 0) := by
      have := (hz2.sub hz1')
      rw [sub_self] at this
      exact tendsto_zero_iff_norm_tendsto_zero.1 this
    have := ((h1.pow 2).const_mul (1 + φ)).add ((h2.pow 2).const_mul (φ / 2))
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at this
    exact this
  have hVlim : Tendsto (V zt) atTop (𝓝 0) := by
    have hinf := tendsto_atTop_ciInf hVt ⟨0, by rintro _ ⟨k, rfl⟩; exact hV0 zt k⟩
    have h2 := hinf.comp hsstop
    have := tendsto_nhds_unique h2 hVsub
    rw [this] at hinf
    exact hinf
  -- conclude
  have hzbar2 : Tendsto (fun k => zbar (k + 2)) atTop (𝓝 zt) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ k, ‖zbar (k + 2) - zt‖ ≤ Real.sqrt (V zt k / (1 + φ)) := by
      intro k
      apply Real.le_sqrt_of_sq_le
      rw [le_div_iff₀ (by positivity)]
      simp only [hV]
      nlinarith [sq_nonneg ‖z (k + 2) - z (k + 1)‖]
    have hs : Tendsto (fun k => Real.sqrt (V zt k / (1 + φ))) atTop (𝓝 0) := by
      have := (hVlim.div_const (1 + φ)).sqrt
      rwa [zero_div, Real.sqrt_zero] at this
    exact squeeze_zero (fun k => norm_nonneg _) hb hs
  have hz2' : Tendsto (fun k => z (k + 2)) atTop (𝓝 zt) := by
    have := hdiff.add hzbar2
    rw [zero_add] at this
    refine this.congr (fun k => ?_)
    abel
  refine ⟨zt, hzt_sol, (tendsto_add_atTop_iff_nat 2).1 hz2', (tendsto_add_atTop_iff_nat 2).1 hzbar2⟩

theorem graal_converges {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (F : E → E) (L lam : ℝ) (z zbar : ℕ → E)
    (hS : (solutionSet g F).Nonempty)
    (hg : IsProperConvexLSC g) (hF : IsMonotoneOperatorOn F (effDom g))
    (hL : 0 < L) (hLip : ∀ u ∈ effDom g, ∀ v ∈ effDom g, ‖F u - F v‖ ≤ L * ‖u - v‖)
    (hlam : 0 < lam) (hlamL : lam ≤ φ / (2 * L))
    (hrun : IsGRAALRun g F lam z zbar) :
    ∃ zs ∈ solutionSet g F,
      Filter.Tendsto z Filter.atTop (nhds zs) ∧
        Filter.Tendsto zbar Filter.atTop (nhds zs) := by
  obtain ⟨hbar, hprox⟩ := hrun
  -- shift the run by one step so that the new `z 1` is a prox output
  set z' : ℕ → E := fun k => z (k + 1) with hz'
  set zb' : ℕ → E := fun k => zbar (k + 1) with hzb'
  have hrun' : IsGRAALRun g F lam z' zb' := by
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · have := hbar (k + 1) (by omega)
      simp only [hz', hzb']
      rw [show k - 1 + 1 = k + 1 - 1 by omega]
      exact this
    · exact hprox (k + 1) (by omega)
  obtain ⟨hbot, ⟨x0, hx0⟩, hconv, hlsc⟩ := hg
  have hdom1 : z' 1 ∈ effDom g := by
    -- z 2 is a prox output of lam * g, hence finite
    have hp := hprox 1 le_rfl
    set h : E → EReal := fun x => (lam : EReal) * g x with hh
    have hbot' : ∀ x, h x ≠ ⊥ := by
      intro x
      by_cases hx : g x = ⊤
      · simp only [hh, hx, EReal.coe_mul_top_of_pos hlam]; exact top_ne_bot
      · rw [show h x = ((lam * (g x).toReal : ℝ) : EReal) by
          simp only [hh]; rw [EReal.coe_mul, ← ereal_eq hx (hbot x)]]
        exact EReal.coe_ne_bot _
    have hx0' : h x0 ≠ ⊤ := by
      rw [show h x0 = ((lam * (g x0).toReal : ℝ) : EReal) by
        simp only [hh]; rw [EReal.coe_mul, ← ereal_eq hx0 (hbot x0)]]
      exact EReal.coe_ne_top _
    have hfin := prox_fin hx0' hbot' hp
    intro hgx
    apply hfin
    simp only [hh]
    show (lam : EReal) * g (z (1 + 1)) = ⊤
    rw [show (1 + 1 : ℕ) = 2 from rfl]
    have : z' 1 = z 2 := rfl
    rw [← this, hgx, EReal.coe_mul_top_of_pos hlam]
  obtain ⟨zs, hzs, h1, h2⟩ := conv_core g F L lam z' zb' hS ⟨hbot, ⟨x0, hx0⟩, hconv, hlsc⟩ hF hL
    hLip hlam hlamL hrun' hdom1
  exact ⟨zs, hzs, (tendsto_add_atTop_iff_nat 1).1 h1, (tendsto_add_atTop_iff_nat 1).1 h2⟩

end GoldenRatioVI.Fixed

open GoldenRatioVI.Fixed

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (F : E → E) (L lam : ℝ) (z zbar : ℕ → E)
    (hS : (solutionSet g F).Nonempty)
    (hg : IsProperConvexLSC g) (hF : IsMonotoneOperatorOn F (effDom g))
    (hL : 0 < L) (hLip : ∀ u ∈ effDom g, ∀ v ∈ effDom g, ‖F u - F v‖ ≤ L * ‖u - v‖)
    (hlam : 0 < lam) (hlamL : lam ≤ φ / (2 * L))
    (hrun : IsGRAALRun g F lam z zbar) :
    ∃ zs ∈ solutionSet g F,
      Filter.Tendsto z Filter.atTop (nhds zs) ∧
        Filter.Tendsto zbar Filter.atTop (nhds zs) := by
  exact graal_converges g F L lam z zbar hS hg hF hL hLip hlam hlamL hrun
