-- Prove2me | solution 1 for NAPPAL.Subreg.lemma_6_1_uniform
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T20:24:01.571288+00:00
-- url     : https://prove2.me/submissions/bef7c6dc-d962-47f0-a598-8147526651a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NAPPAL_Subreg_Setting
import Theorems.Thm_NAPPAL_Rate_theorem_4_1
open scoped InnerProductSpace

lemma nap_taylor_core {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : X → ℝ)
    (ℓ : X →L[ℝ] ℝ) (x y : X) (M : ℝ) (hf : Differentiable ℝ f)
    (hM : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ f z - ℓ‖ ≤ M) :
    |f y - f x - ℓ (y - x)| ≤ M * ‖y - x‖ := by
  have hg : ∀ z, HasFDerivAt (fun w => f w - ℓ w) (fderiv ℝ f z - ℓ) z := fun z =>
    (hf z).hasFDerivAt.sub ℓ.hasFDerivAt
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fun w => f w - ℓ w)
    (s := segment ℝ x y) (fun z _ => (hg z).differentiableAt)
    (fun z hz => by rw [(hg z).fderiv]; exact hM z hz) (convex_segment x y)
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  rw [Real.norm_eq_abs] at this
  rw [map_sub]
  convert this using 2
  ring

lemma nap_seg_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (x y c z : X)
    (hz : z ∈ segment ℝ x y) : ‖z - c‖ ≤ max ‖x - c‖ ‖y - c‖ := by
  have hx : x ∈ Metric.closedBall c (max ‖x - c‖ ‖y - c‖) := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact le_max_left _ _
  have hy : y ∈ Metric.closedBall c (max ‖x - c‖ ‖y - c‖) := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact le_max_right _ _
  have := (convex_closedBall c _).segment_subset hx hy hz
  rwa [Metric.mem_closedBall, dist_eq_norm] at this

lemma nap_fderiv_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (f : F → ℝ) (z : F) (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ f z = InnerProductSpace.toDual ℝ F (gradient f z) :=
  hf.hasGradientAt.hasFDerivAt.fderiv

lemma nap_fderiv_apply {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (f : F → ℝ) (z h : F) (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ f z h = ⟪gradient f z, h⟫_ℝ := by
  rw [nap_fderiv_eq f z hf]; simp

/-- gradient-Lipschitz Taylor bound -/
lemma nap_taylor_grad {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (f : F → ℝ) (L : ℝ) (hf : Differentiable ℝ f)
    (hL : ∀ a b, ‖gradient f a - gradient f b‖ ≤ L * ‖a - b‖) (hL0 : 0 ≤ L) (c x y : F) :
    |f y - f x - ⟪gradient f c, y - x⟫_ℝ| ≤ L * max ‖x - c‖ ‖y - c‖ * ‖y - x‖ := by
  have := nap_taylor_core f (fderiv ℝ f c) x y (L * max ‖x - c‖ ‖y - c‖) hf (fun z hz => by
    rw [nap_fderiv_eq f z (hf z), nap_fderiv_eq f c (hf c), ← map_sub,
      LinearIsometryEquiv.norm_map]
    exact (hL z c).trans (mul_le_mul_of_nonneg_left (nap_seg_bound x y c z hz) hL0))
  rwa [nap_fderiv_apply f c _ (hf c)] at this

lemma nap_G_fderiv {n d m : ℕ} (P : NAPPAL.KL.Problem n d m) (hG : Differentiable ℝ P.G)
    (x : NAPPAL.KL.E n) (y : NAPPAL.KL.E d) (h1 : NAPPAL.KL.E n) (h2 : NAPPAL.KL.E d) :
    fderiv ℝ P.G (x, y) (h1, h2) =
      ⟪NAPPAL.KL.gradU P x y, h1⟫_ℝ + ⟪NAPPAL.KL.gradV P x y, h2⟫_ℝ := by
  have hu : HasFDerivAt (fun u' => P.G (u', y))
      ((fderiv ℝ P.G (x, y)).comp (ContinuousLinearMap.inl ℝ _ _)) x :=
    (hG (x, y)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x y)
  have hv : HasFDerivAt (fun v' => P.G (x, v'))
      ((fderiv ℝ P.G (x, y)).comp (ContinuousLinearMap.inr ℝ _ _)) y :=
    (hG (x, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)
  have e1 := nap_fderiv_apply (fun u' => P.G (u', y)) x h1 hu.differentiableAt
  have e2 := nap_fderiv_apply (fun v' => P.G (x, v')) y h2 hv.differentiableAt
  rw [hu.fderiv] at e1
  rw [hv.fderiv] at e2
  unfold NAPPAL.KL.gradU NAPPAL.KL.gradV
  rw [← e1, ← e2]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply]
  rw [← map_add]
  simp

lemma nap_G_taylor {n d m : ℕ} (P : NAPPAL.KL.Problem n d m) (LG : ℝ)
    (hG : Differentiable ℝ P.G) (hLG : 0 ≤ LG)
    (hlip : ∀ u v u' v', ‖NAPPAL.KL.gradU P u v - NAPPAL.KL.gradU P u' v'‖ ^ 2 +
      ‖NAPPAL.KL.gradV P u v - NAPPAL.KL.gradV P u' v'‖ ^ 2 ≤
      LG ^ 2 * (‖u - u'‖ ^ 2 + ‖v - v'‖ ^ 2))
    (c a b : NAPPAL.KL.E n × NAPPAL.KL.E d) :
    |P.G b - P.G a - ⟪NAPPAL.KL.gradU P c.1 c.2, b.1 - a.1⟫_ℝ -
        ⟪NAPPAL.KL.gradV P c.1 c.2, b.2 - a.2⟫_ℝ| ≤
      2 * LG * max ‖a - c‖ ‖b - c‖ * ‖b - a‖ := by
  have := nap_taylor_core P.G (fderiv ℝ P.G c) a b (2 * LG * max ‖a - c‖ ‖b - c‖) hG
    (fun z hz => by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro h
      have hz' := nap_seg_bound a b c z hz
      simp only [ContinuousLinearMap.sub_apply]
      have ez : fderiv ℝ P.G z h = fderiv ℝ P.G (z.1, z.2) (h.1, h.2) := rfl
      have ec : fderiv ℝ P.G c h = fderiv ℝ P.G (c.1, c.2) (h.1, h.2) := rfl
      rw [ez, ec, nap_G_fderiv P hG, nap_G_fderiv P hG]
      set gu := NAPPAL.KL.gradU P z.1 z.2 - NAPPAL.KL.gradU P c.1 c.2
      set gv := NAPPAL.KL.gradV P z.1 z.2 - NAPPAL.KL.gradV P c.1 c.2
      have heq : ⟪NAPPAL.KL.gradU P z.1 z.2, h.1⟫_ℝ + ⟪NAPPAL.KL.gradV P z.1 z.2, h.2⟫_ℝ -
          (⟪NAPPAL.KL.gradU P c.1 c.2, h.1⟫_ℝ + ⟪NAPPAL.KL.gradV P c.1 c.2, h.2⟫_ℝ) =
          ⟪gu, h.1⟫_ℝ + ⟪gv, h.2⟫_ℝ := by
        simp only [gu, gv, inner_sub_left]; ring
      rw [heq, Real.norm_eq_abs]
      have h1 : ‖h.1‖ ≤ ‖h‖ := norm_fst_le h
      have h2 : ‖h.2‖ ≤ ‖h‖ := norm_snd_le h
      have i1 := abs_real_inner_le_norm gu h.1
      have i2 := abs_real_inner_le_norm gv h.2
      have hzc1 : ‖z.1 - c.1‖ ≤ ‖z - c‖ := norm_fst_le (z - c)
      have hzc2 : ‖z.2 - c.2‖ ≤ ‖z - c‖ := norm_snd_le (z - c)
      have hl := hlip z.1 z.2 c.1 c.2
      set N := ‖z - c‖
      have hN : 0 ≤ N := norm_nonneg _
      have hsum : ‖gu‖ + ‖gv‖ ≤ 2 * LG * N := by
        have a0 : 0 ≤ ‖gu‖ := norm_nonneg _
        have b0 : 0 ≤ ‖gv‖ := norm_nonneg _
        have q1 : ‖z.1 - c.1‖ ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzc1 2
        have q2 : ‖z.2 - c.2‖ ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzc2 2
        have : (‖gu‖ + ‖gv‖) ^ 2 ≤ (2 * LG * N) ^ 2 := by
          nlinarith [sq_nonneg (‖gu‖ - ‖gv‖)]
        exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 this
      have hm : 2 * LG * N ≤ 2 * LG * max ‖a - c‖ ‖b - c‖ :=
        mul_le_mul_of_nonneg_left hz' (by positivity)
      have hh : 0 ≤ ‖h‖ := norm_nonneg _
      calc |⟪gu, h.1⟫_ℝ + ⟪gv, h.2⟫_ℝ| ≤ |⟪gu, h.1⟫_ℝ| + |⟪gv, h.2⟫_ℝ| := abs_add_le _ _
        _ ≤ ‖gu‖ * ‖h‖ + ‖gv‖ * ‖h‖ := by
            gcongr
            · exact i1.trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
            · exact i2.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
        _ = (‖gu‖ + ‖gv‖) * ‖h‖ := by ring
        _ ≤ 2 * LG * max ‖a - c‖ ‖b - c‖ * ‖h‖ := by gcongr; exact hsum.trans hm)
  have e : fderiv ℝ P.G c (b - a) = ⟪NAPPAL.KL.gradU P c.1 c.2, b.1 - a.1⟫_ℝ +
      ⟪NAPPAL.KL.gradV P c.1 c.2, b.2 - a.2⟫_ℝ := by
    have : fderiv ℝ P.G c (b - a) = fderiv ℝ P.G (c.1, c.2) ((b - a).1, (b - a).2) := rfl
    rw [this, nap_G_fderiv P hG]; rfl
  rw [e] at this
  convert this using 2
  ring

lemma nap_Om_comp {n d m : ℕ} (P : NAPPAL.KL.Problem n d m) (hOm : Differentiable ℝ P.Om)
    (z h : NAPPAL.KL.E n) (j : Fin m) :
    (fderiv ℝ P.Om z h).ofLp j = ⟪gradient (fun x => P.Om x j) z, h⟫_ℝ := by
  have hj : HasFDerivAt (fun x => P.Om x j)
      ((EuclideanSpace.proj j : NAPPAL.KL.E m →L[ℝ] ℝ).comp (fderiv ℝ P.Om z)) z :=
    (EuclideanSpace.proj j : NAPPAL.KL.E m →L[ℝ] ℝ).hasFDerivAt.comp z (hOm z).hasFDerivAt
  rw [← nap_fderiv_apply _ z h hj.differentiableAt, hj.fderiv]
  rfl

lemma nap_Om_taylor {n d m : ℕ} (P : NAPPAL.KL.Problem n d m) (LOmj : Fin m → ℝ)
    (hOm : Differentiable ℝ P.Om)
    (hL : ∀ j, 0 ≤ LOmj j ∧ ∀ u u', ‖gradient (fun x => P.Om x j) u -
      gradient (fun x => P.Om x j) u'‖ ≤ LOmj j * ‖u - u'‖)
    (q : NAPPAL.KL.E m) (c x y : NAPPAL.KL.E n) :
    |⟪q, P.Om y⟫_ℝ - ⟪q, P.Om x⟫_ℝ - ⟪q, fderiv ℝ P.Om c (y - x)⟫_ℝ| ≤
      ‖q‖ * NAPPAL.KL.LOm LOmj * max ‖x - c‖ ‖y - c‖ * ‖y - x‖ := by
  have hLO : 0 ≤ NAPPAL.KL.LOm LOmj := Finset.sum_nonneg (fun j _ => (hL j).1)
  have hd : ∀ z, HasFDerivAt (fun w => ⟪q, P.Om w⟫_ℝ)
      ((innerSL ℝ q).comp (fderiv ℝ P.Om z)) z := fun z =>
    (innerSL ℝ q).hasFDerivAt.comp z (hOm z).hasFDerivAt
  have := nap_taylor_core (fun w => ⟪q, P.Om w⟫_ℝ) ((innerSL ℝ q).comp (fderiv ℝ P.Om c)) x y
    (‖q‖ * NAPPAL.KL.LOm LOmj * max ‖x - c‖ ‖y - c‖) (fun z => (hd z).differentiableAt)
    (fun z hz => by
      rw [(hd z).fderiv]
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro h
      have hz' := nap_seg_bound x y c z hz
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
      rw [← inner_sub_right, PiLp.inner_apply, Real.norm_eq_abs]
      have hh : 0 ≤ ‖h‖ := norm_nonneg _
      calc |∑ j, ⟪q.ofLp j, (fderiv ℝ P.Om z h - fderiv ℝ P.Om c h).ofLp j⟫_ℝ|
          ≤ ∑ j, |⟪q.ofLp j, (fderiv ℝ P.Om z h - fderiv ℝ P.Om c h).ofLp j⟫_ℝ| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, ‖q‖ * (LOmj j * max ‖x - c‖ ‖y - c‖ * ‖h‖) := by
            apply Finset.sum_le_sum
            intro j _
            rw [PiLp.sub_apply, nap_Om_comp P hOm, nap_Om_comp P hOm, ← inner_sub_left]
            rw [real_inner_eq_re_inner, RCLike.re_to_real, RCLike.inner_apply, conj_trivial]
            rw [abs_mul]
            have hq : |q.ofLp j| ≤ ‖q‖ := by
              have := PiLp.norm_apply_le q j; rwa [Real.norm_eq_abs] at this
            have hg := abs_real_inner_le_norm (gradient (fun x => P.Om x j) z -
              gradient (fun x => P.Om x j) c) h
            have hlj := (hL j).2 z c
            have hl0 := (hL j).1
            have : |⟪gradient (fun x => P.Om x j) z - gradient (fun x => P.Om x j) c, h⟫_ℝ| ≤
                LOmj j * max ‖x - c‖ ‖y - c‖ * ‖h‖ := by
              refine hg.trans ?_
              gcongr
              exact hlj.trans (mul_le_mul_of_nonneg_left hz' hl0)
            rw [mul_comm]; exact mul_le_mul hq this (abs_nonneg _) (norm_nonneg _)
        _ = ‖q‖ * NAPPAL.KL.LOm LOmj * max ‖x - c‖ ‖y - c‖ * ‖h‖ := by
            rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul]; unfold NAPPAL.KL.LOm; ring)
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at this
  exact this

lemma nap_c1_le {n d m : ℕ} (ξ : NAPPAL.KL.W n d m) : ‖ξ.1‖ ≤ NAPPAL.KL.tnorm ξ := by
  unfold NAPPAL.KL.tnorm
  apply Real.le_sqrt_of_sq_le; nlinarith [sq_nonneg ‖ξ.2.1‖, sq_nonneg ‖ξ.2.2‖]
lemma nap_c2_le {n d m : ℕ} (ξ : NAPPAL.KL.W n d m) : ‖ξ.2.1‖ ≤ NAPPAL.KL.tnorm ξ := by
  unfold NAPPAL.KL.tnorm
  apply Real.le_sqrt_of_sq_le; nlinarith [sq_nonneg ‖ξ.1‖, sq_nonneg ‖ξ.2.2‖]
lemma nap_c3_le {n d m : ℕ} (ξ : NAPPAL.KL.W n d m) : ‖ξ.2.2‖ ≤ NAPPAL.KL.tnorm ξ := by
  unfold NAPPAL.KL.tnorm
  apply Real.le_sqrt_of_sq_le; nlinarith [sq_nonneg ‖ξ.1‖, sq_nonneg ‖ξ.2.1‖]


lemma nap_wd1 {n d m : ℕ} (a b : NAPPAL.KL.W n d m) : ‖a.1 - b.1‖ ≤ NAPPAL.KL.wdist a b :=
  nap_c1_le (a - b)
lemma nap_wd2 {n d m : ℕ} (a b : NAPPAL.KL.W n d m) : ‖a.2.1 - b.2.1‖ ≤ NAPPAL.KL.wdist a b :=
  nap_c2_le (a - b)

lemma nap_core {n d m : ℕ} (P : NAPPAL.KL.Problem n d m) (LG LH L0 LK γ Q εm εk : ℝ)
    (LOmj : Fin m → ℝ) (K : NAPPAL.KL.E n → ℝ)
    (hGd : Differentiable ℝ P.G) (hLG : 0 ≤ LG)
    (hGlip : ∀ u v u' v', ‖NAPPAL.KL.gradU P u v - NAPPAL.KL.gradU P u' v'‖ ^ 2 +
      ‖NAPPAL.KL.gradV P u v - NAPPAL.KL.gradV P u' v'‖ ^ 2 ≤
      LG ^ 2 * (‖u - u'‖ ^ 2 + ‖v - v'‖ ^ 2))
    (hHd : Differentiable ℝ P.H) (hLH : 0 ≤ LH)
    (hHlip : ∀ v v', ‖gradient P.H v - gradient P.H v'‖ ≤ LH * ‖v - v'‖)
    (hOmd : Differentiable ℝ P.Om) (hL0 : 0 ≤ L0)
    (hTlip : ∀ u u', ‖NAPPAL.KL.Theta P u - NAPPAL.KL.Theta P u'‖ ≤ L0 * ‖u - u'‖)
    (hOmL : ∀ j, 0 ≤ LOmj j ∧ ∀ u u', ‖gradient (fun x => P.Om x j) u -
      gradient (fun x => P.Om x j) u'‖ ≤ LOmj j * ‖u - u'‖)
    (hKd : Differentiable ℝ K) (hLK : 0 ≤ LK)
    (hKlip : ∀ u u', ‖gradient K u - gradient K u'‖ ≤ LK * ‖u - u'‖)
    (hγ : 0 < γ) (hεm0 : 0 < εm) (hεk : εm ≤ εk)
    (ub u0 u1 : NAPPAL.KL.E n) (vb v0 v1 : NAPPAL.KL.E d) (pb p0 p1 q : NAPPAL.KL.E m)
    (hqk : ‖q‖ ≤ Q) (hrb : NAPPAL.KL.Theta P ub + P.B vb = 0)
    (hqdef : q = p0 + γ • (NAPPAL.KL.Theta P u0 + P.B v0))
    (h7 : p1 = p0 + γ • (NAPPAL.KL.Theta P u1 + P.B v1))
    (O5 : ⟪NAPPAL.KL.gradU P u0 v0, u1⟫_ℝ + P.J u1 +
          ⟪q, fderiv ℝ P.Om u0 u1 + P.Phi u1⟫_ℝ + NAPPAL.KL.bregman K u1 u0 / εk ≤
        ⟪NAPPAL.KL.gradU P u0 v0, ub⟫_ℝ + P.J ub +
          ⟪q, fderiv ℝ P.Om u0 ub + P.Phi ub⟫_ℝ + NAPPAL.KL.bregman K ub u0 / εk)
    (O6 : ⟪NAPPAL.KL.gradV P u0 v0 + gradient P.H v0, v1⟫_ℝ + ⟪q, P.B v1⟫_ℝ +
          γ / 2 * ‖P.B (v1 - v0)‖ ^ 2 ≤
        ⟪NAPPAL.KL.gradV P u0 v0 + gradient P.H v0, vb⟫_ℝ + ⟪q, P.B vb⟫_ℝ +
          γ / 2 * ‖P.B (vb - v0)‖ ^ 2) :
    NAPPAL.KL.augLag P γ (u1, v1, p1) - NAPPAL.KL.augLag P γ (ub, vb, pb) ≤
      (2 * (γ * (L0 + ‖P.B‖) ^ 2 + Q * NAPPAL.KL.LOm LOmj + 2 * LG + LH + 2 * (LK / εm) +
        γ / 2 * ‖P.B‖ ^ 2 + γ / 2 * (L0 + ‖P.B‖) ^ 2) + 1) *
        (NAPPAL.KL.wdist (ub, vb, pb) (u1, v1, p1) ^ 2 +
          NAPPAL.KL.wdist (u0, v0, p0) (u1, v1, p1) ^ 2) := by
  have hεpos : 0 < εk := lt_of_lt_of_le hεm0 hεk
  have hLO : 0 ≤ NAPPAL.KL.LOm LOmj := Finset.sum_nonneg (fun j _ => (hOmL j).1)
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans hqk
  generalize hnB : ‖P.B‖ = nB
  have hnB0 : 0 ≤ nB := hnB ▸ norm_nonneg _
  have hBop : ∀ x, ‖P.B x‖ ≤ nB * ‖x‖ := fun x => hnB ▸ P.B.le_opNorm x
  have hAu : ‖ub - u1‖ ≤ NAPPAL.KL.wdist (ub, vb, pb) (u1, v1, p1) := nap_wd1 (ub, vb, pb) (u1, v1, p1)
  have hAv : ‖vb - v1‖ ≤ NAPPAL.KL.wdist (ub, vb, pb) (u1, v1, p1) := nap_wd2 (ub, vb, pb) (u1, v1, p1)
  have hBu : ‖u0 - u1‖ ≤ NAPPAL.KL.wdist (u0, v0, p0) (u1, v1, p1) := nap_wd1 (u0, v0, p0) (u1, v1, p1)
  have hBv : ‖v0 - v1‖ ≤ NAPPAL.KL.wdist (u0, v0, p0) (u1, v1, p1) := nap_wd2 (u0, v0, p0) (u1, v1, p1)
  have hA0 : 0 ≤ NAPPAL.KL.wdist (ub, vb, pb) (u1, v1, p1) := Real.sqrt_nonneg _
  have hB0 : 0 ≤ NAPPAL.KL.wdist (u0, v0, p0) (u1, v1, p1) := Real.sqrt_nonneg _
  generalize NAPPAL.KL.wdist (ub, vb, pb) (u1, v1, p1) = A at *
  generalize NAPPAL.KL.wdist (u0, v0, p0) (u1, v1, p1) = Bk at *
  obtain ⟨S, hS⟩ : ∃ S, S = A + Bk := ⟨_, rfl⟩
  -- elementary distance facts
  have n1 : ‖u1 - ub‖ ≤ A := by rw [norm_sub_rev]; exact hAu
  have n2 : ‖v1 - vb‖ ≤ A := by rw [norm_sub_rev]; exact hAv
  have n3 : ‖u1 - u0‖ ≤ Bk := by rw [norm_sub_rev]; exact hBu
  have n4 : ‖v1 - v0‖ ≤ Bk := by rw [norm_sub_rev]; exact hBv
  have n5 : ‖ub - u0‖ ≤ S := by
    have := norm_sub_le_norm_sub_add_norm_sub ub u1 u0; linarith
  have n6 : ‖vb - v0‖ ≤ S := by
    have := norm_sub_le_norm_sub_add_norm_sub vb v1 v0; linarith
  have hAS : A ≤ S := by linarith
  have hBS : Bk ≤ S := by linarith
  have hS0 : 0 ≤ S := by linarith
  -- T2
  have T2 := nap_Om_taylor P LOmj hOmd hOmL q u0 ub u1
  have T2' : ‖q‖ * NAPPAL.KL.LOm LOmj * max ‖ub - u0‖ ‖u1 - u0‖ * ‖u1 - ub‖ ≤
      Q * NAPPAL.KL.LOm LOmj * S ^ 2 := by
    have hm : max ‖ub - u0‖ ‖u1 - u0‖ ≤ S := max_le n5 (n3.trans hBS)
    calc ‖q‖ * NAPPAL.KL.LOm LOmj * max ‖ub - u0‖ ‖u1 - u0‖ * ‖u1 - ub‖
        ≤ Q * NAPPAL.KL.LOm LOmj * S * S := by gcongr; exact n1.trans hAS
      _ = Q * NAPPAL.KL.LOm LOmj * S ^ 2 := by ring
  have T2e : ⟪q, fderiv ℝ P.Om u0 (u1 - ub)⟫_ℝ =
      ⟪q, fderiv ℝ P.Om u0 u1⟫_ℝ - ⟪q, fderiv ℝ P.Om u0 ub⟫_ℝ := by
    rw [map_sub, inner_sub_right]
  -- T3
  have T3 := nap_G_taylor P LG hGd hLG hGlip (u0, v0) (ub, vb) (u1, v1)
  have T3' : 2 * LG * max ‖(ub, vb) - (u0, v0)‖ ‖(u1, v1) - (u0, v0)‖ * ‖(u1, v1) - (ub, vb)‖ ≤
      2 * LG * S ^ 2 := by
    have h1 : ‖(ub, vb) - (u0, v0)‖ ≤ S := by
      rw [Prod.mk_sub_mk]; exact norm_prod_le_iff.2 ⟨n5, n6⟩
    have h2 : ‖(u1, v1) - (u0, v0)‖ ≤ S := by
      rw [Prod.mk_sub_mk]; exact norm_prod_le_iff.2 ⟨n3.trans hBS, n4.trans hBS⟩
    have h3 : ‖(u1, v1) - (ub, vb)‖ ≤ S := by
      rw [Prod.mk_sub_mk]; exact norm_prod_le_iff.2 ⟨n1.trans hAS, n2.trans hAS⟩
    calc 2 * LG * max ‖(ub, vb) - (u0, v0)‖ ‖(u1, v1) - (u0, v0)‖ * ‖(u1, v1) - (ub, vb)‖
        ≤ 2 * LG * S * S := by gcongr; exact max_le h1 h2
      _ = 2 * LG * S ^ 2 := by ring
  simp only at T3
  have e3a : ⟪NAPPAL.KL.gradU P u0 v0, u1 - ub⟫_ℝ =
      ⟪NAPPAL.KL.gradU P u0 v0, u1⟫_ℝ - ⟪NAPPAL.KL.gradU P u0 v0, ub⟫_ℝ := inner_sub_right _ _ _
  have e3b : ⟪NAPPAL.KL.gradV P u0 v0, v1 - vb⟫_ℝ =
      ⟪NAPPAL.KL.gradV P u0 v0, v1⟫_ℝ - ⟪NAPPAL.KL.gradV P u0 v0, vb⟫_ℝ := inner_sub_right _ _ _
  -- T4
  have T4 := nap_taylor_grad P.H LH hHd hHlip hLH v0 vb v1
  have T4' : LH * max ‖vb - v0‖ ‖v1 - v0‖ * ‖v1 - vb‖ ≤ LH * S ^ 2 := by
    calc LH * max ‖vb - v0‖ ‖v1 - v0‖ * ‖v1 - vb‖ ≤ LH * S * S := by
          gcongr
          · exact max_le n6 (n4.trans hBS)
          · exact n2.trans hAS
      _ = LH * S ^ 2 := by ring
  have e4 : ⟪gradient P.H v0, v1 - vb⟫_ℝ =
      ⟪gradient P.H v0, v1⟫_ℝ - ⟪gradient P.H v0, vb⟫_ℝ := inner_sub_right _ _ _
  -- Bregman terms
  have hbreg : ∀ x : NAPPAL.KL.E n, ‖x - u0‖ ≤ S →
      |NAPPAL.KL.bregman K x u0| / εk ≤ LK / εm * S ^ 2 := by
    intro x hx
    have := nap_taylor_grad K LK hKd hKlip hLK u0 u0 x
    rw [sub_self, norm_zero, max_eq_right (norm_nonneg _)] at this
    have hb : |NAPPAL.KL.bregman K x u0| ≤ LK * S ^ 2 := by
      unfold NAPPAL.KL.bregman
      refine this.trans ?_
      calc LK * ‖x - u0‖ * ‖x - u0‖ ≤ LK * S * S := by gcongr
        _ = LK * S ^ 2 := by ring
    calc |NAPPAL.KL.bregman K x u0| / εk ≤ LK * S ^ 2 / εk := by gcongr
      _ ≤ LK * S ^ 2 / εm := div_le_div_of_nonneg_left (by positivity) hεm0 hεk
      _ = LK / εm * S ^ 2 := by ring
  have Db := hbreg ub n5
  have D1 := hbreg u1 (n3.trans hBS)
  have Db' : NAPPAL.KL.bregman K ub u0 / εk ≤ |NAPPAL.KL.bregman K ub u0| / εk := by
    gcongr; exact le_abs_self _
  have D1' : -(NAPPAL.KL.bregman K u1 u0 / εk) ≤ |NAPPAL.KL.bregman K u1 u0| / εk := by
    rw [← neg_div]; gcongr; exact neg_le_abs _
  -- residual r1 and dual step
  set r1 := NAPPAL.KL.Theta P u1 + P.B v1 with hr1
  set r0 := NAPPAL.KL.Theta P u0 + P.B v0 with hr0
  have hr1b : ‖r1‖ ≤ (L0 + nB) * A := by
    have : r1 = (NAPPAL.KL.Theta P u1 - NAPPAL.KL.Theta P ub) + P.B (v1 - vb) := by
      rw [map_sub, hr1]
      have : NAPPAL.KL.Theta P ub = - P.B vb := eq_neg_of_add_eq_zero_left hrb
      rw [this]; abel
    rw [this]
    have h1 := hTlip u1 ub
    have h2 := hBop (v1 - vb)
    calc ‖(NAPPAL.KL.Theta P u1 - NAPPAL.KL.Theta P ub) + P.B (v1 - vb)‖
        ≤ L0 * ‖u1 - ub‖ + nB * ‖v1 - vb‖ := (norm_add_le _ _).trans (by linarith)
      _ ≤ L0 * A + nB * A := by gcongr
      _ = (L0 + nB) * A := by ring
  have hpq : p1 - q = γ • (r1 - r0) := by
    rw [h7, hqdef, hr1, hr0, smul_sub]; abel
  have hpqb : ‖p1 - q‖ ≤ γ * ((L0 + nB) * Bk) := by
    rw [hpq, norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
    gcongr
    have : r1 - r0 = (NAPPAL.KL.Theta P u1 - NAPPAL.KL.Theta P u0) + P.B (v1 - v0) := by
      rw [map_sub, hr1, hr0]; abel
    rw [this]
    have h1 := hTlip u1 u0
    have h2 := hBop (v1 - v0)
    calc ‖(NAPPAL.KL.Theta P u1 - NAPPAL.KL.Theta P u0) + P.B (v1 - v0)‖
        ≤ L0 * ‖u1 - u0‖ + nB * ‖v1 - v0‖ := (norm_add_le _ _).trans (by linarith)
      _ ≤ L0 * Bk + nB * Bk := by gcongr
      _ = (L0 + nB) * Bk := by ring
  have T1 : ⟪p1 - q, r1⟫_ℝ ≤ γ * (L0 + nB) ^ 2 * S ^ 2 := by
    refine (real_inner_le_norm _ _).trans ?_
    calc ‖p1 - q‖ * ‖r1‖ ≤ (γ * ((L0 + nB) * Bk)) * ((L0 + nB) * A) := by
          gcongr
      _ ≤ (γ * ((L0 + nB) * S)) * ((L0 + nB) * S) := by gcongr
      _ = γ * (L0 + nB) ^ 2 * S ^ 2 := by ring
  have T5 : γ / 2 * ‖r1‖ ^ 2 ≤ γ / 2 * (L0 + nB) ^ 2 * S ^ 2 := by
    have : ‖r1‖ ^ 2 ≤ ((L0 + nB) * S) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hr1b.trans (by gcongr)) 2
    exact (mul_le_mul_of_nonneg_left this (by positivity)).trans_eq (by ring)
  have T6 : γ / 2 * ‖P.B (vb - v0)‖ ^ 2 ≤ γ / 2 * nB ^ 2 * S ^ 2 := by
    have : ‖P.B (vb - v0)‖ ≤ nB * S :=
      (hBop _).trans (by gcongr)
    have : ‖P.B (vb - v0)‖ ^ 2 ≤ (nB * S) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    exact (mul_le_mul_of_nonneg_left this (by positivity)).trans_eq (by ring)
  have T7 : 0 ≤ γ / 2 * ‖P.B (v1 - v0)‖ ^ 2 := by positivity
  -- assemble
  have hr1sq : ‖r1‖ ^ 2 = ‖r1‖ ^ 2 := rfl
  have L1 : NAPPAL.KL.augLag P γ (u1, v1, p1) = P.G (u1, v1) + P.J u1 + P.H v1 +
      ⟪p1, r1⟫_ℝ + γ / 2 * ‖r1‖ ^ 2 := rfl
  have L2 : NAPPAL.KL.augLag P γ (ub, vb, pb) = P.G (ub, vb) + P.J ub + P.H vb := by
    show P.G (ub, vb) + P.J ub + P.H vb + ⟪pb, NAPPAL.KL.Theta P ub + P.B vb⟫_ℝ +
      γ / 2 * ‖NAPPAL.KL.Theta P ub + P.B vb‖ ^ 2 = _
    rw [hrb]; simp
  have ep : ⟪p1, r1⟫_ℝ = ⟪p1 - q, r1⟫_ℝ + ⟪q, r1⟫_ℝ := by rw [inner_sub_left]; ring
  have eq1 : ⟪q, r1⟫_ℝ = ⟪q, P.Om u1⟫_ℝ + ⟪q, P.Phi u1⟫_ℝ + ⟪q, P.B v1⟫_ℝ := by
    rw [hr1]; unfold NAPPAL.KL.Theta; rw [inner_add_right, inner_add_right]
  have eqb : ⟪q, P.Om ub⟫_ℝ + ⟪q, P.Phi ub⟫_ℝ + ⟪q, P.B vb⟫_ℝ = 0 := by
    have : ⟪q, NAPPAL.KL.Theta P ub + P.B vb⟫_ℝ = 0 := by rw [hrb]; simp
    unfold NAPPAL.KL.Theta at this; rw [inner_add_right, inner_add_right] at this; exact this
  rw [inner_add_right, inner_add_right] at O5
  rw [inner_add_left, inner_add_left] at O6
  have hT2 := (abs_le.1 T2).2
  have hT3 := (abs_le.1 T3).2
  have hT4 := (abs_le.1 T4).2
  rw [T2e] at hT2
  rw [e3a, e3b] at hT3
  rw [e4] at hT4
  have hfin : NAPPAL.KL.augLag P γ (u1, v1, p1) - NAPPAL.KL.augLag P γ (ub, vb, pb) ≤
      (γ * (L0 + nB) ^ 2 + Q * NAPPAL.KL.LOm LOmj + 2 * LG + LH + 2 * (LK / εm) +
        γ / 2 * nB ^ 2 + γ / 2 * (L0 + nB) ^ 2) * S ^ 2 := by
    rw [L1, L2, ep, eq1]
    linarith
  have hS2 : S ^ 2 ≤ 2 * (A ^ 2 + Bk ^ 2) := by
    rw [hS]
    calc (A + Bk) ^ 2 = 2 * (A ^ 2 + Bk ^ 2) - (A - Bk) ^ 2 := by ring
      _ ≤ 2 * (A ^ 2 + Bk ^ 2) := by linarith [sq_nonneg (A - Bk)]
  generalize hCdef : γ * (L0 + nB) ^ 2 + Q * NAPPAL.KL.LOm LOmj + 2 * LG + LH + 2 * (LK / εm) +
        γ / 2 * nB ^ 2 + γ / 2 * (L0 + nB) ^ 2 = C at hfin ⊢
  have hC0 : 0 ≤ C := by rw [← hCdef]; positivity
  have hX : 0 ≤ A ^ 2 + Bk ^ 2 := by positivity
  refine hfin.trans ?_
  calc C * S ^ 2 ≤ C * (2 * (A ^ 2 + Bk ^ 2)) := mul_le_mul_of_nonneg_left hS2 hC0
    _ ≤ (2 * C + 1) * (A ^ 2 + Bk ^ 2) := by
        have : C * (2 * (A ^ 2 + Bk ^ 2)) + (A ^ 2 + Bk ^ 2) = (2 * C + 1) * (A ^ 2 + Bk ^ 2) := by
          ring
        linarith

theorem solution {n d m : ℕ} (P : NAPPAL.KL.Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (LK : ℝ) (K : NAPPAL.KL.E n → ℝ) (β γ σ : ℝ) (δ ε : ℕ → ℝ)
    (u : ℕ → NAPPAL.KL.E n) (v : ℕ → NAPPAL.KL.E d) (p : ℕ → NAPPAL.KL.E m)
    (hrun : NAPPAL.Subreg.RunHyp P LG LH L0 LOmj LK K β γ σ δ ε u v p) :
    ∃ c6 : ℝ, 0 < c6 ∧ ∀ wbar : NAPPAL.KL.W n d m, NAPPAL.KL.IsStationary P γ wbar → ∀ k : ℕ,
      NAPPAL.KL.augLag P γ (NAPPAL.KL.wseq u v p (k+1)) - NAPPAL.KL.augLag P γ wbar ≤
        c6 * (NAPPAL.KL.wdist wbar (NAPPAL.KL.wseq u v p (k+1)) ^ 2 +
          NAPPAL.KL.wdist (NAPPAL.KL.wseq u v p k) (NAPPAL.KL.wseq u v p (k+1)) ^ 2) := by
  have hrun' : NAPPAL.Rate.RunHyp P LG LH L0 LOmj K β LK γ σ δ ε u v p := by
    obtain ⟨h1, h2, ⟨hγ, hσ, hσ1, hk⟩, h8⟩ := hrun
    refine ⟨h1, h2, ⟨hγ, hσ, hσ1, fun k => ?_⟩, h8⟩
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hk k
    exact ⟨⟨a1, a2, a3⟩, a4, a5, a6⟩
  obtain ⟨-, -, ⟨⟨R, hR⟩, -⟩, -, -, -⟩ :=
    NAPPAL.Rate.theorem_4_1 P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun'
  obtain ⟨hA1, hA2, ⟨hγ, hσ, hσ1, hk⟩, h8⟩ := hrun
  obtain ⟨⟨hGd, hLG, hGlip⟩, ⟨hHd, hLH, hHlip⟩, -, ⟨hOmd, -, hL0, hTlip⟩, hOmL, ⟨-, hlam⟩, -⟩ :=
    hA1
  obtain ⟨hKd, hβ, -, hLK, hKlip, -⟩ := hA2
  have hR0 : 0 ≤ R := le_trans (Real.sqrt_nonneg _) (hR 0)
  have hLO : 0 ≤ NAPPAL.KL.LOm LOmj := Finset.sum_nonneg (fun j _ => (hOmL j).1)
  set nB := ‖P.B‖ with hnB
  have hnB0 : 0 ≤ nB := norm_nonneg _
  set Q := R + γ * (‖NAPPAL.KL.Theta P 0‖ + L0 * R + nB * R) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  -- bound on q^k
  have hq : ∀ k, ‖NAPPAL.Rate.qseq P γ u v p k‖ ≤ Q := by
    intro k
    have hu := (nap_c1_le ((u k, v k, p k) : NAPPAL.KL.W n d m)).trans (hR k)
    have hv := (nap_c2_le ((u k, v k, p k) : NAPPAL.KL.W n d m)).trans (hR k)
    have hp := (nap_c3_le ((u k, v k, p k) : NAPPAL.KL.W n d m)).trans (hR k)
    simp only at hu hv hp
    have hT : ‖NAPPAL.KL.Theta P (u k)‖ ≤ ‖NAPPAL.KL.Theta P 0‖ + L0 * R := by
      have := hTlip (u k) 0
      rw [sub_zero] at this
      have h2 := norm_sub_norm_le (NAPPAL.KL.Theta P (u k)) (NAPPAL.KL.Theta P 0)
      nlinarith
    have hBv : ‖P.B (v k)‖ ≤ nB * R :=
      (P.B.le_opNorm _).trans (mul_le_mul_of_nonneg_left hv hnB0)
    unfold NAPPAL.Rate.qseq
    calc ‖p k + γ • (NAPPAL.KL.Theta P (u k) + P.B (v k))‖
        ≤ ‖p k‖ + ‖γ • (NAPPAL.KL.Theta P (u k) + P.B (v k))‖ := norm_add_le _ _
      _ = ‖p k‖ + γ * ‖NAPPAL.KL.Theta P (u k) + P.B (v k)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
      _ ≤ R + γ * (‖NAPPAL.KL.Theta P 0‖ + L0 * R + nB * R) := by
          gcongr
          exact (norm_add_le _ _).trans (by linarith)
  -- lower bound on ε^k
  set lam := NAPPAL.KL.lamMin P
  set Dmax := LG + Q * NAPPAL.KL.LOm LOmj + γ * L0 ^ 2 + 14 * γ * nB ^ 2 * L0 ^ 2 / lam +
    14 * (LG + γ * nB * L0) ^ 2 / (γ * lam) + 1 with hDmax
  have hDmax1 : 1 ≤ Dmax := by
    have : 0 ≤ 14 * γ * nB ^ 2 * L0 ^ 2 / lam := by positivity
    have : 0 ≤ 14 * (LG + γ * nB * L0) ^ 2 / (γ * lam) := by positivity
    have : 0 ≤ Q * NAPPAL.KL.LOm LOmj := by positivity
    have : 0 ≤ γ * L0 ^ 2 := by positivity
    linarith
  set εm := σ * (β / Dmax) with hεm
  have hεm0 : 0 < εm := by positivity
  have hεk : ∀ k, εm ≤ ε k := by
    intro k
    obtain ⟨-, hσδ, -⟩ := hk k
    refine le_trans ?_ hσδ
    apply mul_le_mul_of_nonneg_left _ hσ.le
    rw [h8 k]
    unfold NAPPAL.KL.delta8
    have hqk := hq k
    have hD : LG + ‖NAPPAL.Rate.qseq P γ u v p k‖ * NAPPAL.KL.LOm LOmj + γ * L0 ^ 2 +
        14 * γ * ‖P.B‖ ^ 2 * L0 ^ 2 / NAPPAL.KL.lamMin P +
        14 * (LG + γ * ‖P.B‖ * L0) ^ 2 / (γ * NAPPAL.KL.lamMin P) + 1 ≤ Dmax := by
      rw [hDmax]
      have := mul_le_mul_of_nonneg_right hqk hLO
      linarith
    have hpos : 0 < LG + ‖NAPPAL.Rate.qseq P γ u v p k‖ * NAPPAL.KL.LOm LOmj + γ * L0 ^ 2 +
        14 * γ * ‖P.B‖ ^ 2 * L0 ^ 2 / NAPPAL.KL.lamMin P +
        14 * (LG + γ * ‖P.B‖ * L0) ^ 2 / (γ * NAPPAL.KL.lamMin P) + 1 := by positivity
    exact div_le_div_of_nonneg_left hβ.le hpos hD
  -- the constant
  set C := γ * (L0 + nB) ^ 2 + Q * NAPPAL.KL.LOm LOmj + 2 * LG + LH + 2 * (LK / εm) +
    γ / 2 * nB ^ 2 + γ / 2 * (L0 + nB) ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨2 * C + 1, by positivity, ?_⟩
  rintro ⟨ub, vb, pb⟩ hstat k
  obtain ⟨a, -, b, hb, -, -, hr0⟩ := hstat
  have hubU : ub ∈ P.U := hb.1
  have hrb : NAPPAL.KL.Theta P ub + P.B vb = 0 := by
    have := hr0; simp only at this; exact this.symm
  obtain ⟨hδpos, hσδ, hεδ, ⟨-, h5⟩, h6, h7⟩ := hk k
  have hqk := hq k
  exact nap_core P LG LH L0 LK γ Q εm (ε k) LOmj K hGd hLG hGlip hHd hLH hHlip hOmd hL0 hTlip
    hOmL hKd hLK hKlip hγ hεm0 (hεk k) ub (u k) (u (k+1)) vb (v k) (v (k+1)) pb (p k) (p (k+1))
    (NAPPAL.Rate.qseq P γ u v p k) hqk hrb rfl h7 (h5 ub hubU) (h6 vb)
