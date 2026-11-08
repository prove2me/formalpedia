-- Prove2me | solution 1 for NonStrongConvexGM.QuasiStrong.projected_gradient_linear_convergence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T03:14:51.798727+00:00
-- url     : https://prove2.me/submissions/76732530-4cc2-4d0a-9aaf-646028c8994e

import Mathlib
import Definitions.Def_NonStrongConvexGM_QuasiStrong_Model

set_option autoImplicit false

section PGLCHelpers

open NonStrongConvexGM.QuasiStrong NecoaraNG.Chain
open scoped InnerProductSpace

theorem pglc_nearest_exists {n : ℕ} {S : Set (E n)} (hS : IsClosed S) (hne : S.Nonempty)
    (u : E n) : ∃ p, IsNearest S u p := by
  obtain ⟨p, hp, hd⟩ := hS.exists_infDist_eq_dist hne u
  refine ⟨p, hp, fun z hz => ?_⟩
  rw [← dist_eq_norm, ← dist_eq_norm, ← hd]
  exact Metric.infDist_le_dist_of_mem hz

theorem pglc_project_spec {n : ℕ} {S : Set (E n)} {u : E n} (h : ∃ p, IsNearest S u p) :
    IsNearest S u (project S u) := by
  unfold project
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- Variational inequality for a nearest point of a convex set. -/
theorem pglc_proj_vi {n : ℕ} {S : Set (E n)} (hS : Convex ℝ S)
    {u p : E n} (h : IsNearest S u p) {z : E n} (hz : z ∈ S) : ⟪u - p, z - p⟫_ℝ ≤ 0 := by
  by_contra hc
  push Not at hc
  have hD0 : 0 ≤ ‖z - p‖ ^ 2 := sq_nonneg _
  have hDc : 0 < ‖z - p‖ ^ 2 + ⟪u - p, z - p⟫_ℝ := by linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ⟪u - p, z - p⟫_ℝ / (‖z - p‖ ^ 2 + ⟪u - p, z - p⟫_ℝ) :=
    ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; exact div_pos hc hDc
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hDc]; linarith
  have hq : p + t • (z - p) ∈ S := hS.add_smul_sub_mem h.1 hz ⟨ht0.le, ht1⟩
  have h1 := h.2 _ hq
  have h2 : ‖u - p‖ ^ 2 ≤ ‖u - (p + t • (z - p))‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h1
  have h3 : u - (p + t • (z - p)) = (u - p) - t • (z - p) := by abel
  rw [h3, norm_sub_sq_real (u - p) (t • (z - p)), real_inner_smul_right, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs] at h2
  have h4 : t * (2 * ⟪u - p, z - p⟫_ℝ) ≤ t * (t * ‖z - p‖ ^ 2) := by nlinarith
  have h5 : 2 * ⟪u - p, z - p⟫_ℝ ≤ t * ‖z - p‖ ^ 2 := le_of_mul_le_mul_left h4 ht0
  have h6 : t * ‖z - p‖ ^ 2 < ⟪u - p, z - p⟫_ℝ := by
    rw [ht, div_mul_eq_mul_div, div_lt_iff₀ hDc]
    nlinarith
  linarith

theorem pglc_nearest_unique {n : ℕ} {S : Set (E n)} (hS : Convex ℝ S) {u p q : E n}
    (hp : IsNearest S u p) (hq : IsNearest S u q) : p = q := by
  have h1 := pglc_proj_vi hS hp hq.1
  have h2 := pglc_proj_vi hS hq hp.1
  have e : ‖q - p‖ ^ 2 = ⟪u - p, q - p⟫_ℝ + ⟪u - q, p - q⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  have h3 : ‖q - p‖ ^ 2 ≤ 0 := by rw [e]; linarith
  have h4 : ‖q - p‖ = 0 := by nlinarith [norm_nonneg (q - p)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp h4)).symm

variable {n : ℕ} (P : Problem n)

theorem pglc_contOn : ContinuousOn P.f P.X := fun x hx => (P.derivative x hx).continuousWithinAt

theorem pglc_opt_val {y : E n} (hy : y ∈ optSet P.X P.f) : P.f y = value P := by
  have hc := Classical.choose_spec P.attained
  exact le_antisymm (hy.2 _ hc.1) (hc.2 _ hy.1)

theorem pglc_optSet_convex : Convex ℝ (optSet P.X P.f) := by
  intro a ha b hb θ η hθ hη hθη
  refine ⟨P.convex.1 ha.1 hb.1 hθ hη hθη, fun z hz => ?_⟩
  have h1 := P.convex.2 ha.1 hb.1 hθ hη hθη
  have hza := ha.2 z hz
  have hzb := hb.2 z hz
  simp only [smul_eq_mul] at h1
  have hsum : θ * P.f z + η * P.f z = P.f z := by rw [← add_mul, hθη, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hza hθ, mul_le_mul_of_nonneg_left hzb hη]

theorem pglc_optSet_closed : IsClosed (optSet P.X P.f) := by
  have e : optSet P.X P.f = P.X ∩ P.f ⁻¹' Set.Iic (value P) := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      show P.f x ≤ value P
      exact hx.2 _ (Classical.choose_spec P.attained).1
    · rintro ⟨hx, hv⟩
      refine ⟨hx, fun y hy => ?_⟩
      have hv' : P.f x ≤ value P := hv
      exact hv'.trans ((Classical.choose_spec P.attained).2 y hy)
  rw [e]
  exact (pglc_contOn P).preimage_isClosed_of_isClosed P.closed isClosed_Iic

theorem pglc_nearestOpt_spec (x : E n) : IsNearest (optSet P.X P.f) x (nearestOpt P x) :=
  pglc_project_spec (pglc_nearest_exists (pglc_optSet_closed P) P.attained x)

theorem pglc_nearestOpt_eq {x p : E n} (h : IsNearest (optSet P.X P.f) x p) :
    nearestOpt P x = p :=
  pglc_nearest_unique (pglc_optSet_convex P) (pglc_nearestOpt_spec P x) h

theorem pglc_line_deriv {x w : E n} (hmaps : ∀ s ∈ Set.Icc (0 : ℝ) 1, x + s • w ∈ P.X)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun s : ℝ => P.f (x + s • w)) ⟪P.grad (x + t • w), w⟫_ℝ
      (Set.Icc 0 1) t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have hm : Set.MapsTo (fun s : ℝ => x + s • w) (Set.Icc 0 1) P.X := fun s hs => hmaps s hs
  have h1 := (P.derivative _ (hmaps t ht)).comp_hasDerivWithinAt t hl.hasDerivWithinAt hm
  rw [innerSL_apply_apply] at h1
  exact h1

theorem pglc_descent {x y : E n} (hx : x ∈ P.X) (hy : y ∈ P.X) :
    P.f y ≤ P.f x + ⟪P.grad x, y - x⟫_ℝ + P.L / 2 * ‖y - x‖ ^ 2 := by
  obtain ⟨w, hw⟩ : ∃ w, w = y - x := ⟨_, rfl⟩
  rw [← hw]
  have hmaps : ∀ s ∈ Set.Icc (0 : ℝ) 1, x + s • w ∈ P.X := fun s hs => by
    rw [hw]; exact P.convex.1.add_smul_sub_mem hx hy hs
  let g : ℝ → ℝ := fun t => P.f (x + t • w) - t * ⟪P.grad x, w⟫_ℝ - P.L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt g (⟪P.grad (x + t • w), w⟫_ℝ
      - ⟪P.grad x, w⟫_ℝ - P.L / 2 * (2 * t) * ‖w‖ ^ 2) (Set.Icc 0 1) t := by
    intro t ht
    have h1 := pglc_line_deriv P hmaps ht
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪P.grad x, w⟫_ℝ) ⟪P.grad x, w⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪P.grad x, w⟫_ℝ
    have h3 : HasDerivAt (fun s : ℝ => P.L / 2 * s ^ 2 * ‖w‖ ^ 2)
        (P.L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (P.L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2.hasDerivWithinAt).sub h3.hasDerivWithinAt
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t ht => (hg t ht).continuousWithinAt)
    (fun t ht => (hg t (Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
  have hle : ⟪P.grad (x + c • w), w⟫_ℝ - ⟪P.grad x, w⟫_ℝ - P.L / 2 * (2 * c) * ‖w‖ ^ 2 ≤ 0 := by
    have e1 : ⟪P.grad (x + c • w), w⟫_ℝ - ⟪P.grad x, w⟫_ℝ = ⟪P.grad (x + c • w) - P.grad x, w⟫_ℝ := by
      rw [inner_sub_left]
    have e2 := real_inner_le_norm (P.grad (x + c • w) - P.grad x) w
    have e3 := P.grad_lipschitz (x + c • w) (hmaps c ⟨hc.1.le, hc.2.le⟩) x hx
    have e4 : ‖x + c • w - x‖ = c * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    rw [e4] at e3
    have : ‖P.grad (x + c • w) - P.grad x‖ * ‖w‖ ≤ P.L * (c * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
    nlinarith
  rw [hcd] at hle
  have : g 1 ≤ g 0 := by
    have := hle; simp only [sub_zero, div_one] at this; linarith
  simp only [g, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hxy : x + w = y := by rw [hw]; abel
  rw [hxy] at this
  linarith

theorem pglc_convex_fo {x y : E n} (hx : x ∈ P.X) (hy : y ∈ P.X) :
    P.f x + ⟪P.grad x, y - x⟫_ℝ ≤ P.f y := by
  have hmaps : ∀ s ∈ Set.Icc (0 : ℝ) 1, x + s • (y - x) ∈ P.X := fun s hs =>
    P.convex.1.add_smul_sub_mem hx hy hs
  have hφ : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ => P.f (x + t • (y - x))) := by
    have h := P.convex.comp_affineMap (AffineMap.lineMap x y)
    have e : (fun t : ℝ => P.f (x + t • (y - x))) = P.f ∘ AffineMap.lineMap x y := by
      funext t
      simp only [Function.comp_apply, AffineMap.lineMap_apply_module']
      rw [add_comm]
    rw [e]
    refine h.subset (fun t ht => ?_) (convex_Icc 0 1)
    simp only [Set.mem_preimage, AffineMap.lineMap_apply_module']
    rw [add_comm]
    exact hmaps t ht
  have hd := pglc_line_deriv P hmaps (Set.left_mem_Icc.2 zero_le_one)
  rw [zero_smul, add_zero] at hd
  have hmem : Set.Icc (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    mem_nhdsWithin.2 ⟨Set.Iio 1, isOpen_Iio, Set.mem_Iio.2 zero_lt_one,
      fun t ht => ⟨le_of_lt ht.2, le_of_lt ht.1⟩⟩
  have h := hφ.le_slope_of_hasDerivWithinAt_Ioi (Set.left_mem_Icc.2 zero_le_one)
    (Set.right_mem_Icc.2 zero_le_one) zero_lt_one (hd.mono_of_mem_nhdsWithin hmem)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hxy : x + (y - x) = y := by abel
  rw [hxy] at h
  linarith

/-- Quasi-strong convexity gives quadratic functional growth at points of `X`. -/
theorem pglc_qg {κ : ℝ} (hq : IsQuasiStrong P κ) {x : E n} (hx : x ∈ P.X) :
    κ / 2 * ‖x - nearestOpt P x‖ ^ 2 ≤ P.f x - value P := by
  have hn := pglc_nearestOpt_spec P x
  obtain ⟨xb, hxb⟩ : ∃ xb, xb = nearestOpt P x := ⟨_, rfl⟩
  rw [← hxb] at hn ⊢
  have hval : P.f xb = value P := pglc_opt_val P hn.1
  rw [← hval]
  have hconvS := pglc_optSet_convex P
  obtain ⟨d, hd⟩ : ∃ d, d = x - xb := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = κ / 2 * ‖d‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ, ∀ t, h t = P.f (xb + t • d) - P.f xb := ⟨_, fun t => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, ∀ t, G t = ⟪P.grad (xb + t • d), d⟫_ℝ :=
    ⟨_, fun t => rfl⟩
  have hzX : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → xb + t • d ∈ P.X := by
    intro t ht0 ht1
    rw [hd]; exact P.convex.1.add_smul_sub_mem hn.1.1 hx ⟨ht0, ht1⟩
  have hnear : ∀ t : ℝ, 0 ≤ t → IsNearest (optSet P.X P.f) (xb + t • d) xb := by
    intro t ht
    refine ⟨hn.1, fun z hz => ?_⟩
    have hv : ⟪d, z - xb⟫_ℝ ≤ 0 := by rw [hd]; exact pglc_proj_vi hconvS hn hz
    have e1 : xb + t • d - xb = t • d := by abel
    have e2 : xb + t • d - z = t • d - (z - xb) := by abel
    rw [e1, e2]
    have h2 : ‖t • d‖ ^ 2 ≤ ‖t • d - (z - xb)‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_left]
      nlinarith [sq_nonneg ‖z - xb‖, mul_nonneg ht (neg_nonneg.mpr hv)]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
  have hQS : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → h t - t * G t + c * t ^ 2 ≤ 0 := by
    intro t ht ht1
    have q := hq.2 _ (hzX t ht ht1)
    rw [pglc_nearestOpt_eq P (hnear t ht), ← hval] at q
    have e1 : xb - (xb + t • d) = (-t) • d := by rw [neg_smul]; abel
    have e2 : xb + t • d - xb = t • d := by abel
    rw [e1, e2, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at q
    rw [hh, hG, hc]
    linarith
  have hfo : ∀ s t : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → h s + (t - s) * G s ≤ h t := by
    intro s t hs0 hs1 ht0 ht1
    have q := pglc_convex_fo P (hzX s hs0 hs1) (hzX t ht0 ht1)
    have e : xb + t • d - (xb + s • d) = (t - s) • d := by rw [sub_smul]; abel
    rw [e, real_inner_smul_right] at q
    rw [hh, hh, hG]
    linarith
  have hnn : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ h t := by
    intro t ht0 ht1
    have := hn.1.2 _ (hzX t ht0 ht1)
    rw [hh]
    linarith
  have hstep : ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ 1 → t * h s + (t - s) * s ^ 2 * c ≤ s * h t := by
    intro s t hs hst ht1
    have q1 := hQS s hs.le (hst.trans ht1)
    have q2 := hfo s t hs.le (hst.trans ht1) (hs.le.trans hst) ht1
    nlinarith [mul_le_mul_of_nonneg_left q2 hs.le,
      mul_le_mul_of_nonneg_left q1 (sub_nonneg.mpr hst)]
  have hchain : ∀ r : ℝ, 0 < r → r < 1 → ∀ M : ℕ,
      h (r ^ M) / r ^ M + c * r * (1 - r ^ M) ≤ h 1 := by
    intro r hr0 hr1 M
    induction M with
    | zero => simp
    | succ M ih =>
      have hT : 0 < r ^ M := pow_pos hr0 M
      have hS : 0 < r ^ (M + 1) := pow_pos hr0 (M + 1)
      have hSeq : r ^ (M + 1) = r ^ M * r := pow_succ r M
      have hT1 : r ^ M ≤ 1 := pow_le_one₀ hr0.le hr1.le
      have hst := hstep (r ^ (M + 1)) (r ^ M) hS (by rw [hSeq]; nlinarith) hT1
      have key : h (r ^ (M + 1)) / r ^ (M + 1) + c * (1 - r) * r ^ (M + 1)
          ≤ h (r ^ M) / r ^ M := by
        rw [div_add' _ _ _ hS.ne', div_le_div_iff₀ hS hT]
        have e : (h (r ^ (M + 1)) + c * (1 - r) * r ^ (M + 1) * r ^ (M + 1)) * r ^ M
            = r ^ M * h (r ^ (M + 1)) + (r ^ M - r ^ (M + 1)) * (r ^ (M + 1)) ^ 2 * c := by
          rw [hSeq]; ring
        rw [e]; linarith
      have e2 : c * r * (1 - r ^ (M + 1)) = c * r * (1 - r ^ M) + c * (1 - r) * r ^ (M + 1) := by
        rw [hSeq]; ring
      rw [e2]; linarith
  have hlow : ∀ r : ℝ, 0 < r → r < 1 → ∀ M : ℕ, c * r * (1 - r ^ M) ≤ h 1 := by
    intro r hr0 hr1 M
    have h1 := hchain r hr0 hr1 M
    have hp : 0 < r ^ M := pow_pos hr0 M
    have hp1 : r ^ M ≤ 1 := pow_le_one₀ hr0.le hr1.le
    have : 0 ≤ h (r ^ M) / r ^ M := div_nonneg (hnn _ hp.le hp1) hp.le
    linarith
  have hfin : c ≤ h 1 := by
    by_contra H
    push Not at H
    have h1nn : 0 ≤ h 1 := hnn 1 zero_le_one le_rfl
    have hcpos : 0 < c := lt_of_le_of_lt h1nn H
    obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = c - h 1 := ⟨_, rfl⟩
    have hεpos : 0 < ε := by linarith
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / (2 * c) := ⟨_, rfl⟩
    have hδpos : 0 < δ := by rw [hδ]; exact div_pos hεpos (by linarith)
    have hδc : c * δ = ε / 2 := by
      rw [hδ, mul_div_assoc', div_eq_div_iff (by linarith) (by norm_num)]; ring
    have hδle : δ ≤ 1 / 2 := by
      rw [hδ, div_le_iff₀ (by linarith)]; linarith
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hδpos (show 1 - δ < 1 by linarith)
    have hl := hlow (1 - δ) (by linarith) (by linarith) M
    have hpM : 0 ≤ (1 - δ) ^ M := pow_nonneg (by linarith) M
    nlinarith [mul_lt_mul_of_pos_left hM hcpos, mul_nonneg (mul_nonneg hcpos.le hpM) hδpos.le]
  have e1 : xb + (1 : ℝ) • d = x := by rw [one_smul, hd]; abel
  rw [hh, e1, hc, hd] at hfin
  exact hfin

/-- One projected gradient step: the gradient-mapping inequality. -/
theorem pglc_gm {x p : E n} (hx : x ∈ P.X)
    (hp : IsNearest P.X (x - (1 / P.L) • P.grad x) p) {z : E n} (hz : z ∈ P.X) :
    P.f p + P.L * ⟪x - p, z - x⟫_ℝ + P.L / 2 * ‖x - p‖ ^ 2
      ≤ P.f x + ⟪P.grad x, z - x⟫_ℝ := by
  have hL := P.L_pos
  have hdesc := pglc_descent P hx hp.1
  have hvi := pglc_proj_vi P.convex.1 hp hz
  have e1 : x - (1 / P.L) • P.grad x - p = (x - p) - (1 / P.L) • P.grad x := by abel
  have e2 : z - p = (z - x) + (x - p) := by abel
  have e3 : p - x = -(x - p) := by abel
  rw [e1, e2, inner_sub_left, real_inner_smul_left, inner_add_right, inner_add_right,
    real_inner_self_eq_norm_sq] at hvi
  rw [e3, inner_neg_right, norm_neg] at hdesc
  have hvi2 : ⟪x - p, z - x⟫_ℝ + ‖x - p‖ ^ 2
      ≤ (⟪P.grad x, z - x⟫_ℝ + ⟪P.grad x, x - p⟫_ℝ) / P.L := by
    rw [div_eq_mul_one_div, mul_comm]; linarith
  rw [le_div_iff₀ hL] at hvi2
  nlinarith

theorem pglc_rate_eq {κ : ℝ} (hκ : 0 < κ) : rate P κ = (P.L - κ) / (P.L + κ) := by
  have hL := P.L_pos
  unfold rate
  have h1 : (1 : ℝ) + κ / P.L ≠ 0 := by positivity
  rw [div_eq_div_iff h1 (by linarith)]
  field_simp

/-- One step contracts the squared distance to the optimal set by `rate`. -/
theorem pglc_step {κ : ℝ} (hq : IsQuasiStrong P κ) {x p : E n} (hx : x ∈ P.X)
    (hp : IsNearest P.X (x - (1 / P.L) • P.grad x) p) :
    ‖p - nearestOpt P p‖ ^ 2 ≤ rate P κ * ‖x - nearestOpt P x‖ ^ 2 ∧
      ‖p - nearestOpt P x‖ ≤ ‖x - nearestOpt P x‖ := by
  have hL := P.L_pos
  have hκ := hq.1
  have hxb := pglc_nearestOpt_spec P x
  have hpb := pglc_nearestOpt_spec P p
  have hgm := pglc_gm P hx hp hxb.1.1
  have hqs := hq.2 x hx
  have hfg := pglc_qg P hq hp.1
  have hnear : ‖p - nearestOpt P p‖ ≤ ‖p - nearestOpt P x‖ := hpb.2 _ hxb.1
  have hsq : ‖p - nearestOpt P p‖ ^ 2 ≤ ‖p - nearestOpt P x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnear 2
  have hid : ‖p - nearestOpt P x‖ ^ 2 = ‖x - p‖ ^ 2 + 2 * ⟪x - p, nearestOpt P x - x⟫_ℝ
      + ‖x - nearestOpt P x‖ ^ 2 := by
    have e : p - nearestOpt P x = -((x - p) + (nearestOpt P x - x)) := by abel
    rw [e, norm_neg, norm_add_sq_real, norm_sub_rev (nearestOpt P x) x]
  have hsqL := mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ P.L / 2)
  have hidL : P.L / 2 * ‖p - nearestOpt P x‖ ^ 2 = P.L / 2 * ‖x - p‖ ^ 2
      + P.L * ⟪x - p, nearestOpt P x - x⟫_ℝ + P.L / 2 * ‖x - nearestOpt P x‖ ^ 2 := by
    rw [hid]; ring
  have hA : (κ + P.L) * ‖p - nearestOpt P p‖ ^ 2
      ≤ (P.L - κ) * ‖x - nearestOpt P x‖ ^ 2 := by linarith
  have hB : P.L * ‖p - nearestOpt P x‖ ^ 2 ≤ P.L * ‖x - nearestOpt P x‖ ^ 2 := by
    nlinarith [sq_nonneg ‖p - nearestOpt P p‖, sq_nonneg ‖x - nearestOpt P x‖]
  refine ⟨?_, ?_⟩
  · rw [pglc_rate_eq P hκ, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    linarith
  · have hB' : ‖p - nearestOpt P x‖ ^ 2 ≤ ‖x - nearestOpt P x‖ ^ 2 :=
      le_of_mul_le_mul_left hB hL
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hB'

end PGLCHelpers

open NonStrongConvexGM.QuasiStrong in
theorem solution {n : ℕ} (P : Problem n) (κ : ℝ) (h : IsQuasiStrong P κ)
    (x₀ : NecoaraNG.Chain.E n) (hx₀ : x₀ ∈ P.X) :
    (∀ k : ℕ, ‖orbit P x₀ k - nearestOpt P (orbit P x₀ k)‖ ^ 2 ≤
      rate P κ ^ k * ‖x₀ - nearestOpt P x₀‖ ^ 2) ∧
    (∃ xlim : NecoaraNG.Chain.E n, xlim ∈ NecoaraNG.Chain.optSet P.X P.f ∧
      Filter.Tendsto (orbit P x₀) Filter.atTop (nhds xlim) ∧
      ∃ C r : ℝ, 0 ≤ C ∧ 0 ≤ r ∧ r < 1 ∧
        ∀ k : ℕ, ‖orbit P x₀ k - xlim‖ ≤ C * r ^ k) := by
  have hL := P.L_pos
  have hκ := h.1
  have hXne : P.X.Nonempty := ⟨x₀, hx₀⟩
  have hproj : ∀ u, NecoaraNG.Chain.IsNearest P.X u (project P.X u) := fun u =>
    pglc_project_spec (pglc_nearest_exists P.closed hXne u)
  have horb : ∀ k, orbit P x₀ (k + 1)
      = project P.X (orbit P x₀ k - (1 / P.L) • P.grad (orbit P x₀ k)) := fun k => rfl
  have hmem : ∀ k, orbit P x₀ k ∈ P.X := by
    intro k
    induction k with
    | zero => exact hx₀
    | succ k _ => rw [horb]; exact (hproj _).1
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℝ, ∀ k, δ k = ‖orbit P x₀ k - nearestOpt P (orbit P x₀ k)‖ :=
    ⟨_, fun k => rfl⟩
  have hδnn : ∀ k, 0 ≤ δ k := fun k => by rw [hδ]; exact norm_nonneg _
  have hstep : ∀ k, δ (k + 1) ^ 2 ≤ rate P κ * δ k ^ 2 ∧
      ‖orbit P x₀ (k + 1) - orbit P x₀ k‖ ≤ 2 * δ k := by
    intro k
    have hs := pglc_step P h (hmem k) (hproj (orbit P x₀ k - (1 / P.L) • P.grad (orbit P x₀ k)))
    rw [← horb] at hs
    refine ⟨by rw [hδ, hδ]; exact hs.1, ?_⟩
    have tri := norm_sub_le_norm_sub_add_norm_sub (orbit P x₀ (k + 1))
      (nearestOpt P (orbit P x₀ k)) (orbit P x₀ k)
    rw [norm_sub_rev (nearestOpt P (orbit P x₀ k)) (orbit P x₀ k)] at tri
    rw [hδ]; linarith [hs.2]
  have hrate1 : rate P κ < 1 := by
    rw [pglc_rate_eq P hκ, div_lt_one (by linarith)]; linarith
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = max (rate P κ) 0 := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; exact le_max_right _ _
  have hρ1 : ρ < 1 := by rw [hρdef]; exact max_lt hrate1 one_pos
  have hrρ : rate P κ ≤ ρ := by rw [hρdef]; exact le_max_left _ _
  have hρpow : ∀ k, δ k ^ 2 ≤ ρ ^ k * δ 0 ^ 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 := (hstep k).1
      have h2 : rate P κ * δ k ^ 2 ≤ ρ * δ k ^ 2 :=
        mul_le_mul_of_nonneg_right hrρ (sq_nonneg _)
      have h3 := mul_le_mul_of_nonneg_left ih hρ0
      rw [pow_succ ρ k]
      nlinarith
  have hx0 : orbit P x₀ 0 = x₀ := rfl
  refine ⟨?_, ?_⟩
  · intro k
    have goal_eq : ‖orbit P x₀ k - nearestOpt P (orbit P x₀ k)‖ ^ 2 ≤
        rate P κ ^ k * ‖x₀ - nearestOpt P x₀‖ ^ 2 ↔ δ k ^ 2 ≤ rate P κ ^ k * δ 0 ^ 2 := by
      rw [hδ, hδ, hx0]
    rw [goal_eq]
    rcases le_or_gt 0 (rate P κ) with hr | hr
    · have : ρ = rate P κ := by rw [hρdef]; exact max_eq_left hr
      rw [← this]; exact hρpow k
    · have h1 := (hstep 0).1
      have hz : δ 0 ^ 2 = 0 := by
        have := sq_nonneg (δ 1)
        nlinarith [sq_nonneg (δ 0)]
      have := hρpow k
      rw [hz, mul_zero] at this ⊢
      exact this
  · obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = Real.sqrt ρ := ⟨_, rfl⟩
    have hq0 : 0 ≤ q := by rw [hqdef]; exact Real.sqrt_nonneg _
    have hq2 : q ^ 2 = ρ := by rw [hqdef]; exact Real.sq_sqrt hρ0
    have hq1 : q < 1 := by
      rw [hqdef, Real.sqrt_lt' one_pos]; simpa using hρ1
    have hδq : ∀ k, δ k ≤ q ^ k * δ 0 := by
      intro k
      have h1 := hρpow k
      have e : (q ^ k * δ 0) ^ 2 = ρ ^ k * δ 0 ^ 2 := by
        rw [← hq2]; ring
      rw [← e] at h1
      exact (sq_le_sq₀ (hδnn k) (mul_nonneg (pow_nonneg hq0 k) (hδnn 0))).mp h1
    have hu : ∀ k, dist (orbit P x₀ k) (orbit P x₀ (k + 1)) ≤ 2 * δ 0 * q ^ k := by
      intro k
      rw [dist_eq_norm, norm_sub_rev]
      have := (hstep k).2
      have := hδq k
      nlinarith
    have hcs := cauchySeq_of_le_geometric q (2 * δ 0) hq1 hu
    obtain ⟨xlim, hlim⟩ := cauchySeq_tendsto_of_complete hcs
    have hxlimX : xlim ∈ P.X :=
      P.closed.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)
    have hδlim : Filter.Tendsto δ Filter.atTop (nhds 0) := by
      have hg : Filter.Tendsto (fun k : ℕ => δ 0 * q ^ k) Filter.atTop (nhds 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (δ 0)
      refine squeeze_zero hδnn (fun k => ?_) hg
      have := hδq k; linarith
    have hdiff0 : Filter.Tendsto (fun k => orbit P x₀ k - nearestOpt P (orbit P x₀ k))
        Filter.atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have e : (fun k => ‖orbit P x₀ k - nearestOpt P (orbit P x₀ k)‖) = δ := by
        funext k; rw [hδ]
      rw [e]; exact hδlim
    have hbar : Filter.Tendsto (fun k => nearestOpt P (orbit P x₀ k)) Filter.atTop
        (nhds xlim) := by
      have := hlim.sub hdiff0
      simpa using this
    have hcw := (P.derivative xlim hxlimX).continuousWithinAt
    have hfbar : Filter.Tendsto (fun k => P.f (nearestOpt P (orbit P x₀ k))) Filter.atTop
        (nhds (P.f xlim)) :=
      hcw.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hbar, Filter.Eventually.of_forall
        (fun k => (pglc_nearestOpt_spec P (orbit P x₀ k)).1.1)⟩)
    have hconst : (fun k => P.f (nearestOpt P (orbit P x₀ k))) = fun _ => value P := by
      funext k; exact pglc_opt_val P (pglc_nearestOpt_spec P (orbit P x₀ k)).1
    rw [hconst] at hfbar
    have hfx : value P = P.f xlim := tendsto_nhds_unique tendsto_const_nhds hfbar
    refine ⟨xlim, ⟨hxlimX, fun y hy => ?_⟩, hlim, 2 * δ 0 / (1 - q), q,
      div_nonneg (by linarith [hδnn 0]) (by linarith), hq0, hq1, fun k => ?_⟩
    · rw [← hfx]; exact (Classical.choose_spec P.attained).2 y hy
    · have := dist_le_of_le_geometric_of_tendsto q (2 * δ 0) hq1 hu hlim k
      rw [dist_eq_norm] at this
      calc ‖orbit P x₀ k - xlim‖ ≤ 2 * δ 0 * q ^ k / (1 - q) := this
        _ = 2 * δ 0 / (1 - q) * q ^ k := by ring
