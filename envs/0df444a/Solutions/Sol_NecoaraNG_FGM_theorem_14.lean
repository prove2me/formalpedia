-- Prove2me | solution 1 for NecoaraNG.FGM.theorem_14
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T05:36:43.490959+00:00
-- url     : https://prove2.me/submissions/a2d5f7a5-769d-4e53-bfe7-ae3b0cd51bd3

import Mathlib
import Definitions.Def_NecoaraNG_FGM_Setting

set_option autoImplicit false

open scoped RealInnerProductSpace in
theorem nc14_line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (x w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) ⟪G (x + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hF (x + t • w))).comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1

open scoped RealInnerProductSpace in
theorem nc14_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {L : ℝ} (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : E) :
    F y ≤ F x + ⟪G x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => F (x + t • w) - t * ⟪G x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪G (x + t • w), w⟫ - ⟪G x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := nc14_line_deriv hF x w t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪G x, w⟫) ⟪G x, w⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪G x, w⟫
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hle : ⟪G (x + c • w), w⟫ - ⟪G x, w⟫ - L / 2 * (2 * c) * ‖w‖ ^ 2 ≤ 0 := by
    have e1 : ⟪G (x + c • w), w⟫ - ⟪G x, w⟫ = ⟪G (x + c • w) - G x, w⟫ := by
      rw [inner_sub_left]
    have e2 := real_inner_le_norm (G (x + c • w) - G x) w
    have e3 := hG (x + c • w) x
    have e4 : ‖x + c • w - x‖ = c * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    rw [e4] at e3
    have : ‖G (x + c • w) - G x‖ * ‖w‖ ≤ L * (c * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
    nlinarith
  rw [hcd] at hle
  have : g 1 ≤ g 0 := by
    have := hle; simp only [sub_zero, div_one] at this; linarith
  simp only [g, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hw : x + w = y := by simp [w]
  rw [hw] at this
  linarith

open scoped RealInnerProductSpace in
theorem nc14_convex_fo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (hc : ConvexOn ℝ Set.univ F) (x y : E) : F x + ⟪G x, y - x⟫ ≤ F y := by
  set w := y - x
  have hφ : ConvexOn ℝ Set.univ (fun t : ℝ => F (x + t • w)) := by
    have := hc.comp_affineMap (AffineMap.lineMap x y)
    simp only [Set.preimage_univ] at this
    have e : (fun t : ℝ => F (x + t • w)) = F ∘ AffineMap.lineMap x y := by
      funext t
      simp [AffineMap.lineMap_apply, w, add_comm]
    rw [e]; exact this
  have h := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one
    (by simpa using nc14_line_deriv hF x w 0)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hw : x + w = y := by simp [w]
  rw [hw] at h
  linarith

open scoped InnerProductSpace in
/-- Variational inequality for a nearest point of a convex set. -/
theorem nc14_proj_vi {n : ℕ} {S : Set (NecoaraNG.Chain.E n)} (hS : Convex ℝ S)
    {u p : NecoaraNG.Chain.E n} (h : NecoaraNG.Chain.IsNearest S u p)
    {z : NecoaraNG.Chain.E n} (hz : z ∈ S) : ⟪u - p, z - p⟫_ℝ ≤ 0 := by
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

theorem nc14_optSet_convex {n : ℕ} {X : Set (NecoaraNG.Chain.E n)} (hXconv : Convex ℝ X)
    {f : NecoaraNG.Chain.E n → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    Convex ℝ (NecoaraNG.Chain.optSet X f) := by
  intro a ha b hb θ η hθ hη hθη
  refine ⟨hXconv ha.1 hb.1 hθ hη hθη, fun z hz => ?_⟩
  have h1 := hf.2 (Set.mem_univ a) (Set.mem_univ b) hθ hη hθη
  have hza := ha.2 z hz
  have hzb := hb.2 z hz
  simp only [smul_eq_mul] at h1
  have hsum : θ * f z + η * f z = f z := by rw [← add_mul, hθη, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hza hθ, mul_le_mul_of_nonneg_left hzb hη]

open scoped InnerProductSpace in
/-- Quasi-strong convexity everywhere gives quadratic functional growth at points of `X`. -/
theorem nc14_qg {n : ℕ} {X : Set (NecoaraNG.Chain.E n)} (hXconv : Convex ℝ X)
    {f : NecoaraNG.Chain.E n → ℝ} (hdiff : ∀ x, DifferentiableAt ℝ f x)
    (hf : ConvexOn ℝ Set.univ f)
    {κ : ℝ} (hκ : 0 < κ) (hqs : NecoaraNG.FGM.QuasiStrongEverywhere X f κ)
    {x xb : NecoaraNG.Chain.E n} (hx : x ∈ X)
    (hn : NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) x xb) :
    κ / 2 * ‖x - xb‖ ^ 2 ≤ f x - f xb := by
  have hF : ∀ z, HasGradientAt f (gradient f z) z := fun z => (hdiff z).hasGradientAt
  have hconvS := nc14_optSet_convex hXconv hf
  obtain ⟨d, hd⟩ : ∃ d, d = x - xb := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = κ / 2 * ‖d‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ, ∀ t, h t = f (xb + t • d) - f xb := ⟨_, fun t => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, ∀ t, G t = ⟪gradient f (xb + t • d), d⟫_ℝ :=
    ⟨_, fun t => rfl⟩
  have hnear : ∀ t : ℝ, 0 ≤ t →
      NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) (xb + t • d) xb := by
    intro t ht
    refine ⟨hn.1, fun z hz => ?_⟩
    have hv : ⟪d, z - xb⟫_ℝ ≤ 0 := by rw [hd]; exact nc14_proj_vi hconvS hn hz
    have e1 : xb + t • d - xb = t • d := by abel
    have e2 : xb + t • d - z = t • d - (z - xb) := by abel
    rw [e1, e2]
    have h2 : ‖t • d‖ ^ 2 ≤ ‖t • d - (z - xb)‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_left]
      nlinarith [sq_nonneg ‖z - xb‖, mul_nonneg ht (neg_nonneg.mpr hv)]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
  have hQS : ∀ t : ℝ, 0 ≤ t → h t - t * G t + c * t ^ 2 ≤ 0 := by
    intro t ht
    have q := hqs _ _ (hnear t ht)
    have e1 : xb - (xb + t • d) = (-t) • d := by rw [neg_smul]; abel
    have e2 : xb + t • d - xb = t • d := by abel
    rw [e1, e2, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at q
    rw [hh, hG, hc]
    linarith
  have hfo : ∀ s t : ℝ, h s + (t - s) * G s ≤ h t := by
    intro s t
    have q := nc14_convex_fo hF hf (xb + s • d) (xb + t • d)
    have e : xb + t • d - (xb + s • d) = (t - s) • d := by rw [sub_smul]; abel
    rw [e, real_inner_smul_right] at q
    rw [hh, hh, hG]
    linarith
  have hnn : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ h t := by
    intro t ht0 ht1
    have hmem : xb + t • d ∈ X := by
      rw [hd]; exact hXconv.add_smul_sub_mem hn.1.1 hx ⟨ht0, ht1⟩
    have := hn.1.2 _ hmem
    rw [hh]
    linarith
  have hstep : ∀ s t : ℝ, 0 < s → s ≤ t → t * h s + (t - s) * s ^ 2 * c ≤ s * h t := by
    intro s t hs hst
    have q1 := hQS s hs.le
    have q2 := hfo s t
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
      have hst := hstep (r ^ (M + 1)) (r ^ M) hS (by rw [hSeq]; nlinarith)
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

open scoped InnerProductSpace in
/-- One projected gradient step: the gradient-mapping inequality. -/
theorem nc14_gm {n : ℕ} {X : Set (NecoaraNG.Chain.E n)} (hXconv : Convex ℝ X)
    {f : NecoaraNG.Chain.E n → ℝ} (hdiff : ∀ x, DifferentiableAt ℝ f x) {L : ℝ} (hL : 0 < L)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {y p : NecoaraNG.Chain.E n}
    (hp : NecoaraNG.Chain.IsNearest X (y - (1 / L) • gradient f y) p)
    {z : NecoaraNG.Chain.E n} (hz : z ∈ X) :
    f p + ⟪L • (y - p), z - y⟫_ℝ + 1 / (2 * L) * ‖L • (y - p)‖ ^ 2
      ≤ f y + ⟪gradient f y, z - y⟫_ℝ := by
  have hF : ∀ x, HasGradientAt f (gradient f x) x := fun x => (hdiff x).hasGradientAt
  have hdesc := nc14_descent hF hLip y p
  have hvi := nc14_proj_vi hXconv hp hz
  have e1 : y - (1 / L) • gradient f y - p = (y - p) - (1 / L) • gradient f y := by abel
  have e2 : z - p = (z - y) + (y - p) := by abel
  have e3 : p - y = -(y - p) := by abel
  rw [e1, e2, inner_sub_left, real_inner_smul_left, inner_add_right, inner_add_right,
    real_inner_self_eq_norm_sq] at hvi
  rw [e3, inner_neg_right, norm_neg] at hdesc
  rw [real_inner_smul_left, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hL' : 1 / (2 * L) * (L ^ 2 * ‖y - p‖ ^ 2) = L / 2 * ‖y - p‖ ^ 2 := by
    rw [one_div_mul_eq_div, div_eq_iff (mul_pos two_pos hL).ne']; ring
  rw [hL']
  have hvi2 : ⟪y - p, z - y⟫_ℝ + ‖y - p‖ ^ 2
      ≤ (⟪gradient f y, z - y⟫_ℝ + ⟪gradient f y, y - p⟫_ℝ) / L := by
    rw [div_eq_mul_one_div, mul_comm]; linarith
  rw [le_div_iff₀ hL] at hvi2
  nlinarith

open scoped InnerProductSpace in
/-- The Lyapunov step of (FGM), as pure algebra. -/
theorem nc14_core {n : ℕ} (L α fa fp fs : ℝ) (a y s p : NecoaraNG.Chain.E n)
    (hL : 0 < L) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hA : fp + ⟪L • (y - p), s - y⟫_ℝ + 1 / (2 * L) * ‖L • (y - p)‖ ^ 2
      + α ^ 2 * L / 2 * ‖y - s‖ ^ 2 ≤ fs)
    (hB : fp + ⟪L • (y - p), a - y⟫_ℝ + 1 / (2 * L) * ‖L • (y - p)‖ ^ 2 ≤ fa) :
    fp - fs + L / 2 * ‖p - (1 - α) • a - α • s‖ ^ 2
      ≤ (1 - α) * (fa - fs + L / 2 * ‖(1 + α) • y - a - α • s‖ ^ 2) := by
  have e : 1 / (2 * L) * ‖L • (y - p)‖ ^ 2 = L / 2 * ‖y - p‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, one_div_mul_eq_div,
      div_eq_iff (mul_pos two_pos hL).ne']
    ring
  rw [e] at hA hB
  have hq : 0 ≤ ‖y - a‖ ^ 2 := sq_nonneg _
  have hA' := mul_le_mul_of_nonneg_left hA hα0
  have hB' := mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr hα1)
  have hq' := mul_nonneg (mul_nonneg (mul_nonneg hL.le hα0) (sub_nonneg.mpr hα1)) hq
  simp only [← real_inner_self_eq_norm_sq] at hA' hB' hq' ⊢
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_right, real_inner_comm] at hA' hB' hq' ⊢
  nlinarith [hA', hB', hq']

open scoped InnerProductSpace in
open NecoaraNG.FGM in
theorem solution {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hdiff : ∀ x, DifferentiableAt ℝ f x) (hf : ConvexOn ℝ Set.univ f)
    (Lf : ℝ) (hLf : 0 < Lf) (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hqs : QuasiStrongEverywhere X f κ)
    (x y : ℕ → NecoaraNG.Chain.E n)
    (hrun : IsFGMRun X f Lf ((Real.sqrt Lf - Real.sqrt κ) / (Real.sqrt Lf + Real.sqrt κ)) x y)
    (ystar : NecoaraNG.Chain.E n) (hsame : ∀ k, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) (y k) ystar) :
    ∀ k : ℕ, f (x k) - f xstar ≤ (1 - Real.sqrt (κ / Lf)) ^ k * (2 * (f (x 0) - f xstar)) := by
  intro k
  have hF : ∀ z, HasGradientAt f (gradient f z) z := fun z => (hdiff z).hasGradientAt
  obtain ⟨hx0, hy0, hstep⟩ := hrun
  have hxX : ∀ j, x j ∈ X := by
    intro j
    cases j with
    | zero => exact hx0
    | succ j => exact (hstep j).1.1
  have hys : ystar ∈ NecoaraNG.Chain.optSet X f := (hsame 0).1
  have hfeq : f ystar = f xstar := le_antisymm (hys.2 _ hxstar.1) (hxstar.2 _ hys.1)
  rw [← hfeq]
  have hA : ∀ j, f (x (j + 1)) + ⟪Lf • (y j - x (j + 1)), ystar - y j⟫_ℝ
      + 1 / (2 * Lf) * ‖Lf • (y j - x (j + 1))‖ ^ 2 + κ / 2 * ‖y j - ystar‖ ^ 2
        ≤ f ystar := by
    intro j
    have g := nc14_gm hXconv hdiff hLf hL (hstep j).1 hys.1
    have q := hqs (y j) ystar (hsame j)
    linarith
  have hB : ∀ j, f (x (j + 1)) + ⟪Lf • (y j - x (j + 1)), x j - y j⟫_ℝ
      + 1 / (2 * Lf) * ‖Lf • (y j - x (j + 1))‖ ^ 2 ≤ f (x j) := by
    intro j
    have g := nc14_gm hXconv hdiff hLf hL (hstep j).1 (hxX j)
    have q := nc14_convex_fo hF hf (y j) (x j)
    linarith
  have hn0 : NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) (x 0) ystar := by
    rw [← hy0]; exact hsame 0
  have hqg := nc14_qg hXconv hdiff hf hκ hqs hx0 hn0
  by_cases hκL : κ ≤ Lf
  · set α := Real.sqrt (κ / Lf) with hα
    have hα0 : 0 < α := Real.sqrt_pos.mpr (div_pos hκ hLf)
    have hα1 : α ≤ 1 := by
      rw [hα, ← Real.sqrt_one]
      exact Real.sqrt_le_sqrt ((div_le_one hLf).mpr hκL)
    have hα2 : α ^ 2 = κ / Lf := Real.sq_sqrt (div_pos hκ hLf).le
    have hκα : κ = α ^ 2 * Lf := by rw [hα2, div_mul_cancel₀ κ hLf.ne']
    have hsL : 0 < Real.sqrt Lf := Real.sqrt_pos.mpr hLf
    have hsk : Real.sqrt κ = α * Real.sqrt Lf := by
      rw [hα, Real.sqrt_div hκ.le, div_mul_cancel₀ _ hsL.ne']
    have hβ : (1 + α) * ((Real.sqrt Lf - Real.sqrt κ) / (Real.sqrt Lf + Real.sqrt κ))
        = 1 - α := by
      rw [hsk]
      have hden : Real.sqrt Lf + α * Real.sqrt Lf ≠ 0 :=
        (show (0 : ℝ) < Real.sqrt Lf + α * Real.sqrt Lf by
          have := mul_pos hα0 hsL; linarith).ne'
      rw [mul_div_assoc', div_eq_iff hden]; ring
    obtain ⟨V, hV⟩ : ∃ V : ℕ → ℝ, ∀ j, V j = f (x j) - f ystar
        + Lf / 2 * ‖(1 + α) • y j - x j - α • ystar‖ ^ 2 := ⟨_, fun j => rfl⟩
    have hVstep : ∀ j, V (j + 1) ≤ (1 - α) * V j := by
      intro j
      have hw : (1 + α) • y (j + 1) - x (j + 1) - α • ystar
          = x (j + 1) - (1 - α) • x j - α • ystar := by
        rw [(hstep j).2, smul_add, smul_smul, hβ]; module
      rw [hV, hV, hw]
      have hAj := hA j
      rw [hκα] at hAj
      exact nc14_core Lf α (f (x j)) (f (x (j + 1))) (f ystar) (x j) (y j) ystar (x (j + 1))
        hLf hα0.le hα1 hAj (hB j)
    have hVk : ∀ j, V j ≤ (1 - α) ^ j * V 0 := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc V (j + 1) ≤ (1 - α) * V j := hVstep j
          _ ≤ (1 - α) * ((1 - α) ^ j * V 0) := mul_le_mul_of_nonneg_left ih (by linarith)
          _ = (1 - α) ^ (j + 1) * V 0 := by ring
    have hV0 : V 0 ≤ 2 * (f (x 0) - f ystar) := by
      rw [hV, hy0]
      have e : (1 + α) • x 0 - x 0 - α • ystar = α • (x 0 - ystar) := by module
      rw [e, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have hq := hqg
      rw [hκα] at hq
      nlinarith
    have hfV : f (x k) - f ystar ≤ V k := by
      rw [hV]
      nlinarith [mul_nonneg hLf.le (sq_nonneg ‖(1 + α) • y k - x k - α • ystar‖)]
    calc f (x k) - f ystar ≤ V k := hfV
      _ ≤ (1 - α) ^ k * V 0 := hVk k
      _ ≤ (1 - α) ^ k * (2 * (f (x 0) - f ystar)) :=
        mul_le_mul_of_nonneg_left hV0 (pow_nonneg (by linarith) k)
  · push Not at hκL
    have hyeq : ∀ j, y j = ystar := by
      intro j
      have q := hqs (y j) ystar (hsame j)
      have d := nc14_descent hF hL (y j) ystar
      have hn : ‖ystar - y j‖ = ‖y j - ystar‖ := norm_sub_rev _ _
      rw [hn] at d
      have hN : ‖y j - ystar‖ ^ 2 ≤ 0 := by
        by_contra hc
        push Not at hc
        nlinarith [mul_pos (sub_pos.mpr hκL) hc]
      have h0 : ‖y j - ystar‖ ^ 2 = 0 := le_antisymm hN (sq_nonneg _)
      have h1 : ‖y j - ystar‖ = 0 := pow_eq_zero_iff two_ne_zero |>.mp h0
      exact sub_eq_zero.mp (norm_eq_zero.mp h1)
    have hx0eq : x 0 = ystar := by rw [← hy0]; exact hyeq 0
    have hle : f (x k) ≤ f ystar := by
      cases k with
      | zero => rw [hx0eq]
      | succ j =>
        have a := hA j
        rw [hyeq j] at a
        simp only [sub_self, inner_zero_right, norm_zero] at a
        have : 0 ≤ 1 / (2 * Lf) * ‖Lf • (ystar - x (j + 1))‖ ^ 2 :=
          mul_nonneg (one_div_nonneg.mpr (by linarith)) (sq_nonneg _)
        nlinarith
    simp only [hx0eq, sub_self, mul_zero]
    linarith
