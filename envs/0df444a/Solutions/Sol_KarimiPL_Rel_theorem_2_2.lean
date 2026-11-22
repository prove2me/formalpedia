-- Prove2me | solution 2 for KarimiPL.Rel.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:01:42.467325+00:00
-- url     : https://prove2.me/submissions/018f3fba-116d-4f59-b06a-02a25056368a

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_KarimiPL_Rel_Conditions

namespace RRAux_KarimiPL_Rel_theorem_2

open scoped InnerProductSpace
open KarimiPL.Rel Filter Topology

variable {d : ℕ}

theorem grad_inner (f : E d → ℝ) (x v : E d) :
    fderiv ℝ f x v = ⟪gradient f x, v⟫_ℝ := by
  unfold gradient; exact InnerProductSpace.toDual_symm_apply.symm

theorem descent (f : E d → ℝ) (L : ℝ) (hd : Differentiable ℝ f)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x y : E d) :
    f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x with hw
  set ψ : ℝ → ℝ := fun t => f (x + t • w) - t * ⟪gradient f x, w⟫_ℝ - L / 2 * t ^ 2 * ‖w‖ ^ 2
    with hψ
  have hder : ∀ t, HasDerivAt ψ (⟪gradient f (x + t • w), w⟫_ℝ - ⟪gradient f x, w⟫_ℝ
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have hl : HasDerivAt (fun t : ℝ => x + t • w) w t := by
      simpa using ((hasDerivAt_id t).smul_const w).const_add x
    have hc := (hd (x + t • w)).hasFDerivAt.comp_hasDerivAt t hl
    rw [grad_inner f] at hc
    have h2 : HasDerivAt (fun t : ℝ => t * ⟪gradient f x, w⟫_ℝ) ⟪gradient f x, w⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, w⟫_ℝ
    have h3 : HasDerivAt (fun t : ℝ => L / 2 * t ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (hc.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro t _; exact (hder t).continuousAt.continuousWithinAt
    · intro t _; exact (hder t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hder t).deriv]
      have h1 := real_inner_le_norm (gradient f (x + t • w) - gradient f x) w
      have h2 := hlip (x + t • w) x
      have e : x + t • w - x = t • w := by abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at h2
      rw [inner_sub_left] at h1
      have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg w)
      nlinarith
  have := hanti (show (0:ℝ) ∈ Set.Ici 0 from Set.mem_Ici.2 le_rfl)
    (show (1:ℝ) ∈ Set.Ici 0 from Set.mem_Ici.2 zero_le_one) zero_le_one
  simp only [hψ, zero_smul, add_zero, one_smul, zero_mul, sub_zero, one_mul] at this
  have e : x + w = y := by rw [hw]; abel
  rw [e] at this
  norm_num at this
  rw [grad_inner f] at this
  linarith

theorem grad_zero (f : E d → ℝ) (z : E d) (hz : ∀ y, f z ≤ f y) : gradient f z = 0 := by
  have hlm : IsLocalMin f z := Filter.Eventually.of_forall hz
  unfold gradient
  rw [hlm.fderiv_eq_zero, map_zero]

theorem conv_grad (f : E d → ℝ) (hc : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f)
    (x y : E d) : f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y := by
  have hg : ConvexOn ℝ Set.univ (f ∘ AffineMap.lineMap (k := ℝ) x y) := by
    have := hc.comp_affineMap (AffineMap.lineMap (k := ℝ) x y)
    simpa using this
  have hl : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y - x)).const_add x
  have hfx : HasFDerivAt f (fderiv ℝ f x) (x + (0:ℝ) • (y - x)) := by
    simpa using (hd x).hasFDerivAt
  have hcomp := hfx.comp_hasDerivAt (0:ℝ) hl
  have e : (f ∘ AffineMap.lineMap (k := ℝ) x y) = fun t : ℝ => f (x + t • (y - x)) := by
    funext t; simp [AffineMap.lineMap_apply, add_comm]
  have hd' : HasDerivAt (f ∘ AffineMap.lineMap (k := ℝ) x y) ⟪gradient f x, y - x⟫_ℝ 0 := by
    rw [e, ← grad_inner f]; exact hcomp
  have := hg.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd'
  rw [slope_def_field, e] at this
  have e1 : x + (1:ℝ) • (y - x) = y := by rw [one_smul]; abel
  simp only [e1, zero_smul, add_zero, sub_zero, div_one] at this
  linarith

theorem pp (f : E d → ℝ) (p : E d → E d) (hp : IsProjSel f p) (x : E d) : p (p x) = p x := by
  obtain ⟨_, h2⟩ := hp (p x)
  rw [Metric.infDist_zero_of_mem (hp x).1, norm_eq_zero, sub_eq_zero] at h2
  exact h2.symm

theorem fp (f : E d → ℝ) (p : E d → E d) (hp : IsProjSel f p) (xstar : E d)
    (hxstar : ∀ y, f xstar ≤ f y) (x : E d) : f (p x) = f xstar :=
  le_antisymm ((hp x).1 xstar) (hxstar _)

theorem sqrt_step (a b G L m : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hL : 0 < L) (hm : 0 ≤ m)
    (hG : 0 ≤ G) (h1 : b ≤ a - G ^ 2 / (2 * L)) (h2 : m ^ 2 * a ≤ G ^ 2) :
    G * m ≤ 4 * L * (Real.sqrt a - Real.sqrt b) := by
  set u := Real.sqrt a with hu
  set v := Real.sqrt b with hv
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hua : u ^ 2 = a := Real.sq_sqrt ha
  have hvb : v ^ 2 = b := Real.sq_sqrt hb
  have h1' : G ^ 2 ≤ 2 * L * (u ^ 2 - v ^ 2) := by
    rw [hua, hvb]
    have : G ^ 2 / (2 * L) ≤ a - b := by linarith
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hmu : m * u ≤ G := by
    have : (m * u) ^ 2 ≤ G ^ 2 := by rw [mul_pow, hua]; exact h2
    exact (pow_le_pow_iff_left₀ (mul_nonneg hm hu0) hG (by norm_num)).1 this
  have hvu : v ≤ u := by
    have h0 : 0 ≤ 2 * L * (u ^ 2 - v ^ 2) := le_trans (sq_nonneg G) h1'
    have h0' : 0 ≤ u ^ 2 - v ^ 2 := (mul_nonneg_iff_of_pos_left (by linarith)).1 h0
    exact (pow_le_pow_iff_left₀ hv0 hu0 (by norm_num : (2:ℕ) ≠ 0)).1 (by linarith)
  -- G * m * (u + v) ≤ 2 G² ≤ 4 L (u - v)(u + v)
  have k1 : G * m * (u + v) ≤ 2 * G ^ 2 := by
    have : m * (u + v) ≤ 2 * G := by nlinarith
    nlinarith
  have k2 : 2 * G ^ 2 ≤ 4 * L * (u - v) * (u + v) := by nlinarith
  rcases (add_nonneg hu0 hv0).lt_or_eq with hpos | hzero
  · have : G * m * (u + v) ≤ 4 * L * (u - v) * (u + v) := k1.trans k2
    have := le_of_mul_le_mul_right (by linarith : G * m * (u + v) ≤ 4 * L * (u - v) * (u + v)) hpos
    linarith
  · have hu' : u = 0 := by linarith
    have hv' : v = 0 := by linarith
    rw [hu', hv'] at h1'
    have : G = 0 := by nlinarith
    rw [this, hu', hv']; simp

/-- PL implies QG, through the path length of gradient descent with step `1/L`. -/
theorem pl_qg_dist (f : E d → ℝ) (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (fstar : ℝ)
    (hfs : ∀ y, fstar ≤ f y) (μ : ℝ) (hμ : 0 < μ)
    (hPL : ∀ x, 2 * μ * (f x - fstar) ≤ ‖gradient f x‖ ^ 2) (x0 : E d) :
    ∃ z, (∀ y, f z ≤ f y) ∧
      Real.sqrt (2 * μ) * ‖x0 - z‖ ≤ 4 * Real.sqrt (f x0 - fstar) := by
  set m := Real.sqrt (2 * μ) with hm
  have hm0 : 0 < m := Real.sqrt_pos.2 (by positivity)
  have hm2 : m ^ 2 = 2 * μ := Real.sq_sqrt (by positivity)
  let xs : ℕ → E d := fun k => Nat.rec x0 (fun _ y => y - (1 / L) • gradient f y) k
  have hxs0 : xs 0 = x0 := rfl
  have hxs : ∀ k, xs (k + 1) = xs k - (1 / L) • gradient f (xs k) := fun k => rfl
  set s : ℕ → ℝ := fun k => Real.sqrt (f (xs k) - fstar) with hs
  set D : ℕ → ℝ := fun k => ‖gradient f (xs k)‖ / L with hD
  have hdesc : ∀ k, f (xs (k + 1)) ≤ f (xs k) - ‖gradient f (xs k)‖ ^ 2 / (2 * L) := by
    intro k
    have := descent f L hdiff hLip (xs k) (xs (k + 1))
    rw [hxs k] at this
    have e : xs k - (1 / L) • gradient f (xs k) - xs k = -((1 / L) • gradient f (xs k)) := by abel
    rw [e, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_neg,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at this
    have e2 : -(1 / L * ‖gradient f (xs k)‖ ^ 2) + L / 2 * ((1 / L) ^ 2 * ‖gradient f (xs k)‖ ^ 2)
        = -(‖gradient f (xs k)‖ ^ 2 / (2 * L)) := by field_simp; ring
    linarith
  have hDs : ∀ k, D k * m ≤ 4 * (s k - s (k + 1)) := by
    intro k
    have h := sqrt_step (f (xs k) - fstar) (f (xs (k + 1)) - fstar) ‖gradient f (xs k)‖ L m
      (sub_nonneg.2 (hfs _)) (sub_nonneg.2 (hfs _)) hL hm0.le (norm_nonneg _)
      (by linarith [hdesc k]) (by rw [hm2]; exact hPL _)
    simp only [hD, hs]
    rw [div_mul_eq_mul_div, div_le_iff₀ hL]
    linarith
  have hdist : ∀ k, dist (xs k) (xs k.succ) ≤ D k := by
    intro k
    rw [dist_eq_norm, Nat.succ_eq_add_one, hxs k]
    simp only [hD, sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.2 hL)]
    rw [one_div_mul_eq_div]
  have hD0 : ∀ k, 0 ≤ D k := fun k => by positivity
  have hsum_le : ∀ n, ∑ i ∈ Finset.range n, D i ≤ 4 / m * s 0 := by
    intro n
    have htel : ∀ n, ∑ i ∈ Finset.range n, D i * m ≤ 4 * (s 0 - s n) := by
      intro n
      induction n with
      | zero => simp
      | succ j ih => rw [Finset.sum_range_succ]; linarith [hDs j]
    have h1 := htel n
    rw [← Finset.sum_mul] at h1
    have hsn : 0 ≤ s n := Real.sqrt_nonneg _
    rw [div_mul_eq_mul_div, le_div_iff₀ hm0]
    linarith
  have hsumm : Summable D := summable_of_sum_range_le hD0 hsum_le
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_dist_le_of_summable D hdist hsumm)
  have hdz := dist_le_tsum_of_dist_le_of_tendsto₀ D hdist hsumm hz
  have htsum : ∑' n, D n ≤ 4 / m * s 0 := Real.tsum_le_of_sum_range_le hD0 hsum_le
  -- f z = fstar
  have hDt : Tendsto D atTop (𝓝 0) := hsumm.tendsto_atTop_zero
  have hGt : Tendsto (fun k => (L * D k) ^ 2 / (2 * μ)) atTop (𝓝 0) := by
    have := ((hDt.const_mul L).pow 2).div_const (2 * μ)
    simpa using this
  have hft : Tendsto (fun k => f (xs k) - fstar) atTop (𝓝 (f z - fstar)) :=
    ((hdiff.continuous.tendsto z).comp hz).sub_const fstar
  have hle : ∀ k, f (xs k) - fstar ≤ (L * D k) ^ 2 / (2 * μ) := by
    intro k
    have : L * D k = ‖gradient f (xs k)‖ := by simp only [hD]; field_simp
    rw [this, le_div_iff₀ (by positivity)]
    linarith [hPL (xs k)]
  have hfz : f z - fstar ≤ 0 := le_of_tendsto_of_tendsto' hft hGt hle
  refine ⟨z, fun y => by linarith [hfs y], ?_⟩
  rw [hxs0] at hdz
  rw [dist_eq_norm] at hdz
  have h3 : ‖x0 - z‖ ≤ 4 / m * s 0 := hdz.trans htsum
  rw [div_mul_eq_mul_div, le_div_iff₀ hm0] at h3
  simp only [hs, hxs0] at h3
  linarith

theorem pl_qg (f : E d → ℝ) (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (xstar : E d) (hxstar : ∀ y, f xstar ≤ f y) (p : E d → E d) (hp : IsProjSel f p)
    (μ : ℝ) (hμ : 0 < μ) (hPL : ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f xstar)) :
    QG f p (f xstar) (μ / 4) := by
  intro x
  obtain ⟨z, hz, hdz⟩ := pl_qg_dist f hdiff L hL hLip (f xstar) hxstar μ hμ hPL x
  have h1 : ‖p x - x‖ ≤ ‖x - z‖ := by
    rw [norm_sub_rev, (hp x).2, ← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem hz
  have hm2 : Real.sqrt (2 * μ) ^ 2 = 2 * μ := Real.sq_sqrt (by positivity)
  have hs2 : Real.sqrt (f x - f xstar) ^ 2 = f x - f xstar := Real.sq_sqrt (sub_nonneg.2 (hxstar _))
  have hm0 : 0 ≤ Real.sqrt (2 * μ) := Real.sqrt_nonneg _
  have h2 : Real.sqrt (2 * μ) * ‖p x - x‖ ≤ 4 * Real.sqrt (f x - f xstar) :=
    (mul_le_mul_of_nonneg_left h1 hm0).trans hdz
  have h3 : (Real.sqrt (2 * μ) * ‖p x - x‖) ^ 2 ≤ (4 * Real.sqrt (f x - f xstar)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  rw [mul_pow, mul_pow, hm2, hs2] at h3
  nlinarith

theorem eb_pl (f : E d → ℝ) (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (xstar : E d) (hxstar : ∀ y, f xstar ≤ f y) (p : E d → E d) (hp : IsProjSel f p)
    (μ : ℝ) (hμ : 0 < μ) (hEB : EB f p μ) :
    ShiOptRates.PolyakLojasiewicz f (gradient f) (μ ^ 2 / L) (f xstar) := by
  intro x
  have h1 := descent f L hdiff hLip (p x) x
  rw [grad_zero f (p x) (hp x).1, inner_zero_left, fp f p hp xstar hxstar] at h1
  have h2 := hEB x
  rw [norm_sub_rev] at h2
  have h3 : (μ * ‖x - p x‖) ^ 2 ≤ ‖gradient f x‖ ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  have e : 2 * (μ ^ 2 / L) * (f x - f xstar) ≤ 2 * (μ ^ 2 / L) * (L / 2 * ‖x - p x‖ ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e2 : 2 * (μ ^ 2 / L) * (L / 2 * ‖x - p x‖ ^ 2) = (μ * ‖x - p x‖) ^ 2 := by
    field_simp
  linarith

theorem pl_eb (f : E d → ℝ) (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (xstar : E d) (hxstar : ∀ y, f xstar ≤ f y) (p : E d → E d) (hp : IsProjSel f p)
    (μ : ℝ) (hμ : 0 < μ) (hPL : ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f xstar)) :
    EB f p (μ / 2) := by
  intro x
  have hq := pl_qg f hdiff L hL hLip xstar hxstar p hp μ hμ hPL x
  have h := hPL x
  have h3 : (μ / 2 * ‖p x - x‖) ^ 2 ≤ ‖gradient f x‖ ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) (by norm_num)).1 h3

theorem qg_pl (f : E d → ℝ) (hdiff : Differentiable ℝ f) (hc : ConvexOn ℝ Set.univ f)
    (xstar : E d) (hxstar : ∀ y, f xstar ≤ f y) (p : E d → E d) (hp : IsProjSel f p)
    (μ : ℝ) (hμ : 0 < μ) (hQG : QG f p (f xstar) μ) :
    ShiOptRates.PolyakLojasiewicz f (gradient f) (μ / 4) (f xstar) := by
  intro x
  have h1 := conv_grad f hc hdiff x (p x)
  rw [fp f p hp xstar hxstar] at h1
  have h2 : f x - f xstar ≤ ‖gradient f x‖ * ‖p x - x‖ := by
    have := real_inner_le_norm (gradient f x) (x - p x)
    have e : ⟪gradient f x, p x - x⟫_ℝ = -⟪gradient f x, x - p x⟫_ℝ := by
      rw [← inner_neg_right, neg_sub]
    rw [norm_sub_rev] at this
    rw [e] at h1
    linarith
  have h3 := hQG x
  set r := ‖p x - x‖
  set G := ‖gradient f x‖
  have hr : 0 ≤ r := norm_nonneg _
  have hG : 0 ≤ G := norm_nonneg _
  have hδ : 0 ≤ f x - f xstar := sub_nonneg.2 (hxstar _)
  have h4 : μ * r ≤ 2 * G := by
    rcases hr.lt_or_eq with hrp | hr0
    · have : μ / 2 * r ^ 2 ≤ G * r := h3.trans h2
      nlinarith
    · rw [← hr0]; linarith
  have h5 : μ * (f x - f xstar) ≤ μ * (G * r) := mul_le_mul_of_nonneg_left h2 hμ.le
  have h6 : μ * (G * r) ≤ G * (2 * G) := by nlinarith
  nlinarith

end RRAux_KarimiPL_Rel_theorem_2

open RRAux_KarimiPL_Rel_theorem_2
open scoped InnerProductSpace

open KarimiPL.Rel in
theorem solution {d : ℕ} (f : E d → ℝ) (hdiff : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L) (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (xstar : E d) (hxstar : ∀ y, f xstar ≤ f y)
    (p : E d → E d) (hp : IsProjSel f p) :
    (Holds (SC f) → Holds (ESC f p)) ∧
    (Holds (ESC f p) → Holds (WSC f p)) ∧
    (Holds (WSC f p) → Holds (RSI f p)) ∧
    (Holds (RSI f p) → Holds (EB f p)) ∧
    (Holds (EB f p) ↔ Holds (fun μ => ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f xstar))) ∧
    (Holds (fun μ => ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f xstar)) →
      Holds (QG f p (f xstar))) ∧
    (ConvexOn ℝ Set.univ f →
      (Holds (RSI f p) ↔ Holds (EB f p)) ∧
      (Holds (EB f p) ↔
        Holds (fun μ => ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f xstar))) ∧
      (Holds (fun μ => ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f xstar)) ↔
        Holds (QG f p (f xstar)))) := by
  have rsi_eb : Holds (RSI f p) → Holds (EB f p) := by
    rintro ⟨μ, hμ, h⟩
    refine ⟨μ, hμ, fun x => ?_⟩
    have h1 := h x
    have h2 := real_inner_le_norm (gradient f x) (x - p x)
    rw [norm_sub_rev x (p x)] at h2
    rcases (norm_nonneg (p x - x)).lt_or_eq with hpos | h0
    · have : μ * ‖p x - x‖ * ‖p x - x‖ ≤ ‖gradient f x‖ * ‖p x - x‖ := by nlinarith
      exact le_of_mul_le_mul_right this hpos
    · rw [← h0]; simp
  have eb_pl' : Holds (EB f p) →
      Holds (fun μ => ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f xstar)) := by
    rintro ⟨μ, hμ, h⟩
    exact ⟨μ ^ 2 / L, by positivity, eb_pl f hdiff L hL hLip xstar hxstar p hp μ hμ h⟩
  have pl_eb' : Holds (fun μ => ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f xstar)) →
      Holds (EB f p) := by
    rintro ⟨μ, hμ, h⟩
    exact ⟨μ / 2, by positivity, pl_eb f hdiff L hL hLip xstar hxstar p hp μ hμ h⟩
  have pl_qg' : Holds (fun μ => ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f xstar)) →
      Holds (QG f p (f xstar)) := by
    rintro ⟨μ, hμ, h⟩
    exact ⟨μ / 4, by positivity, pl_qg f hdiff L hL hLip xstar hxstar p hp μ hμ h⟩
  refine ⟨?_, ?_, ?_, rsi_eb, ⟨eb_pl', pl_eb'⟩, pl_qg', ?_⟩
  · rintro ⟨μ, hμ, h⟩
    exact ⟨μ, hμ, fun x y _ => h x y⟩
  · rintro ⟨μ, hμ, h⟩
    exact ⟨μ, hμ, fun x => h x (p x) (pp f p hp x).symm⟩
  · rintro ⟨μ, hμ, h⟩
    refine ⟨μ / 2, by positivity, fun x => ?_⟩
    have h1 := h x
    have h2 : f (p x) ≤ f x := (hp x).1 x
    have e : ⟪gradient f x, p x - x⟫_ℝ = -⟪gradient f x, x - p x⟫_ℝ := by
      rw [← inner_neg_right, neg_sub]
    rw [e] at h1
    linarith
  · intro hc
    have qg_pl' : Holds (QG f p (f xstar)) →
        Holds (fun μ => ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f xstar)) := by
      rintro ⟨μ, hμ, h⟩
      exact ⟨μ / 4, by positivity, qg_pl f hdiff hc xstar hxstar p hp μ hμ h⟩
    have qg_rsi : Holds (QG f p (f xstar)) → Holds (RSI f p) := by
      rintro ⟨μ, hμ, h⟩
      refine ⟨μ / 2, by positivity, fun x => ?_⟩
      have h1 := conv_grad f hc hdiff x (p x)
      rw [fp f p hp xstar hxstar] at h1
      have h2 := h x
      have e : ⟪gradient f x, p x - x⟫_ℝ = -⟪gradient f x, x - p x⟫_ℝ := by
        rw [← inner_neg_right, neg_sub]
      rw [e] at h1
      linarith
    refine ⟨⟨rsi_eb, fun h => qg_rsi (pl_qg' (eb_pl' h))⟩, ⟨eb_pl', pl_eb'⟩, ⟨pl_qg', qg_pl'⟩⟩

#print axioms solution
