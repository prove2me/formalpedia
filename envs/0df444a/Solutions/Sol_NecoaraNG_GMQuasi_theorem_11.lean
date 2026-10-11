-- Prove2me | solution 1 for NecoaraNG.GMQuasi.theorem_11
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T22:20:04.34882+00:00
-- url     : https://prove2.me/submissions/5dc1c0d4-7ccd-4475-b2e3-cf20b05183d4

import Mathlib
import Definitions.Def_NecoaraNG_GMIff_Setting

namespace RRAux_NecoaraNG_GMQuasi_theorem_11

open scoped InnerProductSpace

section
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem grad_inner (f : F → ℝ) (x v : F) :
    fderiv ℝ f x v = ⟪gradient f x, v⟫_ℝ := by
  unfold gradient; exact InnerProductSpace.toDual_symm_apply.symm

theorem line_deriv (f : F → ℝ) (x w : F) (t : ℝ) (hd : DifferentiableAt ℝ f (x + t • w)) :
    HasDerivAt (fun s : ℝ => f (x + s • w)) ⟪gradient f (x + t • w), w⟫_ℝ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have hc := hd.hasFDerivAt.comp_hasDerivAt t hl
  rw [grad_inner f] at hc
  exact hc

theorem first_order {X : Set F} (hXconv : Convex ℝ X) (f : F → ℝ) (hf : ConvexOn ℝ X f)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x) {x y : F} (hx : x ∈ X) (hy : y ∈ X) :
    f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y := by
  set φ : ℝ → ℝ := fun t => f (x + t • (y - x)) with hφ
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • (y - x) ∈ X := fun t ht =>
    hXconv.add_smul_sub_mem hx hy ht
  have hconv : ConvexOn ℝ (Set.Icc (0:ℝ) 1) φ := by
    refine ⟨convex_Icc 0 1, ?_⟩
    intro a ha b hb α β hα hβ hαβ
    have := hf.2 (hmem a ha) (hmem b hb) hα hβ hαβ
    have e : α • (x + a • (y - x)) + β • (x + b • (y - x))
        = x + (α • a + β • b) • (y - x) := by
      have : α • (x + a • (y - x)) + β • (x + b • (y - x))
          = (α + β) • x + (α * a + β * b) • (y - x) := by module
      rw [this, hαβ, one_smul, smul_eq_mul, smul_eq_mul]
    rw [e] at this
    simpa [hφ] using this
  have hd : HasDerivAt φ ⟪gradient f x, y - x⟫_ℝ 0 := by
    have := line_deriv f x (y - x) 0 (by simpa using hdiff x hx)
    simpa using this
  have := hconv.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hd
  have e1 : φ 1 = f y := by simp only [hφ, one_smul]; congr 1; abel
  have e0 : φ 0 = f x := by simp only [hφ, zero_smul, add_zero]
  rw [slope_def_field, e1, e0, sub_zero, div_one] at this
  linarith

theorem descentX {X : Set F} (hXconv : Convex ℝ X) (f : F → ℝ)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x) (L : ℝ)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {x y : F} (hx : x ∈ X) (hy : y ∈ X) :
    f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x with hw
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • w ∈ X := fun t ht =>
    hXconv.add_smul_sub_mem hx hy ht
  set ψ : ℝ → ℝ := fun t => f (x + t • w) - t * ⟪gradient f x, w⟫_ℝ - L / 2 * t ^ 2 * ‖w‖ ^ 2
    with hψ
  have hder : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ (⟪gradient f (x + t • w), w⟫_ℝ
      - ⟪gradient f x, w⟫_ℝ - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t ht
    have hc := line_deriv f x w t (hdiff _ (hmem t ht))
    have h2 : HasDerivAt (fun t : ℝ => t * ⟪gradient f x, w⟫_ℝ) ⟪gradient f x, w⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, w⟫_ℝ
    have h3 : HasDerivAt (fun t : ℝ => L / 2 * t ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (hc.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · intro t ht; exact (hder t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hder t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht' := Set.Ioo_subset_Icc_self ht
      rw [(hder t ht').deriv]
      have h1 := real_inner_le_norm (gradient f (x + t • w) - gradient f x) w
      have h2 := hL _ (hmem t ht') x hx
      have e : x + t • w - x = t • w := by abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1] at h2
      rw [inner_sub_left] at h1
      have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg w)
      nlinarith
  have := hanti (show (0:ℝ) ∈ Set.Icc 0 1 by simp) (show (1:ℝ) ∈ Set.Icc 0 1 by simp) zero_le_one
  simp only [hψ, zero_smul, add_zero, one_smul, zero_mul, sub_zero, one_mul] at this
  have e : x + w = y := by rw [hw]; abel
  rw [e] at this
  norm_num at this
  rw [grad_inner f] at this
  linarith

end

open NecoaraNG.Chain in
theorem proj_vi {n : ℕ} {S : Set (E n)} (hS : Convex ℝ S) {y p : E n} (h : IsNearest S y p) :
    ∀ z ∈ S, ⟪y - p, z - p⟫_ℝ ≤ 0 := by
  have hbdd : BddBelow (Set.range fun w : S => ‖y - (w : E n)‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have heq : ‖y - p‖ = ⨅ w : S, ‖y - (w : E n)‖ := by
    apply le_antisymm
    · haveI : Nonempty S := ⟨⟨p, h.1⟩⟩
      exact le_ciInf fun w => h.2 w w.2
    · exact ciInf_le hbdd ⟨p, h.1⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero hS h.1).1 heq

open NecoaraNG.Chain in
theorem exists_nearest {n : ℕ} {S : Set (E n)} (hne : S.Nonempty) (hc : IsClosed S)
    (hcv : Convex ℝ S) (u : E n) : ∃ p, IsNearest S u p := by
  obtain ⟨v, hv, heq⟩ := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hcv u
  have hbdd : BddBelow (Set.range fun w : S => ‖u - (w : E n)‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  exact ⟨v, hv, fun z hz => heq ▸ ciInf_le hbdd ⟨z, hz⟩⟩

open NecoaraNG.Chain in
theorem three_point {n : ℕ} {X : Set (E n)} (hXconv : Convex ℝ X) (f : E n → ℝ)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x) (L : ℝ) (hLp : 0 < L)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {x z xp : E n} (c : ℝ) (hx : x ∈ X) (hz : z ∈ X)
    (hp : IsNearest X (x - (1 / L) • gradient f x) xp)
    (hc : f x + ⟪gradient f x, z - x⟫_ℝ + c ≤ f z) :
    f xp ≤ f z + L / 2 * (‖x - z‖ ^ 2 - ‖xp - z‖ ^ 2) - c := by
  have hpX : xp ∈ X := hp.1
  have hd := descentX hXconv f hdiff L hL hx hpX
  have hvi := proj_vi hXconv hp z hz
  set g := gradient f x with hg
  set a := x - xp with ha
  set b := z - xp with hb
  have e1 : x - (1 / L) • g - xp = a - (1 / L) • g := by rw [ha]; abel
  have e2 : z - x = b - a := by rw [ha, hb]; abel
  have e3 : xp - x = -a := by rw [ha]; abel
  have e4 : x - z = a - b := by rw [ha, hb]; abel
  have e5 : xp - z = -b := by rw [hb]; abel
  rw [e1, inner_sub_left, inner_smul_left] at hvi
  rw [e2, inner_sub_right] at hc
  rw [e3, inner_neg_right, norm_neg] at hd
  rw [e4, e5, norm_neg, norm_sub_sq_real]
  simp only [RCLike.conj_to_real] at hvi
  have hm : L * ⟪a, b⟫_ℝ ≤ ⟪g, b⟫_ℝ := by
    have := mul_le_mul_of_nonneg_left hvi hLp.le
    rw [mul_sub, ← mul_assoc, mul_one_div_cancel hLp.ne', one_mul, mul_zero] at this
    linarith
  nlinarith

open NecoaraNG.Chain in
theorem nearest_segment {n : ℕ} {S : Set (E n)} (hS : Convex ℝ S) {x p : E n}
    (h : IsNearest S x p) {t : ℝ} (ht : 0 ≤ t) : IsNearest S (p + t • (x - p)) p := by
  refine ⟨h.1, fun z hz => ?_⟩
  have hvi := proj_vi hS h z hz
  have e : p + t • (x - p) - z = t • (x - p) - (z - p) := by abel
  have e2 : p + t • (x - p) - p = t • (x - p) := by abel
  rw [e, e2]
  have h1 : ‖t • (x - p)‖ ^ 2 ≤ ‖t • (x - p) - (z - p)‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_left]
    simp only [RCLike.conj_to_real]
    have : t * ⟪x - p, z - p⟫_ℝ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hvi
    nlinarith [sq_nonneg ‖z - p‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

theorem small_t (A K : ℝ) (hK : 0 ≤ K) (h : ∀ t : ℝ, 0 < t → t ≤ 1 → -(K * t) ≤ A) : 0 ≤ A := by
  by_contra hA
  push Not at hA
  set t := min 1 (-A / (2 * (K + 1))) with ht
  have hK1 : 0 < K + 1 := by linarith
  have htp : 0 < t := lt_min one_pos (div_pos (by linarith) (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ -A / (2 * (K + 1)) := min_le_right _ _
  have h1 := h t htp ht1
  have h2 : (K + 1) * t ≤ -A / 2 := by
    rw [le_div_iff₀ (by positivity)] at ht2; nlinarith
  nlinarith

open NecoaraNG.Chain in
theorem qfg_of_qs {n : ℕ} {X : Set (E n)} (hXconv : Convex ℝ X) (f : E n → ℝ)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x) (hoptv : Convex ℝ (optSet X f))
    (κ : ℝ) (hκ : 0 < κ) (hqs : QuasiStrong X f κ) : QuadFunGrowth X f κ := by
  intro x hx xbar hxbar
  have hxbX : xbar ∈ X := hxbar.1.1
  set w := x - xbar with hw
  set d2 := ‖x - xbar‖ ^ 2 with hd2
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, xbar + t • w ∈ X := fun t ht =>
    hXconv.add_smul_sub_mem hxbX hx ht
  set g : ℝ → ℝ := fun t => (f (xbar + t • w) - f xbar - κ / 2 * d2 * t ^ 2) / t with hg
  have hder : ∀ t, 0 < t → t ≤ 1 → HasDerivAt g
      (((⟪gradient f (xbar + t • w), w⟫_ℝ - κ / 2 * d2 * (2 * t)) * t
        - (f (xbar + t • w) - f xbar - κ / 2 * d2 * t ^ 2) * 1) / t ^ 2) t := by
    intro t ht0 ht1
    have hc := line_deriv f xbar w t (hdiff _ (hmem t ⟨ht0.le, ht1⟩))
    have h3 : HasDerivAt (fun t : ℝ => κ / 2 * d2 * t ^ 2) (κ / 2 * d2 * (2 * t)) t := by
      have := (hasDerivAt_pow 2 t).const_mul (κ / 2 * d2)
      simpa using this
    have hnum := (hc.sub_const (f xbar)).sub h3
    exact hnum.div (hasDerivAt_id t) ht0.ne'
  have hmono : MonotoneOn g (Set.Ioc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 1)
    · intro t ht; exact (hder t ht.1 ht.2).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      exact (hder t ht.1 ht.2.le).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      rw [(hder t ht.1 ht.2.le).deriv]
      apply div_nonneg _ (by positivity)
      have hq := hqs (xbar + t • w) (hmem t ⟨ht.1.le, ht.2.le⟩) xbar
        (nearest_segment hoptv hxbar ht.1.le)
      have e1 : xbar - (xbar + t • w) = -(t • w) := by abel
      have e2 : xbar + t • w - xbar = t • w := by abel
      rw [e1, e2, inner_neg_right, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs] at hq
      nlinarith
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → -(κ / 2 * d2 * t) ≤ f x - f xbar - κ / 2 * d2 := by
    intro t ht0 ht1
    have hm := hmono ⟨ht0, ht1⟩ ⟨one_pos, le_rfl⟩ ht1
    have hfopt : f xbar ≤ f (xbar + t • w) := hxbar.1.2 _ (hmem t ⟨ht0.le, ht1⟩)
    have e : xbar + (1:ℝ) • w = x := by rw [one_smul, hw]; abel
    simp only [hg, e, one_pow, mul_one, div_one] at hm
    rw [div_le_iff₀ ht0] at hm
    have : -(κ / 2 * d2 * t) * t ≤ f (xbar + t • w) - f xbar - κ / 2 * d2 * t ^ 2 := by nlinarith
    nlinarith
  have := small_t (f x - f xbar - κ / 2 * d2) (κ / 2 * d2) (by positivity) key
  linarith

end RRAux_NecoaraNG_GMQuasi_theorem_11

open scoped InnerProductSpace
open RRAux_NecoaraNG_GMQuasi_theorem_11

theorem solution {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hqs : NecoaraNG.Chain.QuasiStrong X f κ)
    (x : ℕ → NecoaraNG.Chain.E n) (hrun : NecoaraNG.GMIff.IsGMRun X f (fun _ => 1 / Lf) x) :
    ∀ k : ℕ, ∀ xkbar x0bar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) (x k) xkbar →
      NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) (x 0) x0bar →
        ‖x k - xkbar‖ ^ 2 ≤ ((1 - κ / Lf) / (1 + κ / Lf)) ^ k * ‖x 0 - x0bar‖ ^ 2 := by
  have hcont : ContinuousOn f X := fun y hy => (hdiff y hy).continuousAt.continuousWithinAt
  have hopt : NecoaraNG.Chain.optSet X f = X ∩ f ⁻¹' Set.Iic (f xstar) := by
    ext y
    constructor
    · intro h; exact ⟨h.1, h.2 xstar hxstar.1⟩
    · intro h; exact ⟨h.1, fun z hz => le_trans h.2 (hxstar.2 z hz)⟩
  have hoptc : IsClosed (NecoaraNG.Chain.optSet X f) := by
    rw [hopt]; exact hcont.preimage_isClosed_of_isClosed hXc isClosed_Iic
  have hoptv : Convex ℝ (NecoaraNG.Chain.optSet X f) := by
    rw [hopt]; exact hf.convex_le (f xstar)
  have hqfg := qfg_of_qs hXconv f hdiff hoptv κ hκ hqs
  have hxX : ∀ k, x k ∈ X := by
    intro k
    cases k with
    | zero => exact hrun.1
    | succ k => exact (hrun.2 k).1
  have hex : ∀ k, ∃ p, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) (x k) p :=
    fun k => exists_nearest ⟨xstar, hxstar⟩ hoptc hoptv (x k)
  -- one step
  have step : ∀ k p p', NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) (x k) p →
      NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) (x (k + 1)) p' →
      (Lf + κ) * ‖x (k + 1) - p'‖ ^ 2 ≤ (Lf - κ) * ‖x k - p‖ ^ 2 := by
    intro k p p' hp hp'
    have hpX : p ∈ X := hp.1.1
    have hq := hqs (x k) (hxX k) p hp
    have tp := three_point hXconv f hdiff Lf hLf hL (κ / 2 * ‖x k - p‖ ^ 2) (hxX k) hpX
      (hrun.2 k) hq
    have hg := hqfg (x (k + 1)) (hxX (k + 1)) p' hp'
    have h1 : f p ≤ f p' := hp.1.2 p' hp'.1.1
    have h2 : f p' ≤ f p := hp'.1.2 p hpX
    have h3 : ‖x (k + 1) - p'‖ ≤ ‖x (k + 1) - p‖ := hp'.2 p hp.1
    have h4 : ‖x (k + 1) - p'‖ ^ 2 ≤ ‖x (k + 1) - p‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    nlinarith
  have hq : (1 - κ / Lf) / (1 + κ / Lf) = (Lf - κ) / (Lf + κ) := by
    field_simp
  rw [hq]
  have hLk : 0 < Lf + κ := by linarith
  rcases le_or_gt κ Lf with hkl | hkl
  · have hq0 : 0 ≤ (Lf - κ) / (Lf + κ) := div_nonneg (by linarith) hLk.le
    intro k
    induction k with
    | zero =>
      intro xkbar x0bar h h0
      simp only [pow_zero, one_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) (h.2 x0bar h0.1) 2
    | succ k ih =>
      intro xkbar x0bar h h0
      obtain ⟨p, hp⟩ := hex k
      have := step k p xkbar hp h
      have ih' := ih p x0bar hp h0
      have h5 : ‖x (k + 1) - xkbar‖ ^ 2 ≤ (Lf - κ) / (Lf + κ) * ‖x k - p‖ ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hLk]; linarith
      calc ‖x (k + 1) - xkbar‖ ^ 2 ≤ (Lf - κ) / (Lf + κ) * ‖x k - p‖ ^ 2 := h5
        _ ≤ (Lf - κ) / (Lf + κ) * (((Lf - κ) / (Lf + κ)) ^ k * ‖x 0 - x0bar‖ ^ 2) :=
          mul_le_mul_of_nonneg_left ih' hq0
        _ = _ := by ring
  · -- κ > Lf: everything is already optimal
    intro k xkbar x0bar h h0
    obtain ⟨p1, hp1⟩ := hex 1
    have s0 := step 0 x0bar p1 h0 hp1
    have hD0 : ‖x 0 - x0bar‖ ^ 2 = 0 := by
      have : 0 ≤ ‖x (0 + 1) - p1‖ ^ 2 := sq_nonneg _
      have h' : 0 ≤ ‖x 0 - x0bar‖ ^ 2 := sq_nonneg _
      nlinarith
    rw [hD0, mul_zero]
    cases k with
    | zero =>
      have := pow_le_pow_left₀ (norm_nonneg _) (h.2 x0bar h0.1) 2
      linarith
    | succ j =>
      obtain ⟨p, hp⟩ := hex j
      have := step j p xkbar hp h
      have h' : 0 ≤ ‖x j - p‖ ^ 2 := sq_nonneg _
      have h'' : 0 ≤ ‖x (j + 1) - xkbar‖ ^ 2 := sq_nonneg _
      nlinarith

#print axioms solution
