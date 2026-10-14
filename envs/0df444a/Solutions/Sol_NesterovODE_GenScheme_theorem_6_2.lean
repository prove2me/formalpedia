-- Prove2me | solution 2 for NesterovODE.GenScheme.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:12:49.864989+00:00
-- url     : https://prove2.me/submissions/6355c079-4fa8-422e-81ce-6790030db8ba

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_NesterovFB_Rates_Algorithm
import Definitions.Def_NesterovODE_GenScheme_Run

namespace RRAux_NesterovODE_GenScheme_theorem_6

open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem grad_inner (f : F → ℝ) (x v : F) :
    fderiv ℝ f x v = ⟪gradient f x, v⟫_ℝ := by
  unfold gradient; exact InnerProductSpace.toDual_symm_apply.symm

theorem conv_grad (f : F → ℝ) (hc : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f) (x y : F) :
    f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y := by
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

theorem descent (f : F → ℝ) (L : ℝ) (hd : Differentiable ℝ f)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x y : F) :
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

theorem epi (Ψ : F → EReal) (hc : Convex ℝ {p : F × ℝ | Ψ p.1 ≤ (p.2 : EReal)}) (x y : F)
    (a b t : ℝ) (hx : Ψ x ≤ a) (hy : Ψ y ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ψ ((1 - t) • x + t • y) ≤ (((1 - t) * a + t * b : ℝ) : EReal) := by
  have := hc (show (x, a) ∈ {p : F × ℝ | Ψ p.1 ≤ (p.2 : EReal)} from hx)
    (show (y, b) ∈ {p : F × ℝ | Ψ p.1 ≤ (p.2 : EReal)} from hy)
    (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
  simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using this

theorem prox_fin (Ψ : F → EReal) (hbot : ∀ x, Ψ x ≠ ⊥) (s : ℝ) (P : F → F)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Ψ P) (y0 : F) (hy0 : Ψ y0 ≠ ⊤) (w : F) :
    Ψ (P w) ≠ ⊤ := by
  intro h
  have := hP w y0
  rw [h, EReal.top_add_coe, top_le_iff, ← EReal.coe_toReal hy0 (hbot y0), ← EReal.coe_add] at this
  exact EReal.coe_ne_top _ this

theorem prox_ineq (Ψ : F → EReal) (hc : Convex ℝ {p : F × ℝ | Ψ p.1 ≤ (p.2 : EReal)})
    (s : ℝ) (hs : 0 < s) (P : F → F) (hP : ThreeOpSplitting.ConvexRates.IsProx s Ψ P)
    (w u : F) (a b : ℝ) (ha : Ψ (P w) = a) (hb : Ψ u = b) :
    a ≤ b + ⟪P w - w, u - P w⟫_ℝ / s := by
  set d := P w - w with hd
  set e := u - P w with he
  have key : a - b - ⟪d, e⟫_ℝ / s ≤ 0 := by
    apply small_le _ (‖e‖ ^ 2 / (2 * s)) (by positivity)
    intro t ht ht1
    have hv := epi Ψ hc (P w) u a b t ha.le hb.le ht.le ht1
    have hp := hP w ((1 - t) • P w + t • u)
    rw [ha] at hp
    have h2 := hp.trans (add_le_add_left hv _)
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h2
    have ev : (1 - t) • P w + t • u - w = d + t • e := by rw [hd, he]; module
    rw [ev, norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_smul_right] at h2
    have hid : t * (a - b - ⟪d, e⟫_ℝ / s) - t * (‖e‖ ^ 2 / (2 * s) * t)
        = (a + ‖d‖ ^ 2 / (2 * s))
          - ((1 - t) * a + t * b + (‖d‖ ^ 2 + 2 * (t * ⟪d, e⟫_ℝ) + t ^ 2 * ‖e‖ ^ 2) / (2 * s)) := by
      field_simp; ring
    have : t * (a - b - ⟪d, e⟫_ℝ / s) ≤ t * (‖e‖ ^ 2 / (2 * s) * t) := by linarith
    exact le_of_mul_le_mul_left this ht
  linarith

theorem inner_aux (g D e : F) (s : ℝ) (hs : s ≠ 0) :
    ⟪s • g - D, e + D⟫_ℝ / s = ⟪g, e⟫_ℝ + ⟪g, D⟫_ℝ - ⟪D, e⟫_ℝ / s - ‖D‖ ^ 2 / s := by
  rw [inner_sub_left, inner_add_right, inner_add_right, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  field_simp; ring

theorem pg_ineq (Ψ : F → EReal) (hc : Convex ℝ {p : F × ℝ | Ψ p.1 ≤ (p.2 : EReal)})
    (Φ : F → ℝ) (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : Differentiable ℝ Φ) (L : ℝ)
    (hlip : ∀ x y, ‖gradient Φ x - gradient Φ y‖ ≤ L * ‖x - y‖)
    (s : ℝ) (hs : 0 < s) (hsL : s * L ≤ 1) (P : F → F)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Ψ P) (y u xp : F)
    (hxp : xp = P (y - s • gradient Φ y)) (a b : ℝ) (ha : Ψ xp = a) (hb : Ψ u = b) :
    a + Φ xp ≤ b + Φ u + ⟪(1 / s) • (y - xp), y - u⟫_ℝ - s / 2 * ‖(1 / s) • (y - xp)‖ ^ 2 := by
  set g := gradient Φ y with hg
  have h1 := prox_ineq Ψ hc s hs P hP (y - s • g) u a b (by rw [← hxp]; exact ha) hb
  rw [← hxp] at h1
  have h2 := descent Φ L hΦd hlip y xp
  have h3 := conv_grad Φ hΦc hΦd y u
  have hL : L ≤ 1 / s := by rw [le_div_iff₀ hs]; linarith
  have h4 : L / 2 * ‖xp - y‖ ^ 2 ≤ 1 / s / 2 * ‖xp - y‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have i1 : ⟪xp - (y - s • g), u - xp⟫_ℝ / s
      = ⟪g, u - y⟫_ℝ + ⟪g, y - xp⟫_ℝ - ⟪y - xp, u - y⟫_ℝ / s - ‖y - xp‖ ^ 2 / s := by
    have e1 : xp - (y - s • g) = s • g - (y - xp) := by abel
    have e2 : u - xp = (u - y) + (y - xp) := by abel
    rw [e1, e2]
    exact inner_aux g (y - xp) (u - y) s hs.ne'
  have i2 : ⟪g, xp - y⟫_ℝ = -⟪g, y - xp⟫_ℝ := by rw [← inner_neg_right, neg_sub]
  have i3 : ‖xp - y‖ = ‖y - xp‖ := norm_sub_rev _ _
  have i4 : ⟪(1 / s) • (y - xp), y - u⟫_ℝ - s / 2 * ‖(1 / s) • (y - xp)‖ ^ 2
      = -(⟪y - xp, u - y⟫_ℝ / s) - ‖y - xp‖ ^ 2 / (2 * s) := by
    rw [real_inner_smul_left, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have : y - u = -(u - y) := by abel
    rw [this, inner_neg_right]
    field_simp
  rw [i1] at h1
  rw [i2, i3] at h2
  rw [i3] at h4
  have i5 : 1 / s / 2 * ‖y - xp‖ ^ 2 = ‖y - xp‖ ^ 2 / s - ‖y - xp‖ ^ 2 / (2 * s) := by
    field_simp; ring
  linarith

theorem alg (G Z : F) (θ s : ℝ) (hθ : θ ≠ 0) (hs : s ≠ 0) :
    ⟪G, θ • Z⟫_ℝ - s / 2 * ‖G‖ ^ 2
      = θ ^ 2 / (2 * s) * (‖Z‖ ^ 2 - ‖Z - (s / θ) • G‖ ^ 2) := by
  rw [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_smul_right,
    real_inner_smul_right, real_inner_comm G Z]
  field_simp; ring

theorem coe_sum (S : Finset ℕ) (g : ℕ → ℝ) :
    ((∑ k ∈ S, g k : ℝ) : EReal) = ∑ k ∈ S, (g k : EReal) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

theorem rec_num (k r s d0 d1 A0 A1 : ℝ) (hk : 0 ≤ k) (hr : 3 < r) (hs : 0 < s)
    (h : d1 ≤ (1 - (r - 1) / (k + r - 1)) * d0 + ((r - 1) / (k + r - 1)) ^ 2 / (2 * s) * (A0 - A1)) :
    2 * s / (r - 1) * (k + 1 + r - 2) ^ 2 * d1 + (r - 1) * A1
      + 2 * s / (r - 1) * (k * (r - 3) + (r - 2) ^ 2) * d0
      ≤ 2 * s / (r - 1) * (k + r - 2) ^ 2 * d0 + (r - 1) * A0 := by
  have hr1 : 0 < r - 1 := by linarith
  have hc : 0 < k + r - 1 := by linarith
  have hm : 0 ≤ 2 * s * (k + r - 1) ^ 2 / (r - 1) := by positivity
  have key := mul_le_mul_of_nonneg_left h hm
  have e1 : 2 * s * (k + r - 1) ^ 2 / (r - 1)
      * ((1 - (r - 1) / (k + r - 1)) * d0 + ((r - 1) / (k + r - 1)) ^ 2 / (2 * s) * (A0 - A1))
      = 2 * s * (k + r - 1) * k / (r - 1) * d0 + (r - 1) * (A0 - A1) := by
    field_simp; ring
  have e2 : 2 * s * (k + r - 1) ^ 2 / (r - 1) * d1 = 2 * s / (r - 1) * (k + 1 + r - 2) ^ 2 * d1 := by
    ring
  have e3 : 2 * s / (r - 1) * (k + r - 2) ^ 2 * d0 - 2 * s / (r - 1) * (k * (r - 3) + (r - 2) ^ 2) * d0
      = 2 * s * (k + r - 1) * k / (r - 1) * d0 := by
    ring
  rw [e1, e2] at key
  linarith

theorem bound_num (k r s δ D E : ℝ) (hk : 1 ≤ k) (hr : 3 < r) (hs : 0 < s) (hD : 0 ≤ D)
    (hE : 2 * s / (r - 1) * (k + r - 2) ^ 2 * δ ≤ E) (hE1 : E ≤ (r - 1) * D)
    (hA : 0 ≤ (r - 1) * D - E + E) :
    δ ≤ (r - 1) ^ 2 * D / (2 * s * (k + r - 2) ^ 2) := by
  have hr1 : 0 < r - 1 := by linarith
  have hc : 0 < k + r - 2 := by linarith
  rw [le_div_iff₀ (by positivity)]
  have h := hE.trans hE1
  have := mul_le_mul_of_nonneg_left h hr1.le
  have e : (r - 1) * (2 * s / (r - 1) * (k + r - 2) ^ 2 * δ) = δ * (2 * s * (k + r - 2) ^ 2) := by
    field_simp
  nlinarith

theorem sum_num (r s S E1 D : ℝ) (hr : 3 < r) (hs : 0 < s)
    (h : 2 * s * (r - 3) / (r - 1) * S ≤ E1) (hE1 : E1 ≤ (r - 1) * D) :
    S ≤ (r - 1) ^ 2 * D / (2 * s * (r - 3)) := by
  have hr1 : 0 < r - 1 := by linarith
  have hr3 : 0 < r - 3 := by linarith
  rw [le_div_iff₀ (by positivity)]
  have h2 := h.trans hE1
  have := mul_le_mul_of_nonneg_left h2 hr1.le
  have e : (r - 1) * (2 * s * (r - 3) / (r - 1) * S) = S * (2 * s * (r - 3)) := by
    field_simp
  nlinarith

theorem term_num (k r s δ : ℝ) (hk : 0 ≤ k) (hr : 3 < r) (hs : 0 < s) (hδ : 0 ≤ δ) :
    2 * s * (r - 3) / (r - 1) * ((k + r - 1) * δ) ≤ 2 * s / (r - 1) * (k * (r - 3) + (r - 2) ^ 2) * δ := by
  have hr1 : 0 < r - 1 := by linarith
  have h1 : (r - 3) * (k + r - 1) ≤ k * (r - 3) + (r - 2) ^ 2 := by nlinarith
  have h2 : 0 ≤ 2 * s / (r - 1) * δ := by positivity
  have := mul_le_mul_of_nonneg_left h1 h2
  have e1 : 2 * s * (r - 3) / (r - 1) * ((k + r - 1) * δ) = 2 * s / (r - 1) * δ * ((r - 3) * (k + r - 1)) := by
    ring
  have e2 : 2 * s / (r - 1) * (k * (r - 3) + (r - 2) ^ 2) * δ
      = 2 * s / (r - 1) * δ * (k * (r - 3) + (r - 2) ^ 2) := by ring
  rw [e1, e2]; exact this

end RRAux_NesterovODE_GenScheme_theorem_6

open scoped InnerProductSpace
open RRAux_NesterovODE_GenScheme_theorem_6

open InnerProductSpace NesterovFB.Rates ThreeOpSplitting.ConvexRates NesterovODE.GenScheme in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : NNReal) (s r : ℝ) (P : H → H) (x : ℕ → H) (xstar : H)
    (hΨ : IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL0 : 0 < L) (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * L ≤ 1)
    (hP : IsProx s Ψ P)
    (hr : 3 < r)
    (hrun : IsGenNesterovRun Φ P r s x)
    (hmin : ∀ y : H, theta Ψ Φ xstar ≤ theta Ψ Φ y) :
    (∀ k : ℕ, 1 ≤ k →
      theta Ψ Φ (x k) - theta Ψ Φ xstar
        ≤ (((r - 1) ^ 2 * ‖x 0 - xstar‖ ^ 2 / (2 * s * ((k : ℝ) + r - 2) ^ 2) : ℝ) : EReal)) ∧
    (∀ K : ℕ,
      ∑ k ∈ Finset.Icc 1 K, (((k : ℝ) + r - 1 : ℝ) : EReal) * (theta Ψ Φ (x k) - theta Ψ Φ xstar)
        ≤ (((r - 1) ^ 2 * ‖x 0 - xstar‖ ^ 2 / (2 * s * (r - 3)) : ℝ) : EReal)) := by
  obtain ⟨hbot, ⟨y0, hy0⟩, _, hepi⟩ := hΨ
  have hΦd' : Differentiable ℝ Φ := hΦd.differentiable (by norm_num)
  have hlip : ∀ a b, ‖gradient Φ a - gradient Φ b‖ ≤ (L : ℝ) * ‖a - b‖ := by
    intro a b; have := hL.dist_le_mul a b; rwa [dist_eq_norm, dist_eq_norm] at this
  have hfinP := prox_fin Ψ hbot s P hP y0 hy0
  set ψ : H → ℝ := fun v => (Ψ v).toReal with hψdef
  have hψ : ∀ v, Ψ v ≠ ⊤ → Ψ v = (ψ v : EReal) := fun v hv => (EReal.coe_toReal hv (hbot v)).symm
  have hxk : ∀ k, Ψ (x (k + 1)) ≠ ⊤ := by intro k; rw [hrun k]; exact hfinP _
  have htheta : ∀ v, Ψ v ≠ ⊤ → theta Ψ Φ v = ((ψ v + Φ v : ℝ) : EReal) := by
    intro v hv; unfold theta; rw [hψ v hv, EReal.coe_add]
  have hstar : Ψ xstar ≠ ⊤ := by
    intro h
    have := hmin (x 1)
    rw [htheta _ (hxk 0)] at this
    unfold theta at this
    rw [h, EReal.top_add_coe, top_le_iff] at this
    exact EReal.coe_ne_top _ this
  set tstar := ψ xstar + Φ xstar with htstar
  have hmin' : ∀ v, Ψ v ≠ ⊤ → tstar ≤ ψ v + Φ v := by
    intro v hv; have := hmin v; rw [htheta _ hstar, htheta _ hv] at this
    exact EReal.coe_le_coe_iff.1 this
  have hr1 : 0 < r - 1 := by linarith
  have core : ∀ k : ℕ, ψ (x (k + 1)) + Φ (x (k + 1)) - tstar
      ≤ (1 - (r - 1) / ((k : ℝ) + r - 1)) * (ψ (x k) + Φ (x k) - tstar)
        + ((r - 1) / ((k : ℝ) + r - 1)) ^ 2 / (2 * s)
          * (‖zSeq r x k - xstar‖ ^ 2 - ‖zSeq r x (k + 1) - xstar‖ ^ 2) := by
    intro k
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hc : 0 < (k : ℝ) + r - 1 := by linarith
    set θ := (r - 1) / ((k : ℝ) + r - 1) with hθ
    have hθ0 : 0 < θ := div_pos hr1 hc
    have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hc]; linarith
    set u := (1 - θ) • x k + θ • xstar with hu
    have hΨu : Ψ u ≤ (((1 - θ) * ψ (x k) + θ * ψ xstar : ℝ) : EReal) := by
      rcases Nat.eq_zero_or_pos k with hk | hkpos
      · subst hk
        have h1 : θ = 1 := by rw [hθ]; push_cast; rw [zero_add]; exact div_self hr1.ne'
        rw [hu, h1]; simp only [sub_self, zero_smul, one_smul, zero_add, zero_mul, one_mul]
        rw [hψ _ hstar]
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        exact epi Ψ hepi _ _ _ _ θ (hψ _ (hxk j)).le (hψ _ hstar).le hθ0.le hθ1
    have hufin : Ψ u ≠ ⊤ := fun h => by
      rw [h, top_le_iff] at hΨu; exact EReal.coe_ne_top _ hΨu
    have hΨu' : ψ u ≤ (1 - θ) * ψ (x k) + θ * ψ xstar := by
      rw [hψ _ hufin] at hΨu; exact EReal.coe_le_coe_iff.1 hΨu
    have hΦu : Φ u ≤ (1 - θ) * Φ (x k) + θ * Φ xstar := by
      have := hΦc.2 (Set.mem_univ (x k)) (Set.mem_univ xstar) (by linarith : 0 ≤ 1 - θ) hθ0.le
        (by ring)
      simpa [smul_eq_mul] using this
    have hpg := pg_ineq Ψ hepi Φ hΦc hΦd' L hlip s hs hsL P hP (extrap r x k) u (x (k + 1))
      (hrun k) (ψ (x (k + 1))) (ψ u) (hψ _ (hxk k)) (hψ _ hufin)
    -- vector identities
    set b := ((k : ℝ) - 1) / (r - 1) with hb
    set d := x k - x (k - 1) with hd
    have hy : extrap r x k = x k + (θ * b) • d := by
      unfold extrap
      have : ((k : ℝ) - 1) / ((k : ℝ) + r - 1) = θ * b := by rw [hθ, hb]; field_simp
      rw [this]
    have hzk : zSeq r x k = x k + b • d := rfl
    have hzk1 : zSeq r x (k + 1) = x (k + 1) + ((k : ℝ) / (r - 1)) • (x (k + 1) - x k) := by
      unfold zSeq
      push_cast
      simp only [add_sub_cancel_right]
    have hyu : extrap r x k - u = θ • (zSeq r x k - xstar) := by
      rw [hy, hzk, hu]; module
    have hsθ : s / θ * (1 / s) = 1 + (k : ℝ) / (r - 1) := by
      rw [hθ]; field_simp; ring
    have hdb : (1 + (k : ℝ) / (r - 1)) * (θ * b) = b := by
      rw [hθ, hb]; field_simp; ring
    have hz : zSeq r x (k + 1) - xstar
        = (zSeq r x k - xstar) - (s / θ) • ((1 / s) • (extrap r x k - x (k + 1))) := by
      rw [smul_smul, hsθ, hzk1, hzk, hy]
      rw [show (1 + (k : ℝ) / (r - 1)) • (x k + (θ * b) • d - x (k + 1))
          = (1 + (k : ℝ) / (r - 1)) • x k + b • d - (1 + (k : ℝ) / (r - 1)) • x (k + 1) by
        rw [smul_sub, smul_add, smul_smul, hdb]]
      module
    have hal := alg ((1 / s) • (extrap r x k - x (k + 1))) (zSeq r x k - xstar) θ s hθ0.ne' hs.ne'
    rw [← hz, ← hyu] at hal
    have e1 : (1 - θ) * (ψ (x k) + Φ (x k) - tstar)
        = (1 - θ) * ψ (x k) + (1 - θ) * Φ (x k) - (1 - θ) * tstar := by ring
    rw [e1, htstar]
    linarith
  set δ : ℕ → ℝ := fun k => ψ (x k) + Φ (x k) - tstar with hδ
  set A : ℕ → ℝ := fun k => ‖zSeq r x k - xstar‖ ^ 2 with hA
  set D := ‖x 0 - xstar‖ ^ 2 with hD
  have hA0 : ∀ k, 0 ≤ A k := fun k => by positivity
  have hδ0 : ∀ k, 0 ≤ δ (k + 1) := fun k => sub_nonneg.2 (hmin' _ (hxk k))
  have hz0 : zSeq r x 0 = x 0 := by unfold zSeq; simp
  -- first step
  have hstep0 : 2 * s * δ 1 + A 1 ≤ D := by
    have h := core 0
    have h1 : (r - 1) / (((0:ℕ) : ℝ) + r - 1) = 1 := by
      push_cast; rw [zero_add]; exact div_self hr1.ne'
    rw [h1, hz0] at h
    have h2 : δ 1 ≤ 1 / (2 * s) * (D - A 1) := by
      simp only [hδ, hA, hD]; simpa using h
    rw [mul_comm, ← div_eq_mul_one_div, le_div_iff₀ (by positivity)] at h2
    linarith
  set E : ℕ → ℝ := fun k => 2 * s / (r - 1) * ((k : ℝ) + r - 2) ^ 2 * δ k + (r - 1) * A k with hE
  have hrec : ∀ k : ℕ, E (k + 1) + 2 * s / (r - 1) * ((k : ℝ) * (r - 3) + (r - 2) ^ 2) * δ k ≤ E k := by
    intro k
    have := rec_num (k : ℝ) r s (δ k) (δ (k + 1)) (A k) (A (k + 1)) (Nat.cast_nonneg k) hr hs (core k)
    simp only [hE]
    push_cast
    linarith
  have hE1 : E 1 ≤ (r - 1) * D := by
    have e : E 1 = (r - 1) * (2 * s * δ 1 + A 1) := by
      simp only [hE]; push_cast; field_simp; ring
    rw [e]; exact mul_le_mul_of_nonneg_left hstep0 hr1.le
  have hdec : ∀ k : ℕ, E (k + 1) ≤ E 1 := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ j ih =>
      have h := hrec (j + 1)
      have : 0 ≤ 2 * s / (r - 1) * (((j + 1 : ℕ) : ℝ) * (r - 3) + (r - 2) ^ 2) * δ (j + 1) := by
        have := hδ0 j
        have : 0 ≤ ((j + 1 : ℕ) : ℝ) * (r - 3) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
        positivity
      linarith
  have hEnn : ∀ k : ℕ, 0 ≤ E (k + 1) := by
    intro k
    have := hδ0 k
    have := hA0 (k + 1)
    have : 0 ≤ ((k + 1 : ℕ) : ℝ) + r - 2 := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
    simp only [hE]; positivity
  refine ⟨?_, ?_⟩
  · intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [htheta _ (hxk j), htheta _ hstar, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    have hle : 2 * s / (r - 1) * (((j + 1 : ℕ) : ℝ) + r - 2) ^ 2 * δ (j + 1) ≤ E (j + 1) := by
      have := hA0 (j + 1)
      have : 0 ≤ (r - 1) * A (j + 1) := mul_nonneg hr1.le this
      simp only [hE]; linarith
    have := bound_num (((j + 1 : ℕ) : ℝ)) r s (δ (j + 1)) D (E (j + 1))
      (by exact_mod_cast hk) hr hs (by positivity) hle ((hdec j).trans hE1)
      (by have : 0 ≤ (r - 1) * D := mul_nonneg hr1.le (by positivity); linarith)
    exact this
  · intro K
    have hsum : ∀ K : ℕ, 2 * s * (r - 3) / (r - 1) * ∑ k ∈ Finset.Icc 1 K, (((k : ℝ) + r - 1) * δ k)
        ≤ E 1 - E (K + 1) := by
      intro K
      induction K with
      | zero => simp
      | succ j ih =>
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1), mul_add]
        have h := hrec (j + 1)
        have ht := term_num (((j + 1 : ℕ) : ℝ)) r s (δ (j + 1)) (Nat.cast_nonneg _) hr hs (hδ0 j)
        linarith
    have hfin : ∀ k ∈ Finset.Icc 1 K,
        (((k : ℝ) + r - 1 : ℝ) : EReal) * (theta Ψ Φ (x k) - theta Ψ Φ xstar)
          = ((((k : ℝ) + r - 1) * δ k : ℝ) : EReal) := by
      intro k hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := (Finset.mem_Icc.1 hk).1; omega⟩
      rw [htheta _ (hxk j), htheta _ hstar, ← EReal.coe_sub, ← EReal.coe_mul]
    rw [Finset.sum_congr rfl hfin, ← coe_sum, EReal.coe_le_coe_iff]
    have h1 := hsum K
    have h2 := hEnn K
    exact sum_num r s _ (E 1) D hr hs (by linarith) hE1

#print axioms solution
