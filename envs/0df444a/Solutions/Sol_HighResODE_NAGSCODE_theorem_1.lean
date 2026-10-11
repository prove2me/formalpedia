-- Prove2me | solution 1 for HighResODE.NAGSCODE.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T22:08:14.56492+00:00
-- url     : https://prove2.me/submissions/9fa939bd-01dc-4e7b-99a4-95c9d42f1bd0

import Mathlib
import Definitions.Def_HighResODE_NAGSCODE_Setting

namespace RRAux_HighResODE_NAGSCODE_theorem_1

open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem grad_diff (f : F → ℝ) (hf : ContDiff ℝ 2 f) : Differentiable ℝ (gradient f) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h2 : Differentiable ℝ (fderiv ℝ f) := h1.differentiable (by norm_num)
  have : gradient f = fun x => (InnerProductSpace.toDual ℝ F).symm (fderiv ℝ f x) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ F).symm.toContinuousLinearEquiv.differentiable.comp h2

theorem grad_inner (f : F → ℝ) (x v : F) :
    fderiv ℝ f x v = ⟪gradient f x, v⟫_ℝ := by
  unfold gradient; exact InnerProductSpace.toDual_symm_apply.symm

theorem psd (f : F → ℝ) (hconv : ∀ x y, f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y)
    (x : F) (H : F →L[ℝ] F) (hg : HasFDerivAt (gradient f) H x) (v : F) : 0 ≤ ⟪v, H v⟫_ℝ := by
  have hmono : ∀ y z : F, 0 ≤ ⟪gradient f y - gradient f z, y - z⟫_ℝ := by
    intro y z
    have h1 := hconv y z
    have h2 := hconv z y
    rw [inner_sub_left]
    rw [← neg_sub y z, inner_neg_right] at h1
    linarith
  set φ : ℝ → ℝ := fun t => ⟪gradient f (x + t • v), v⟫_ℝ with hφ
  have hφm : Monotone φ := by
    intro t t' htt'
    have := hmono (x + t' • v) (x + t • v)
    have e : x + t' • v - (x + t • v) = (t' - t) • v := by rw [sub_smul]; abel
    rw [e, inner_smul_right, inner_sub_left] at this
    simp only [hφ]
    rcases eq_or_lt_of_le htt' with h | h
    · rw [h]
    · have hp : 0 < t' - t := sub_pos.2 h
      have : 0 ≤ ⟪gradient f (x + t' • v), v⟫_ℝ - ⟪gradient f (x + t • v), v⟫_ℝ := by
        by_contra hc
        push Not at hc
        nlinarith
      linarith
  have hd : HasDerivAt φ ⟪H v, v⟫_ℝ 0 := by
    have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
    have hg' : HasFDerivAt (gradient f) H (x + (0:ℝ) • v) := by simpa using hg
    have hc := hg'.comp_hasDerivAt (0:ℝ) hl
    have := hc.inner ℝ (hasDerivAt_const (0:ℝ) v)
    simpa [hφ, Function.comp_def] using this
  have := hφm.deriv_nonneg (x := 0)
  rw [hd.deriv] at this
  rwa [real_inner_comm]

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

theorem decay (E D : ℝ → ℝ) (c : ℝ)
    (hE : ∀ t, 0 ≤ t → HasDerivWithinAt E (D t) (Set.Ici 0) t)
    (hD : ∀ t, 0 ≤ t → D t + c * E t ≤ 0) :
    ∀ t, 0 ≤ t → E t ≤ E 0 * Real.exp (-(c * t)) := by
  have hF : ∀ t, 0 ≤ t → HasDerivWithinAt (fun u => E u * Real.exp (c * u))
      (D t * Real.exp (c * t) + E t * (Real.exp (c * t) * c)) (Set.Ici 0) t := by
    intro t ht
    have h1 : HasDerivWithinAt (fun u => c * u) c (Set.Ici 0) t := by
      simpa using ((hasDerivAt_id t).const_mul c).hasDerivWithinAt
    exact (hE t ht).mul (h1.exp)
  have hanti : AntitoneOn (fun u => E u * Real.exp (c * u)) (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro t ht; exact (hF t ht).continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact ((hF t (le_of_lt ht)).hasDerivAt (Ici_mem_nhds ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [((hF t (le_of_lt ht)).hasDerivAt (Ici_mem_nhds ht)).deriv]
      have := hD t (le_of_lt ht)
      have he := Real.exp_pos (c * t)
      nlinarith
  intro t ht
  have := hanti (show (0:ℝ) ∈ Set.Ici (0:ℝ) from Set.mem_Ici.2 le_rfl) (show t ∈ Set.Ici (0:ℝ) from ht) ht
  simp only [mul_zero, Real.exp_zero, mul_one] at this
  have he := Real.exp_pos (c * t)
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ he]
  exact this


theorem three_sq (p q w : F) : ‖p + q + w‖ ^ 2 ≤ 3 * (‖p‖ ^ 2 + ‖q‖ ^ 2 + ‖w‖ ^ 2) := by
  have h1 := norm_sub_sq_real p q
  have h2 := norm_sub_sq_real p w
  have h3 := norm_sub_sq_real q w
  have e := norm_add_sq_real (p + q) w
  have e2 := norm_add_sq_real p q
  rw [inner_add_left] at e
  nlinarith [sq_nonneg ‖p - q‖, sq_nonneg ‖p - w‖, sq_nonneg ‖q - w‖]

theorem key2 (v x g hv : F) (a r σ μ δ : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hσ : 0 ≤ σ) (hμ : a ^ 2 = μ) (har : a * σ = r) (hK : 0 ≤ ⟪v, hv⟫_ℝ)
    (hδ : μ / 2 * ‖x‖ ^ 2 ≤ δ) (hG : δ + μ / 2 * ‖x‖ ^ 2 ≤ ⟪g, x⟫_ℝ) :
    (1 + r) * ⟪g, v⟫_ℝ + 1 / 4 * (2 * ⟪v, -(2 * a) • v - σ • hv - (1 + r) • g⟫_ℝ)
      + 1 / 4 * (2 * ⟪v + (2 * a) • x + σ • g,
          (-(2 * a) • v - σ • hv - (1 + r) • g) + (2 * a) • v + σ • hv⟫_ℝ)
      + a / 4 * ((1 + r) * δ + 1 / 4 * ‖v‖ ^ 2 + 1 / 4 * ‖v + (2 * a) • x + σ • g‖ ^ 2) ≤ 0 := by
  have hT := three_sq v ((2 * a) • x) (σ • g)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hσ,
    abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * a)] at hT
  have e : (-(2 * a) • v - σ • hv - (1 + r) • g) + (2 * a) • v + σ • hv = -((1 + r) • g) := by
    module
  rw [e]
  simp only [inner_add_left, inner_sub_right, inner_neg_right, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real, real_inner_self_eq_norm_sq]
  try rw [real_inner_comm g v]
  try rw [real_inner_comm g x]
  subst hμ
  have hTn : 0 ≤ ‖v + (2 * a) • x + σ • g‖ ^ 2 := sq_nonneg _
  have h2 : (1 + r) * (a * (δ + a ^ 2 / 2 * ‖x‖ ^ 2)) ≤ (1 + r) * (a * ⟪x, g⟫_ℝ) := by
    rw [real_inner_comm] at hG
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG ha) (by linarith)
  have h2b : (1 + r) * (a * (a ^ 2 / 2 * ‖x‖ ^ 2)) ≤ (1 + r) * (a * δ) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδ ha) (by linarith)
  have h3 : a * ‖v + (2 * a) • x + σ • g‖ ^ 2
      ≤ a * (3 * (‖v‖ ^ 2 + (2 * a * ‖x‖) ^ 2 + (σ * ‖g‖) ^ 2)) := mul_le_mul_of_nonneg_left hT ha
  have h4 : a * (σ * ‖g‖) ^ 2 = r * (σ * ‖g‖ ^ 2) := by rw [← har]; ring
  have h5 : 0 ≤ (1 - r) * (σ * ‖g‖ ^ 2) := mul_nonneg (by linarith) (mul_nonneg hσ (sq_nonneg _))
  have h6 : 0 ≤ r * (σ * ‖g‖ ^ 2) := mul_nonneg hr (mul_nonneg hσ (sq_nonneg _))
  have h7 : 0 ≤ σ * ⟪v, hv⟫_ℝ := mul_nonneg hσ hK
  have h8 : 0 ≤ a * ‖v‖ ^ 2 := mul_nonneg ha (sq_nonneg _)
  have h9 : 0 ≤ r * (a * (a ^ 2 * ‖x‖ ^ 2)) :=
    mul_nonneg hr (mul_nonneg ha (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have h10 : 0 ≤ σ * ‖g‖ ^ 2 := mul_nonneg hσ (sq_nonneg _)
  have h11 : 0 ≤ a * (a ^ 2 * ‖x‖ ^ 2) := mul_nonneg ha (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [real_inner_comm g x] at h2
  linear_combination h3 / 16 + h2 + (3/4) * h2b + (3/16) * h4 + (1/8) * h11 + (7/8) * h9 + (1/2) * h10 + (5/16) * h6 + (1/2) * h7 + (3/4) * h8

theorem init_vec2 (g w : F) (k m a r δ σ : ℝ) (hm : σ - k = m) (hm0 : m ≤ 0) (ha : 0 ≤ a)
    (hG : 0 ≤ ⟪g, w⟫_ℝ) :
    (1 + r) * δ + 1 / 4 * ‖-k • g‖ ^ 2 + 1 / 4 * ‖-k • g + (2 * a) • w + σ • g‖ ^ 2
      ≤ (1 + r) * δ + 1 / 4 * k ^ 2 * ‖g‖ ^ 2 + 1 / 4 * m ^ 2 * ‖g‖ ^ 2 + a ^ 2 * ‖w‖ ^ 2 := by
  have e : -k • g + (2 * a) • w + σ • g = m • g + (2 * a) • w := by
    rw [← hm]; module
  rw [e, norm_add_sq_real, norm_smul, norm_smul, norm_smul, inner_smul_left, inner_smul_right,
    mul_pow, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    sq_abs, sq_abs]
  simp only [RCLike.conj_to_real]
  have : m * (a * ⟪g, w⟫_ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hm0 (mul_nonneg ha hG)
  nlinarith

theorem init_bound2 (s L r μ δ N d k m : ℝ) (hs : 0 < s) (hL : 0 < L) (hsL : s * L ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hμ : μ * s = r ^ 2) (hδ : δ ≤ L / 2 * d ^ 2) (hd0 : 0 ≤ d) (hN0 : 0 ≤ N)
    (hN : N ≤ L * d) (hk : k ^ 2 = 4 * s / (1 + r) ^ 2)
    (hm : m ^ 2 = s * (1 - r) ^ 2 / (1 + r) ^ 2) :
    (1 + r) * δ + 1 / 4 * k ^ 2 * N ^ 2 + 1 / 4 * m ^ 2 * N ^ 2 + μ * d ^ 2
      ≤ 2 * (1 + r) * d ^ 2 / s := by
  have hq : 1 ≤ (1 + r) ^ 2 := by nlinarith
  have hq0 : 0 < (1 + r) ^ 2 := by positivity
  rw [le_div_iff₀ hs]
  set c := s ^ 2 / (1 + r) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hcs : c ≤ s ^ 2 := div_le_self (sq_nonneg s) hq
  have ek : 1 / 4 * k ^ 2 * N ^ 2 * s = c * N ^ 2 := by
    rw [hk, hc]; field_simp
  have em : 1 / 4 * m ^ 2 * N ^ 2 * s = c * ((1 - r) ^ 2 / 4) * N ^ 2 := by
    rw [hm, hc]; field_simp
  have hsN : (s * N) ^ 2 ≤ d ^ 2 := by
    have h1 : s * N ≤ s * (L * d) := mul_le_mul_of_nonneg_left hN hs.le
    have h2 : 0 ≤ s * N := by positivity
    have h3 : s * L * d ≤ d := by
      have := mul_le_mul_of_nonneg_right hsL hd0
      linarith
    have h4 : s * N ≤ d := by linarith
    exact pow_le_pow_left₀ h2 h4 2
  have e1 : c * N ^ 2 ≤ d ^ 2 := by
    have := mul_le_mul_of_nonneg_right hcs (sq_nonneg N)
    have e : s ^ 2 * N ^ 2 = (s * N) ^ 2 := by ring
    linarith
  have e2 : c * ((1 - r) ^ 2 / 4) * N ^ 2 ≤ d ^ 2 / 4 := by
    have : (1 - r) ^ 2 ≤ 1 := by nlinarith
    have : 0 ≤ c * N ^ 2 := by positivity
    nlinarith
  have e3 : (1 + r) * δ * s ≤ (1 + r) * d ^ 2 / 2 := by
    have h1 : δ * s ≤ L / 2 * d ^ 2 * s := mul_le_mul_of_nonneg_right hδ hs.le
    have h2 : L / 2 * d ^ 2 * s ≤ d ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_right hsL (sq_nonneg d)
      linarith
    have h3 : (1 + r) * (δ * s) ≤ (1 + r) * (d ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have e4 : μ * d ^ 2 * s = r ^ 2 * d ^ 2 := by rw [← hμ]; ring
  have e5 : r ^ 2 * d ^ 2 ≤ r * d ^ 2 :=
    mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg d)
  have e6 : ((1 + r) * δ + 1 / 4 * k ^ 2 * N ^ 2 + 1 / 4 * m ^ 2 * N ^ 2 + μ * d ^ 2) * s
      = (1 + r) * δ * s + 1 / 4 * k ^ 2 * N ^ 2 * s + 1 / 4 * m ^ 2 * N ^ 2 * s
        + μ * d ^ 2 * s := by ring
  have e7 : 0 ≤ r * d ^ 2 := mul_nonneg hr0 (sq_nonneg d)
  rw [e6, ek, em, e4]
  linarith [sq_nonneg d]

end RRAux_HighResODE_NAGSCODE_theorem_1

open scoped InnerProductSpace
open RRAux_HighResODE_NAGSCODE_theorem_1

open HighResODE.NAGSCODE in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L s : ℝ) (hf : IsS2 f μ L)
    (xs : EuclideanSpace ℝ (Fin n)) (hmin : ∀ z, f xs ≤ f z) (hs : 0 < s) (hsL : s ≤ 1 / L)
    (x0 : EuclideanSpace ℝ (Fin n)) (X V : ℝ → EuclideanSpace ℝ (Fin n))
    (hsol : IsNAGSCODE f μ s x0 X V) :
    ∀ t, 0 ≤ t →
      f (X t) - f xs ≤ 2 * ‖x0 - xs‖ ^ 2 / s * Real.exp (-(Real.sqrt μ * t / 4)) := by
  intro t ht
  have hL := hf.L_pos
  have hdiff := hf.differentiable
  have hconv := hf.convex
  have hlip := hf.grad_lipschitz
  have hμpos := hf.mu_pos
  have hμL := hf.mu_le_L
  have hsc := hf.strong_convex
  have hgd := grad_diff f hf.contDiff
  have hg0 : gradient f xs = 0 := by
    have hlm : IsLocalMin f xs := Filter.Eventually.of_forall hmin
    unfold gradient
    rw [hlm.fderiv_eq_zero, map_zero]
  have ha : 0 ≤ Real.sqrt μ := Real.sqrt_nonneg _
  have hr : 0 ≤ Real.sqrt (μ * s) := Real.sqrt_nonneg _
  have hσ : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
  have ha2 : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμpos.le
  have har : Real.sqrt μ * Real.sqrt s = Real.sqrt (μ * s) := (Real.sqrt_mul hμpos.le s).symm
  have hsL' : s * L ≤ 1 := by rw [le_div_iff₀ hL] at hsL; linarith
  have hr1 : Real.sqrt (μ * s) ≤ 1 := by
    rw [Real.sqrt_le_one]; nlinarith
  have hderiv : ∀ u, 0 ≤ u → HasDerivWithinAt (lyap f μ s xs X V)
      ((1 + Real.sqrt (μ * s)) * ⟪gradient f (X u), V u⟫_ℝ
        + 1 / 4 * (2 * ⟪V u, -(2 * Real.sqrt μ) • V u
            - Real.sqrt s • fderiv ℝ (gradient f) (X u) (V u)
            - (1 + Real.sqrt (μ * s)) • gradient f (X u)⟫_ℝ)
        + 1 / 4 * (2 * ⟪V u + (2 * Real.sqrt μ) • (X u - xs) + Real.sqrt s • gradient f (X u),
            (-(2 * Real.sqrt μ) • V u - Real.sqrt s • fderiv ℝ (gradient f) (X u) (V u)
              - (1 + Real.sqrt (μ * s)) • gradient f (X u))
              + (2 * Real.sqrt μ) • V u + Real.sqrt s • fderiv ℝ (gradient f) (X u) (V u)⟫_ℝ))
      (Set.Ici 0) u := by
    intro u hu
    have hX := hsol.deriv_pos u hu
    have hV := hsol.deriv_vel u hu
    have h1 : HasDerivWithinAt (fun w => f (X w)) ⟪gradient f (X u), V u⟫_ℝ (Set.Ici 0) u := by
      have := (hdiff (X u)).hasFDerivAt.comp_hasDerivWithinAt u hX
      rw [grad_inner f] at this
      exact this
    have hg : HasDerivWithinAt (fun w => gradient f (X w))
        (fderiv ℝ (gradient f) (X u) (V u)) (Set.Ici 0) u :=
      (hgd (X u)).hasFDerivAt.comp_hasDerivWithinAt u hX
    have hW := (hV.add ((hX.sub_const xs).const_smul (2 * Real.sqrt μ))).add
      (hg.const_smul (Real.sqrt s))
    exact (((h1.sub_const (f xs)).const_mul (1 + Real.sqrt (μ * s))).add
      ((hV.norm_sq).const_mul (1 / 4))).add ((hW.norm_sq).const_mul (1 / 4))
  have hdec := decay (lyap f μ s xs X V) _ (Real.sqrt μ / 4) hderiv (by
    intro u hu
    have hG : f (X u) - f xs + μ / 2 * ‖X u - xs‖ ^ 2 ≤ ⟪gradient f (X u), X u - xs⟫_ℝ := by
      have := hsc (X u) xs
      rw [← neg_sub (X u) xs, inner_neg_right, norm_neg] at this
      linarith
    have hδ : μ / 2 * ‖X u - xs‖ ^ 2 ≤ f (X u) - f xs := by
      have := hsc xs (X u)
      rw [hg0, inner_zero_left] at this
      linarith
    have hK := psd f hconv (X u) _ (hgd (X u)).hasFDerivAt (V u)
    have := key2 (V u) (X u - xs) (gradient f (X u)) (fderiv ℝ (gradient f) (X u) (V u))
      (Real.sqrt μ) (Real.sqrt (μ * s)) (Real.sqrt s) μ (f (X u) - f xs) ha hr hr1 hσ ha2 har
      hK hδ hG
    unfold lyap
    linarith) t ht
  have hle : (1 + Real.sqrt (μ * s)) * (f (X t) - f xs) ≤ lyap f μ s xs X V t := by
    unfold lyap
    nlinarith [sq_nonneg ‖V t‖,
      sq_nonneg ‖V t + (2 * Real.sqrt μ) • (X t - xs) + Real.sqrt s • gradient f (X t)‖]
  have h0 : lyap f μ s xs X V 0 ≤ 2 * (1 + Real.sqrt (μ * s)) * ‖x0 - xs‖ ^ 2 / s := by
    unfold lyap
    rw [hsol.init_pos, hsol.init_vel]
    have hG : 0 ≤ ⟪gradient f x0, x0 - xs⟫_ℝ := by
      have := hconv x0 xs
      rw [← neg_sub x0 xs, inner_neg_right] at this
      linarith [hmin x0]
    have hm0 : Real.sqrt s - 2 * Real.sqrt s / (1 + Real.sqrt (μ * s)) ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ (by positivity)]
      nlinarith
    have hv := init_vec2 (gradient f x0) (x0 - xs) _ _ (Real.sqrt μ) (Real.sqrt (μ * s))
      (f x0 - f xs) (Real.sqrt s) rfl hm0 ha hG
    have hN : ‖gradient f x0‖ ≤ L * ‖x0 - xs‖ := by
      have := hlip x0 xs; rwa [hg0, sub_zero] at this
    have hδ : f x0 - f xs ≤ L / 2 * ‖x0 - xs‖ ^ 2 := by
      have := descent f L hdiff hlip xs x0
      rw [hg0, inner_zero_left] at this
      linarith
    have hq : (1 + Real.sqrt (μ * s)) ≠ 0 := by positivity
    have hk2 : (2 * Real.sqrt s / (1 + Real.sqrt (μ * s))) ^ 2
        = 4 * s / (1 + Real.sqrt (μ * s)) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hs.le]; norm_num
    have hm2 : (Real.sqrt s - 2 * Real.sqrt s / (1 + Real.sqrt (μ * s))) ^ 2
        = s * (1 - Real.sqrt (μ * s)) ^ 2 / (1 + Real.sqrt (μ * s)) ^ 2 := by
      field_simp
      rw [Real.sq_sqrt hs.le]; ring
    have hμs : μ * s = Real.sqrt (μ * s) ^ 2 := (Real.sq_sqrt (by positivity)).symm
    have hb := init_bound2 s L (Real.sqrt (μ * s)) μ _ _ ‖x0 - xs‖ _ _ hs hL hsL' hr hr1 hμs hδ
      (norm_nonneg _) (norm_nonneg _) hN hk2 hm2
    rw [ha2] at hv
    linarith
  have hexp : Real.exp (-(Real.sqrt μ / 4 * t)) = Real.exp (-(Real.sqrt μ * t / 4)) := by
    congr 1; ring
  rw [hexp] at hdec
  have hpos := Real.exp_pos (-(Real.sqrt μ * t / 4))
  have hq : 0 < 1 + Real.sqrt (μ * s) := by positivity
  have hchain : (1 + Real.sqrt (μ * s)) * (f (X t) - f xs)
      ≤ (1 + Real.sqrt (μ * s)) * (2 * ‖x0 - xs‖ ^ 2 / s * Real.exp (-(Real.sqrt μ * t / 4))) := by
    calc (1 + Real.sqrt (μ * s)) * (f (X t) - f xs) ≤ lyap f μ s xs X V t := hle
      _ ≤ lyap f μ s xs X V 0 * Real.exp (-(Real.sqrt μ * t / 4)) := hdec
      _ ≤ 2 * (1 + Real.sqrt (μ * s)) * ‖x0 - xs‖ ^ 2 / s * Real.exp (-(Real.sqrt μ * t / 4)) :=
          mul_le_mul_of_nonneg_right h0 hpos.le
      _ = _ := by ring
  exact le_of_mul_le_mul_left hchain hq

#print axioms solution
