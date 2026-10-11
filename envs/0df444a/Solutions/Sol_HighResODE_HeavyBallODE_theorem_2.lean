-- Prove2me | solution 1 for HighResODE.HeavyBallODE.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T22:03:40.001125+00:00
-- url     : https://prove2.me/submissions/85dc40d9-a5f9-4ae8-a09b-50274744d2a8

import Mathlib
import Definitions.Def_HighResODE_HeavyBallODE_Setting

namespace RRAux_HighResODE_HeavyBallODE_theorem_2

open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem key_deriv (v x g : F) (a r μ δ : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r) (hμ : a ^ 2 = μ)
    (hδ : 0 ≤ δ) (hG : δ + μ / 2 * ‖x‖ ^ 2 ≤ ⟪g, x⟫_ℝ) :
    (1 + r) * ⟪g, v⟫_ℝ + 1 / 4 * (2 * ⟪v, -(2 * a) • v - (1 + r) • g⟫_ℝ)
      + 1 / 4 * (2 * ⟪v + (2 * a) • x, (-(2 * a) • v - (1 + r) • g) + (2 * a) • v⟫_ℝ)
      + a / 4 * ((1 + r) * δ + 1 / 4 * ‖v‖ ^ 2 + 1 / 4 * ‖v + (2 * a) • x‖ ^ 2) ≤ 0 := by
  have e1 : ‖v + (2 * a) • x‖ ^ 2 = ‖v‖ ^ 2 + 4 * a * ⟪v, x⟫_ℝ + 4 * a ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]; ring
  have e2 : 0 ≤ ‖v - (2 * a) • x‖ ^ 2 := sq_nonneg _
  rw [norm_sub_sq_real, norm_smul, inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs] at e2
  rw [e1]
  simp only [inner_add_left, inner_add_right, inner_sub_right, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real, real_inner_self_eq_norm_sq]
  try rw [real_inner_comm g v]
  try rw [real_inner_comm g x]
  try rw [real_inner_comm x v]
  try rw [real_inner_comm x v] at e2
  subst hμ
  have h2 : (1 + r) * (a * (δ + a ^ 2 / 2 * ‖x‖ ^ 2)) ≤ (1 + r) * (a * ⟪g, x⟫_ℝ) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG ha) (by linarith)
  have h3 : 0 ≤ a * (‖v‖ ^ 2 - 2 * (2 * a * ⟪x, v⟫_ℝ) + (2 * a) ^ 2 * ‖x‖ ^ 2) := mul_nonneg ha e2
  have h4 : 0 ≤ a * ‖v‖ ^ 2 := mul_nonneg ha (sq_nonneg _)
  have h5 : 0 ≤ (1 + r) * (a * δ) := mul_nonneg (by linarith) (mul_nonneg ha hδ)
  have h6 : 0 ≤ r * (a * (a ^ 2 * ‖x‖ ^ 2)) := mul_nonneg hr (mul_nonneg ha (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  nlinarith

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


theorem init_num (p r : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1) (hr0 : 0 ≤ r) (hr : r ≤ 1) :
    (1 + r) * p + 2 * p ^ 2 / (1 + r) ^ 2 + r ^ 2 ≤ 7 / 2 := by
  have hq : 0 < (1 + r) ^ 2 := by positivity
  have h1 : 2 * p ^ 2 / (1 + r) ^ 2 ≤ 2 / (1 + r) ^ 2 := by
    apply div_le_div_of_nonneg_right _ hq.le
    nlinarith
  have h2 : 2 / (1 + r) ^ 2 ≤ 7 / 2 - (1 + r) - r ^ 2 := by
    rw [div_le_iff₀ hq]
    nlinarith [mul_nonneg hr0 (mul_nonneg hr0 hr0), mul_nonneg (sub_nonneg.2 hr) hr0,
      mul_nonneg (mul_nonneg (sub_nonneg.2 hr) hr0) hr0]
  nlinarith

theorem init_vec (g w : F) (k a r δ : ℝ) (hk : 0 ≤ k) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hδ : 0 ≤ δ) (hG : δ ≤ ⟪g, w⟫_ℝ) :
    (1 + r) * δ + 1 / 4 * ‖-k • g‖ ^ 2 + 1 / 4 * ‖-k • g + (2 * a) • w‖ ^ 2
      ≤ (1 + r) * ⟪g, w⟫_ℝ + 1 / 2 * k ^ 2 * ‖g‖ ^ 2 + a ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, mul_pow, mul_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  simp only [RCLike.conj_to_real]
  have h1 : 0 ≤ a * k * ⟪g, w⟫_ℝ := mul_nonneg (mul_nonneg ha hk) (hδ.trans hG)
  have h2 : (1 + r) * δ ≤ (1 + r) * ⟪g, w⟫_ℝ := mul_le_mul_of_nonneg_left hG (by linarith)
  nlinarith

theorem init_bound (s L r μ G N d k : ℝ) (hs : 0 < s) (hL : 0 < L) (hsL : s * L ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hμ : μ * s = r ^ 2) (hG : G ≤ L * d ^ 2) (hN0 : 0 ≤ N)
    (hN : N ≤ L * d) (hk : k ^ 2 = 4 * s / (1 + r) ^ 2) :
    (1 + r) * G + 1 / 2 * k ^ 2 * N ^ 2 + μ * d ^ 2 ≤ 7 * d ^ 2 / (2 * s) := by
  have hq : 0 < (1 + r) ^ 2 := by positivity
  have hp0 : 0 ≤ s * L := by positivity
  have hnum := init_num (s * L) r hp0 hsL hr0 hr1
  rw [le_div_iff₀ (by positivity)]
  have e1 : 1 / 2 * k ^ 2 * N ^ 2 * (2 * s) = 2 * (2 * (s * N) ^ 2 / (1 + r) ^ 2) := by
    rw [hk]; field_simp; ring
  have e2 : (s * N) ^ 2 ≤ (s * L) ^ 2 * d ^ 2 := by
    have : s * N ≤ s * L * d := by nlinarith
    have : 0 ≤ s * N := by positivity
    nlinarith
  have e3 : 2 * (s * N) ^ 2 / (1 + r) ^ 2 ≤ 2 * (s * L) ^ 2 / (1 + r) ^ 2 * d ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hq.le
    nlinarith
  have e4 : (1 + r) * G * (2 * s) ≤ 2 * ((1 + r) * (s * L)) * d ^ 2 := by
    have : 0 ≤ (1 + r) * (2 * s) := by positivity
    nlinarith
  have e5 : μ * d ^ 2 * (2 * s) = 2 * r ^ 2 * d ^ 2 := by rw [← hμ]; ring
  have hd : 0 ≤ d ^ 2 := sq_nonneg d
  have e6 := mul_le_mul_of_nonneg_right hnum hd
  nlinarith

end RRAux_HighResODE_HeavyBallODE_theorem_2

open scoped InnerProductSpace
open RRAux_HighResODE_HeavyBallODE_theorem_2

open HighResODE.HeavyBallODE in
theorem solution {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (μ L s : ℝ) (hf : IsS2 f μ L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (hsL : s ≤ 1 / L) (x0 : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n)
    (hsol : IsHeavyBallODE f μ s x0 X V) :
    ∀ t : ℝ, 0 ≤ t →
      f (X t) - f xs ≤ 7 * ‖x0 - xs‖ ^ 2 / (2 * s) * Real.exp (-(Real.sqrt μ * t / 4)) := by
  intro t ht
  obtain ⟨⟨hL, hdiff, hconv, hlip⟩, hμpos, hμL, hsc⟩ := hf.S1
  have hg0 : gradient f xs = 0 := by
    have hlm : IsLocalMin f xs := Filter.Eventually.of_forall hmin
    unfold gradient
    rw [hlm.fderiv_eq_zero, map_zero]
  have ha : 0 ≤ Real.sqrt μ := Real.sqrt_nonneg _
  have hr : 0 ≤ Real.sqrt (μ * s) := Real.sqrt_nonneg _
  have ha2 : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμpos.le
  -- derivative of the Lyapunov function
  have hderiv : ∀ u, 0 ≤ u → HasDerivWithinAt (lyap f μ s xs X V)
      ((1 + Real.sqrt (μ * s)) * ⟪gradient f (X u), V u⟫_ℝ
        + 1 / 4 * (2 * ⟪V u, -(2 * Real.sqrt μ) • V u - (1 + Real.sqrt (μ * s)) • gradient f (X u)⟫_ℝ)
        + 1 / 4 * (2 * ⟪V u + (2 * Real.sqrt μ) • (X u - xs),
            (-(2 * Real.sqrt μ) • V u - (1 + Real.sqrt (μ * s)) • gradient f (X u))
              + (2 * Real.sqrt μ) • V u⟫_ℝ)) (Set.Ici 0) u := by
    intro u hu
    have hX := hsol.deriv_pos u hu
    have hV := hsol.deriv_vel u hu
    have h1 : HasDerivWithinAt (fun w => f (X w)) ⟪gradient f (X u), V u⟫_ℝ (Set.Ici 0) u := by
      have := (hdiff (X u)).hasFDerivAt.comp_hasDerivWithinAt u hX
      have e : ⟪gradient f (X u), V u⟫_ℝ = fderiv ℝ f (X u) (V u) := by
        unfold gradient; exact InnerProductSpace.toDual_symm_apply
      rw [e]; exact this
    have hW := hV.add ((hX.sub_const xs).const_smul (2 * Real.sqrt μ))
    have tot := (((h1.sub_const (f xs)).const_mul (1 + Real.sqrt (μ * s))).add
      ((hV.norm_sq).const_mul (1 / 4))).add ((hW.norm_sq).const_mul (1 / 4))
    exact tot
  have hdec := decay (lyap f μ s xs X V) _ (Real.sqrt μ / 4) hderiv (by
    intro u hu
    have hδ : 0 ≤ f (X u) - f xs := sub_nonneg.2 (hmin _)
    have hG : f (X u) - f xs + μ / 2 * ‖X u - xs‖ ^ 2 ≤ ⟪gradient f (X u), X u - xs⟫_ℝ := by
      have := hsc (X u) xs
      rw [← neg_sub (X u) xs, inner_neg_right, norm_neg] at this
      linarith
    have := key_deriv (V u) (X u - xs) (gradient f (X u)) (Real.sqrt μ) (Real.sqrt (μ * s)) μ
      (f (X u) - f xs) ha hr ha2 hδ hG
    unfold lyap
    linarith) t ht
  -- f(X t) - f xs ≤ lyap t
  have hle : f (X t) - f xs ≤ lyap f μ s xs X V t := by
    unfold lyap
    have hδ : 0 ≤ f (X t) - f xs := sub_nonneg.2 (hmin _)
    have : 0 ≤ Real.sqrt (μ * s) * (f (X t) - f xs) := mul_nonneg hr hδ
    nlinarith [sq_nonneg ‖V t‖, sq_nonneg ‖V t + (2 * Real.sqrt μ) • (X t - xs)‖]
  -- initial bound
  have hsL' : s * L ≤ 1 := by rw [le_div_iff₀ hL] at hsL; linarith
  have hr1 : Real.sqrt (μ * s) ≤ 1 := by
    rw [Real.sqrt_le_one]; nlinarith
  have h0 : lyap f μ s xs X V 0 ≤ 7 * ‖x0 - xs‖ ^ 2 / (2 * s) := by
    unfold lyap
    rw [hsol.init_pos, hsol.init_vel]
    have hk : 0 ≤ 2 * Real.sqrt s / (1 + Real.sqrt (μ * s)) := by positivity
    have hδ : 0 ≤ f x0 - f xs := sub_nonneg.2 (hmin _)
    have hG : f x0 - f xs ≤ ⟪gradient f x0, x0 - xs⟫_ℝ := by
      have := hconv x0 xs
      rw [← neg_sub x0 xs, inner_neg_right] at this
      linarith
    have hv := init_vec (gradient f x0) (x0 - xs) _ _ _ _ hk ha hr hδ hG
    have hN : ‖gradient f x0‖ ≤ L * ‖x0 - xs‖ := by
      have := hlip x0 xs; rwa [hg0, sub_zero] at this
    have hGL : ⟪gradient f x0, x0 - xs⟫_ℝ ≤ L * ‖x0 - xs‖ ^ 2 := by
      have := real_inner_le_norm (gradient f x0) (x0 - xs)
      have := mul_le_mul_of_nonneg_right hN (norm_nonneg (x0 - xs))
      nlinarith
    have hk2 : (2 * Real.sqrt s / (1 + Real.sqrt (μ * s))) ^ 2 = 4 * s / (1 + Real.sqrt (μ * s)) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hs.le]; norm_num
    have hμs : μ * s = Real.sqrt (μ * s) ^ 2 := (Real.sq_sqrt (by positivity)).symm
    have hb := init_bound s L (Real.sqrt (μ * s)) μ _ _ ‖x0 - xs‖ _ hs hL hsL' hr hr1 hμs hGL
      (norm_nonneg _) hN hk2
    rw [ha2] at hv
    linarith
  have hexp : Real.exp (-(Real.sqrt μ / 4 * t)) = Real.exp (-(Real.sqrt μ * t / 4)) := by
    congr 1; ring
  rw [hexp] at hdec
  have hpos := Real.exp_pos (-(Real.sqrt μ * t / 4))
  calc f (X t) - f xs ≤ lyap f μ s xs X V t := hle
    _ ≤ lyap f μ s xs X V 0 * Real.exp (-(Real.sqrt μ * t / 4)) := hdec
    _ ≤ _ := mul_le_mul_of_nonneg_right h0 hpos.le

#print axioms solution
