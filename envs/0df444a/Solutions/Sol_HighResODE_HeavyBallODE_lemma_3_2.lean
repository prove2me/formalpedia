-- Prove2me | solution 1 for HighResODE.HeavyBallODE.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:20:52.805318+00:00
-- url     : https://prove2.me/submissions/07cf3707-e25f-4f83-81c9-4bac75d559b6

import Mathlib
import Definitions.Def_HighResODE_HeavyBallODE_Setting

set_option autoImplicit false

section HlpSec
open scoped InnerProductSpace
open Filter Topology

namespace Hlp
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem inner_grad_eq (f : H → ℝ) (p v : H) : ⟪gradient f p, v⟫_ℝ = fderiv ℝ f p v := by
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]

theorem line_hasDeriv {f : H → ℝ} {p : H} (hp : DifferentiableAt ℝ f p) (x v : H) (t : ℝ)
    (hpt : x + t • v = p) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (⟪gradient f p, v⟫_ℝ) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  rw [inner_grad_eq]
  subst hpt
  exact hp.hasFDerivAt.comp_hasDerivAt t h1

theorem convex_ineq {X : Set H} {f : H → ℝ} (hf : ConvexOn ℝ X f)
    (hd : ∀ x ∈ X, DifferentiableAt ℝ f x) {x y : H} (hx : x ∈ X) (hy : y ∈ X) :
    f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y := by
  have h1 := line_hasDeriv (hd x hx) x (y - x) 0 (by simp)
  have h2 := h1.tendsto_slope_zero_right
  have h3 : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ • ((fun s : ℝ => f (x + s • (y - x))) (0 + t) - (fun s : ℝ => f (x + s • (y - x))) 0)
        ≤ f y - f x := by
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with t ht
    have hc := hf.2 hx hy (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring : (1 - t) + t = 1)
    have e : (1 - t) • x + t • y = x + t • (y - x) := by module
    rw [e] at hc
    simp only [smul_eq_mul, zero_add, zero_smul, add_zero] at hc ⊢
    rw [inv_mul_le_iff₀ ht.1]
    nlinarith
  have := le_of_tendsto h2 h3
  linarith

theorem line_mem {X : Set (H)} (hX : Convex ℝ X) {x y : H} (hx : x ∈ X) (hy : y ∈ X)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : x + t • (y - x) ∈ X := by
  have := hX hx hy (a := 1 - t) (b := t) (by linarith [ht.2]) ht.1 (by ring)
  convert this using 1
  module

theorem descent {X : Set (H)} (hX : Convex ℝ X) {f : H → ℝ}
    (hd : ∀ x ∈ X, DifferentiableAt ℝ f x) {L : ℝ}
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {x y : H} (hx : x ∈ X) (hy : y ∈ X) :
    f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  set v := y - x with hv
  let g : ℝ → ℝ := fun s => f (x + s • v) - s * ⟪gradient f x, v⟫_ℝ - L / 2 * s ^ 2 * ‖v‖ ^ 2
  have hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g
      (⟪gradient f (x + s • v), v⟫_ℝ - ⟪gradient f x, v⟫_ℝ - L * s * ‖v‖ ^ 2) s := by
    intro s hs
    have hm := Hlp.line_mem hX hx hy hs
    have h1 := Hlp.line_hasDeriv (hd _ hm) x v s rfl
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, v⟫_ℝ) (⟪gradient f x, v⟫_ℝ) s := by
      simpa using (hasDerivAt_id s).mul_const (⟪gradient f x, v⟫_ℝ)
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖v‖ ^ 2) (L * s * ‖v‖ ^ 2) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (L / 2)).mul_const (‖v‖ ^ 2)
      refine this.congr_deriv ?_
      first | ring | (norm_num; ring) | norm_num
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn g (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · intro s hs; exact (hder s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hder s (Set.Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs' := Set.Ioo_subset_Icc_self hs
      rw [(hder s hs').deriv]
      have hm := Hlp.line_mem hX hx hy hs'
      have h1 := hL _ hm x hx
      have hn : ‖x + s • v - x‖ = s * ‖v‖ := by
        simp [norm_smul, abs_of_pos hs.1]
      rw [hn] at h1
      have hcs := real_inner_le_norm (gradient f (x + s • v) - gradient f x) v
      rw [inner_sub_left] at hcs
      have h4 := mul_le_mul_of_nonneg_right h1 (norm_nonneg v)
      nlinarith
  have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  have e : x + (1 : ℝ) • v = y := by simp [hv]
  simp only [g, e, zero_smul, add_zero, zero_mul, sub_zero, one_mul, one_pow, mul_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_one] at this
  linarith

theorem cocoercive {f : H → ℝ} (hd : ∀ x, DifferentiableAt ℝ f x) {L : ℝ} (hL0 : 0 < L)
    (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hc : ∀ x y, f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y) (x y : H) :
    ‖gradient f y - gradient f x‖ ^ 2 ≤ 2 * L * (f y - f x - ⟪gradient f x, y - x⟫_ℝ) := by
  set d := gradient f y - gradient f x with hd'
  set z := y - (1 / L) • d with hz
  have h1 := descent (X := Set.univ) convex_univ (f := f) (fun x _ => hd x) (L := L)
    (fun x _ y _ => hL x y) (x := y) (y := z) (Set.mem_univ _) (Set.mem_univ _)
  have h2 := hc x z
  have e1 : z - y = -((1 / L) • d) := by rw [hz]; abel
  have e2 : z - x = (y - x) - (1 / L) • d := by rw [hz]; abel
  rw [e1] at h1
  rw [e2] at h2
  rw [inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs] at h1
  rw [inner_sub_right, real_inner_smul_right] at h2
  have h3 : ⟪gradient f y, d⟫_ℝ - ⟪gradient f x, d⟫_ℝ = ‖d‖ ^ 2 := by
    rw [← inner_sub_left, ← hd', real_inner_self_eq_norm_sq]
  have hq : (1 / L) * L = 1 := by field_simp
  have h4 : L * (1 / L) = 1 := by field_simp
  have key : ‖d‖ ^ 2 ≤ 2 * L * (f y - f x - ⟪gradient f x, y - x⟫_ℝ) := by
    have h5 : f x + (⟪gradient f x, y - x⟫_ℝ - 1 / L * ⟪gradient f x, d⟫_ℝ)
        ≤ f y + (-(1 / L * ⟪gradient f y, d⟫_ℝ)) + L / 2 * (1 / L ^ 2 * ‖d‖ ^ 2) := by
      have : (1 / L) ^ 2 = 1 / L ^ 2 := by rw [one_div_pow]
      rw [this] at h1
      linarith
    have h6 : 1 / L * ⟪gradient f y, d⟫_ℝ - 1 / L * ⟪gradient f x, d⟫_ℝ = 1 / L * ‖d‖ ^ 2 := by
      rw [← mul_sub, h3]
    have h7 : L / 2 * (1 / L ^ 2 * ‖d‖ ^ 2) = 1 / (2 * L) * ‖d‖ ^ 2 := by
      field_simp
    have h8 : f x + ⟪gradient f x, y - x⟫_ℝ + 1 / (2 * L) * ‖d‖ ^ 2 ≤ f y := by
      have : 1 / L * ‖d‖ ^ 2 - 1 / (2 * L) * ‖d‖ ^ 2 = 1 / (2 * L) * ‖d‖ ^ 2 := by
        field_simp; ring
      linarith
    have h9 := mul_le_mul_of_nonneg_left h8 (by linarith : (0:ℝ) ≤ 2 * L)
    have h10 : 2 * L * (1 / (2 * L) * ‖d‖ ^ 2) = ‖d‖ ^ 2 := by field_simp
    nlinarith
  exact key


theorem norm_sub_smul_sq (W g : H) (t : ℝ) :
    ‖W - t • g‖ ^ 2 = ‖W‖ ^ 2 - 2 * t * ⟪g, W⟫_ℝ + t ^ 2 * ‖g‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    ← real_inner_comm W g]
  ring

end Hlp
end HlpSec

namespace HighResODE.HeavyBallODE
open scoped InnerProductSpace

theorem Hlp_B1 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (μ s : ℝ) (hμ : 0 ≤ μ)
    (xs : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n) (t : ℝ) :
    lyap f μ s xs X V t ≤ (1 + Real.sqrt (μ * s)) * (f (X t) - f xs) + 3 / 4 * ‖V t‖ ^ 2
      + 2 * μ * ‖X t - xs‖ ^ 2 := by
  unfold lyap
  have h1 : ‖V t + (2 * Real.sqrt μ) • (X t - xs)‖ ^ 2 ≤
      2 * ‖V t‖ ^ 2 + 2 * ‖(2 * Real.sqrt μ) • (X t - xs)‖ ^ 2 := by
    have := norm_add_le (V t) ((2 * Real.sqrt μ) • (X t - xs))
    have h0 := norm_nonneg (V t + (2 * Real.sqrt μ) • (X t - xs))
    nlinarith [sq_nonneg (‖V t‖ - ‖(2 * Real.sqrt μ) • (X t - xs)‖)]
  have h2 : ‖(2 * Real.sqrt μ) • (X t - xs)‖ ^ 2 = 4 * μ * ‖X t - xs‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hμ]
    ring
  rw [h2] at h1
  nlinarith

theorem Hlp_HB_deriv {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (μ L s : ℝ) (hf : IsS2 f μ L)
    (xs x0 : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n)
    (hsol : IsHeavyBallODE f μ s x0 X V) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (lyap f μ s xs X V)
        ((1 + Real.sqrt (μ * s)) * ⟪gradient f (X t), V t⟫_ℝ
          + 1 / 2 * ⟪V t, -(2 * Real.sqrt μ) • V t - (1 + Real.sqrt (μ * s)) • gradient f (X t)⟫_ℝ
          + 1 / 2 * ⟪V t + (2 * Real.sqrt μ) • (X t - xs),
              -((1 + Real.sqrt (μ * s)) • gradient f (X t))⟫_ℝ)
        (Set.Ici 0) t ∧
      (1 + Real.sqrt (μ * s)) * ⟪gradient f (X t), V t⟫_ℝ
          + 1 / 2 * ⟪V t, -(2 * Real.sqrt μ) • V t - (1 + Real.sqrt (μ * s)) • gradient f (X t)⟫_ℝ
          + 1 / 2 * ⟪V t + (2 * Real.sqrt μ) • (X t - xs),
              -((1 + Real.sqrt (μ * s)) • gradient f (X t))⟫_ℝ
        = -(Real.sqrt μ) *
            (‖V t‖ ^ 2 + (1 + Real.sqrt (μ * s)) * ⟪gradient f (X t), X t - xs⟫_ℝ) := by
  have hfd : DifferentiableAt ℝ f (X t) := hf.S1.isF1.differentiable _
  have hX := hsol.deriv_pos t ht
  have hV := hsol.deriv_vel t ht
  have h1 : HasDerivWithinAt (fun s => f (X s)) ⟪gradient f (X t), V t⟫_ℝ (Set.Ici 0) t := by
    rw [Hlp.inner_grad_eq]
    exact hfd.hasFDerivAt.comp_hasDerivWithinAt t hX
  have h2 := hV.norm_sq
  have h3 : HasDerivWithinAt (fun s => V s + (2 * Real.sqrt μ) • (X s - xs))
      ((-(2 * Real.sqrt μ) • V t - (1 + Real.sqrt (μ * s)) • gradient f (X t))
        + (2 * Real.sqrt μ) • V t) (Set.Ici 0) t :=
    hV.add ((hX.sub_const xs).const_smul (2 * Real.sqrt μ))
  have h4 := h3.norm_sq
  have hA : (-(2 * Real.sqrt μ) • V t - (1 + Real.sqrt (μ * s)) • gradient f (X t))
        + (2 * Real.sqrt μ) • V t = -((1 + Real.sqrt (μ * s)) • gradient f (X t)) := by module
  rw [hA] at h4
  have h5 := (((h1.sub_const (f xs)).const_mul (1 + Real.sqrt (μ * s))).add
    (h2.const_mul (1 / 4))).add (h4.const_mul (1 / 4))
  refine ⟨?_, ?_⟩
  · unfold lyap
    refine h5.congr_deriv ?_
    ring
  · simp only [inner_sub_right, inner_add_left, inner_neg_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, inner_sub_left,
      real_inner_comm (gradient f (X t)) (V t), real_inner_comm (gradient f (X t)) (X t),
      real_inner_comm (gradient f (X t)) xs]
    ring

theorem Hlp_HB_decay {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (μ L s : ℝ) (hf : IsS2 f μ L)
    (xs : HighResODE.NAGSC.E n) (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s)
    (x0 : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n)
    (hsol : IsHeavyBallODE f μ s x0 X V) :
    ∀ t : ℝ, 0 ≤ t → ∃ e' : ℝ, HasDerivWithinAt (lyap f μ s xs X V) e' (Set.Ici 0) t ∧
      e' ≤ -(Real.sqrt μ / 4) * lyap f μ s xs X V t := by
  intro t ht
  obtain ⟨hD, hE⟩ := Hlp_HB_deriv f μ L s hf xs x0 X V hsol t ht
  refine ⟨_, hD, ?_⟩
  rw [hE]
  have hμ : 0 < μ := hf.S1.mu_pos
  have hB := Hlp_B1 f μ s hμ.le xs X V t
  have hsc := hf.S1.strongly_convex (X t) xs
  have e : ⟪gradient f (X t), xs - X t⟫_ℝ = -⟪gradient f (X t), X t - xs⟫_ℝ := by
    rw [← inner_neg_right, neg_sub]
  rw [e, norm_sub_rev xs (X t)] at hsc
  have hsc' : f (X t) - f xs + μ / 2 * ‖X t - xs‖ ^ 2 ≤ ⟪gradient f (X t), X t - xs⟫_ℝ := by
    linarith
  have hf0 : 0 ≤ f (X t) - f xs := sub_nonneg.2 (hmin _)
  have hc1 : 1 ≤ 1 + Real.sqrt (μ * s) := by linarith [Real.sqrt_nonneg (μ * s)]
  have hc0 : 0 ≤ 1 + Real.sqrt (μ * s) := by linarith
  have G1 := mul_le_mul_of_nonneg_left hsc' hc0
  have G2 := mul_nonneg hc0 hf0
  have G3 := mul_nonneg (mul_nonneg (sub_nonneg.2 hc1) hμ.le) (sq_nonneg ‖X t - xs‖)
  have hmain : lyap f μ s xs X V t / 4 ≤ ‖V t‖ ^ 2
      + (1 + Real.sqrt (μ * s)) * ⟪gradient f (X t), X t - xs⟫_ℝ := by
    nlinarith [sq_nonneg ‖V t‖]
  nlinarith [mul_le_mul_of_nonneg_left hmain (Real.sqrt_nonneg μ)]

end HighResODE.HeavyBallODE

open HighResODE.HeavyBallODE
open scoped InnerProductSpace

theorem solution {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (μ L s : ℝ) (hf : IsS2 f μ L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (x0 : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n)
    (hsol : IsHeavyBallODE f μ s x0 X V) :
    ∀ t : ℝ, 0 ≤ t → ∃ e' : ℝ, HasDerivWithinAt (lyap f μ s xs X V) e' (Set.Ici 0) t ∧
      e' ≤ -(Real.sqrt μ / 4) * lyap f μ s xs X V t :=
  Hlp_HB_decay f μ L s hf xs hmin hs x0 X V hsol
