-- Prove2me | solution 1 for HessianDamping.IGAHDSC.theorem_11
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T23:59:07.832369+00:00
-- url     : https://prove2.me/submissions/71e6af8a-c85c-49a6-aa24-63bf598e681f

import Mathlib
import Definitions.Def_HessianDamping_IGAHDSC_Setting

set_option autoImplicit false

namespace IGAHDSCAux

open Set Filter Topology InnerProductSpace

theorem line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (x w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) (inner ℝ (G (x + t • w)) w) t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hF (x + t • w))).comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1

theorem descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {L : ℝ} (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : E) :
    F y ≤ F x + inner ℝ (G x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => F (x + t • w) - t * inner ℝ (G x) w - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (inner ℝ (G (x + t • w)) w - inner ℝ (G x) w
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := line_deriv hF x w t
    have h2 : HasDerivAt (fun s : ℝ => s * inner ℝ (G x) w) (inner ℝ (G x) w) t := by
      simpa using (hasDerivAt_id t).mul_const (inner ℝ (G x) w)
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hle : inner ℝ (G (x + c • w)) w - inner ℝ (G x) w - L / 2 * (2 * c) * ‖w‖ ^ 2 ≤ 0 := by
    have e1 : inner ℝ (G (x + c • w)) w - inner ℝ (G x) w = inner ℝ (G (x + c • w) - G x) w := by
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

/-- First-order inequality for a differentiable `μ`-strongly convex function. -/
theorem sc_first_order {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (hfd : Differentiable ℝ f) (μ : ℝ)
    (hsc : HessianDamping.DINSC.IsStronglyConvex f μ) (y z : H) :
    f y + inner ℝ (gradient f y) (z - y) + μ / 2 * ‖z - y‖ ^ 2 ≤ f z := by
  have h0 : ConvexOn ℝ univ (fun x => f x - μ / 2 * ‖x‖ ^ 2) := hsc
  have hconv : ConvexOn ℝ univ ((fun x => f x - μ / 2 * ‖x‖ ^ 2) ∘ (AffineMap.lineMap y z : ℝ →ᵃ[ℝ] H)) := by
    have := h0.comp_affineMap ((AffineMap.lineMap y z : ℝ →ᵃ[ℝ] H))
    rwa [preimage_univ] at this
  have hl : HasDerivAt ((AffineMap.lineMap y z : ℝ →ᵃ[ℝ] H) : ℝ → H) (z - y) 0 := AffineMap.hasDerivAt_lineMap
  have hl0 : (AffineMap.lineMap y z : ℝ →ᵃ[ℝ] H) (0 : ℝ) = y := AffineMap.lineMap_apply_zero y z
  have hf' : HasDerivAt (fun l => f ((AffineMap.lineMap y z : ℝ →ᵃ[ℝ] H) l)) (inner ℝ (gradient f y) (z - y)) 0 := by
    rw [inner_gradient_left]
    have := (hfd ((AffineMap.lineMap y z : ℝ →ᵃ[ℝ] H) (0 : ℝ))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rw [hl0] at this
    exact this
  have hn := hl.norm_sq
  rw [hl0] at hn
  have hder : HasDerivAt ((fun x => f x - μ / 2 * ‖x‖ ^ 2) ∘ (AffineMap.lineMap y z : ℝ →ᵃ[ℝ] H))
      (inner ℝ (gradient f y) (z - y) - μ / 2 * (2 * inner ℝ y (z - y))) 0 :=
    hf'.sub (hn.const_mul (μ / 2))
  have hsl := hconv.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hder
  rw [slope_def_field] at hsl
  simp only [Function.comp_apply, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    sub_zero, div_one] at hsl
  have e1 : ‖z - y‖ ^ 2 = ‖z‖ ^ 2 - 2 * inner ℝ z y + ‖y‖ ^ 2 := norm_sub_sq_real z y
  have e2 : inner ℝ y (z - y) = inner ℝ z y - ‖y‖ ^ 2 := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm]
  rw [e2] at hsl
  rw [e1]
  linarith

theorem norm3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (e u g : H) (a b c : ℝ) :
    ‖a • e + b • u + c • g‖ ^ 2 = a ^ 2 * ‖e‖ ^ 2 + b ^ 2 * ‖u‖ ^ 2 + c ^ 2 * ‖g‖ ^ 2
      + 2 * a * b * inner ℝ e u + 2 * a * c * inner ℝ e g + 2 * b * c * inner ℝ u g := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [real_inner_comm e u, real_inner_comm e g, real_inner_comm u g]
  ring

theorem quadform {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u w : H) (A b B : ℝ) (hA : 0 < A) (hb : b ^ 2 ≤ A * B) :
    0 ≤ A * ‖u‖ ^ 2 + 2 * b * inner ℝ u w + B * ‖w‖ ^ 2 := by
  have h0 : 0 ≤ ‖A • u + b • w‖ ^ 2 := sq_nonneg _
  have hexp : ‖A • u + b • w‖ ^ 2 = A ^ 2 * ‖u‖ ^ 2 + 2 * A * b * inner ℝ u w + b ^ 2 * ‖w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [real_inner_comm u w]
    ring
  have hw : 0 ≤ (A * B - b ^ 2) * ‖w‖ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have key : 0 ≤ A * (A * ‖u‖ ^ 2 + 2 * b * inner ℝ u w + B * ‖w‖ ^ 2) := by
    nlinarith
  exact (mul_nonneg_iff_of_pos_left hA).1 key

/-- Scalar heart of the IGAHD-SC Lyapunov step `(1 + √(μs)/2) E_{k+1} ≤ E_k`. -/
theorem key {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (e u g : H) (m h β L F0 F1 : ℝ) (hm : 0 < m) (hh : 0 < h) (hβ0 : 0 ≤ β) (hL : 0 < L)
    (hmβ : m * β ≤ 1 / 8) (hmh : m * h ≤ 1)
    (hLc : L * h * (1 + m * h / 2) + 2 * β * m ^ 2 * L * h ^ 2 ≤ m / 2 + m ^ 2 * h)
    (IA : F1 ≤ F0 + h * inner ℝ u g + L * h ^ 2 / 2 * ‖u‖ ^ 2)
    (IB : F0 + m ^ 2 / 2 * ‖e‖ ^ 2 ≤ inner ℝ e g)
    (IM : m ^ 2 * ‖e‖ ^ 2 ≤ inner ℝ e g) :
    (1 + 1 / 2 * (m * h)) * (F1 + 1 / 2 * ‖m • e + (1 : ℝ) • u + β • g‖ ^ 2)
      ≤ F0 + 1 / 2 * ‖m • e + (1 + m * h) • u + (β + h) • g‖ ^ 2 := by
  rw [norm3, norm3]
  have P1 := quadform e u (7 * m ^ 3 / 16) (m ^ 2 / 4) (m / 7) (by positivity) (by
    apply le_of_eq; ring)
  have hmβ0 : 0 ≤ m * β := by positivity
  have t1 : m * (β + h) ≤ 9 / 8 := by linarith
  have t0 : 0 ≤ m * (β + h) := by positivity
  have t2 : (m * (β + h)) ^ 2 ≤ 9 / 8 * (m * (β + h)) := by nlinarith
  have t3 : m * (m * β ^ 2) ≤ m * β / 8 := by
    have := mul_le_mul_of_nonneg_left hmβ hmβ0
    nlinarith
  have P2 := quadform u g (5 * m / 14) (m * (β + h) / 4) (β + h / 2 - m * β ^ 2 / 4)
    (by positivity) (by nlinarith)
  have Q1 := mul_le_mul_of_nonneg_left IA (by positivity : (0 : ℝ) ≤ 1 + 1 / 2 * (m * h))
  have Q2 := mul_le_mul_of_nonneg_left IB (by positivity : (0 : ℝ) ≤ m * h / 2)
  have hc' : 0 ≤ h * (m / 2 * (1 - m * β)) := by
    have : 0 ≤ 1 - m * β := by linarith
    positivity
  have Q3 := mul_le_mul_of_nonneg_left IM hc'
  have Q4 := mul_nonneg hh.le P1
  have Q5 := mul_nonneg hh.le P2
  have h6 : 0 ≤ h * (m ^ 3 * (1 / 16 - m * β / 2)) := by
    have : 0 ≤ 1 / 16 - m * β / 2 := by linarith
    positivity
  have Q6 := mul_nonneg h6 (sq_nonneg ‖e‖)
  have h7 : 0 ≤ h * (m / 4 + m ^ 2 * h / 2 - L * h * (1 + m * h / 2) / 2) := by
    have : 0 ≤ β * m ^ 2 * L * h ^ 2 := by positivity
    have : 0 ≤ m / 4 + m ^ 2 * h / 2 - L * h * (1 + m * h / 2) / 2 := by linarith
    positivity
  have Q7 := mul_nonneg h7 (sq_nonneg ‖u‖)
  linarith

/-- The vector identity `v_k = v_{k+1} + √μ (x_{k+1}-x_k) + √s ∇f(x_k)` from the explicit step. -/
theorem vid {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X1 X0 Xm xs g0 gm : H) (m h β s : ℝ) (hm : 0 < m) (hh : 0 < h) (hs : h ^ 2 = s)
    (hR : X1 = X0 + ((1 - m * h) / (1 + m * h)) • (X0 - Xm)
      - (β * h / (1 + m * h)) • (g0 - gm) - (s / (1 + m * h)) • g0) :
    m • (Xm - xs) + (1 / h) • (X0 - Xm) + β • gm
      = m • (X0 - xs) + (1 + m * h) • ((1 / h) • (X1 - X0)) + (β + h) • g0 := by
  subst hR
  subst hs
  have h1 : (1 + m * h) ≠ 0 := by positivity
  have h2 : h ≠ 0 := hh.ne'
  match_scalars <;> field_simp <;> ring

open HessianDamping.IGAHDSC in
theorem step {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfd : Differentiable ℝ f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : HessianDamping.DINSC.IsStronglyConvex f μ)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ u w : H, ‖gradient f u - gradient f w‖ ≤ L * ‖u - w‖)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y) (hgx : gradient f xstar = 0)
    (β s : ℝ) (hs : 0 < s) (hβ0 : 0 ≤ β)
    (hmβ : Real.sqrt μ * β ≤ 1 / 8) (hmh1 : Real.sqrt μ * Real.sqrt s ≤ 1)
    (hLc : L * Real.sqrt s * (1 + Real.sqrt μ * Real.sqrt s / 2)
      + 2 * β * Real.sqrt μ ^ 2 * L * Real.sqrt s ^ 2 ≤ Real.sqrt μ / 2 + Real.sqrt μ ^ 2 * Real.sqrt s)
    (x : ℕ → H) (hrun : IsIGAHDSCRun f μ β s x) (k : ℕ) (hk : 1 ≤ k) :
    (1 + 1 / 2 * Real.sqrt (μ * s)) * EK f μ β s x xstar (k + 1) ≤ EK f μ β s x xstar k := by
  have hm : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have hh : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hmh : Real.sqrt (μ * s) = Real.sqrt μ * Real.sqrt s := Real.sqrt_mul hμ.le s
  have hs2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hμ2 : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ.le
  have hX := hrun k hk
  dsimp only at hX
  rw [hmh] at hX
  have hv := vid (x (k + 1)) (x k) (x (k - 1)) xstar (gradient f (x k)) (gradient f (x (k - 1)))
    (Real.sqrt μ) (Real.sqrt s) β s hm hh hs2 hX
  set e := x k - xstar with he
  set u := (1 / Real.sqrt s) • (x (k + 1) - x k) with hu
  set g := gradient f (x k) with hg
  have hd : x (k + 1) - x k = Real.sqrt s • u := by
    rw [hu, smul_smul, mul_one_div_cancel hh.ne', one_smul]
  have hF : ∀ z, HasGradientAt f (gradient f z) z := fun z => (hfd z).hasGradientAt
  have IA : f (x (k + 1)) - f xstar ≤ (f (x k) - f xstar) + Real.sqrt s * inner ℝ u g
      + L * Real.sqrt s ^ 2 / 2 * ‖u‖ ^ 2 := by
    have := descent hF hLip (x k) (x (k + 1))
    rw [hd, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hh,
      real_inner_comm u g, mul_pow] at this
    linarith
  have IB : (f (x k) - f xstar) + Real.sqrt μ ^ 2 / 2 * ‖e‖ ^ 2 ≤ inner ℝ e g := by
    have := sc_first_order f hfd μ hsc (x k) xstar
    have e1 : xstar - x k = -e := by rw [he]; abel
    rw [e1, inner_neg_right, norm_neg, real_inner_comm e g] at this
    rw [hμ2]
    linarith
  have IM : Real.sqrt μ ^ 2 * ‖e‖ ^ 2 ≤ inner ℝ e g := by
    have := sc_first_order f hfd μ hsc xstar (x k)
    rw [hgx, inner_zero_left, ← he] at this
    have IB' := IB
    rw [hμ2] at IB' ⊢
    linarith
  have K := key e u g (Real.sqrt μ) (Real.sqrt s) β L _ _ hm hh hβ0 hL hmβ hmh1 hLc IA IB IM
  have hvk : vK f μ β s x xstar k = Real.sqrt μ • e + (1 + Real.sqrt μ * Real.sqrt s) • u
      + (β + Real.sqrt s) • g := by
    simp only [vK]
    exact hv
  have hvk1 : vK f μ β s x xstar (k + 1) = Real.sqrt μ • e + (1 : ℝ) • u + β • g := by
    simp only [vK, Nat.add_sub_cancel, one_smul]
    rfl
  simp only [EK]
  rw [hvk, hvk1, hmh]
  linarith

end IGAHDSCAux

open HessianDamping.IGAHDSC in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (hfC1 : ContDiff ℝ 1 f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : HessianDamping.DINSC.IsStronglyConvex f μ)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ u w : H, ‖gradient f u - gradient f w‖ ≤ L * ‖u - w‖)
    (xstar : H) (hxstar : ∀ y : H, f xstar ≤ f y)
    (β s : ℝ) (hs : 0 < s) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / Real.sqrt μ)
    (hL1 : 8 * β * L ≤ Real.sqrt μ)
    (hL2 : L ≤ (Real.sqrt μ / (2 * s) + μ / Real.sqrt s) /
      (2 * β * μ + 1 / Real.sqrt s + Real.sqrt μ / 2))
    (x : ℕ → H) (hrun : IsIGAHDSCRun f μ β s x) :
    (fun k : ℕ => ‖x k - xstar‖) =O[Filter.atTop]
        (fun k : ℕ => Real.sqrt (HessianDamping.IPAHDSC.qRate μ s) ^ k) ∧
      (fun k : ℕ => f (x k) - f xstar) =O[Filter.atTop]
        (fun k : ℕ => HessianDamping.IPAHDSC.qRate μ s ^ k) ∧
      (fun k : ℕ => HessianDamping.IPAHDSC.thetaRate μ s ^ k *
        ∑ j ∈ Finset.range (k - 1),
          (1 / HessianDamping.IPAHDSC.thetaRate μ s) ^ j * ‖gradient f (x j)‖ ^ 2) =O[Filter.atTop]
        (fun k : ℕ => HessianDamping.IPAHDSC.qRate μ s ^ k) := by
  have hfd : Differentiable ℝ f := hfC1.differentiable (by norm_num)
  have hgx : gradient f xstar = 0 := by
    have hlm : IsLocalMin f xstar := Filter.Eventually.of_forall hxstar
    have := hlm.fderiv_eq_zero
    simp [gradient, this]
  rcases subsingleton_or_nontrivial H with hH | hH
  · have hx : ∀ k, x k = xstar := fun k => Subsingleton.elim _ _
    have hg : ∀ j, gradient f (x j) = 0 := fun j => Subsingleton.elim _ _
    refine ⟨?_, ?_, ?_⟩
    · simp only [hx, sub_self, norm_zero]
      exact Asymptotics.isBigO_zero _ _
    · simp only [hx, sub_self]
      exact Asymptotics.isBigO_zero _ _
    · simp only [hg, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        Finset.sum_const_zero]
      exact Asymptotics.isBigO_zero _ _
  have hm : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have hh : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hs2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hμ2 : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ.le
  -- L ≥ μ
  have hLμ : μ ≤ L := by
    obtain ⟨v, hv⟩ := exists_ne (0 : H)
    have s1 := IGAHDSCAux.sc_first_order f hfd μ hsc (xstar + v) xstar
    have s2 := IGAHDSCAux.sc_first_order f hfd μ hsc xstar (xstar + v)
    have e1 : xstar - (xstar + v) = -v := by abel
    have e2 : xstar + v - xstar = v := by abel
    rw [e1, inner_neg_right, norm_neg] at s1
    rw [e2, hgx, inner_zero_left] at s2
    have c1 := real_inner_le_norm (gradient f (xstar + v)) v
    have c2 := hLip (xstar + v) xstar
    rw [hgx, sub_zero, e2] at c2
    have c3 : ‖gradient f (xstar + v)‖ * ‖v‖ ≤ L * ‖v‖ * ‖v‖ :=
      mul_le_mul_of_nonneg_right c2 (norm_nonneg _)
    have hvp : 0 < ‖v‖ := norm_pos_iff.2 hv
    have : μ * ‖v‖ ^ 2 ≤ L * ‖v‖ ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right this (by positivity)
  set m := Real.sqrt μ with hm_def
  set h := Real.sqrt s with hh_def
  have hLc : L * h * (1 + m * h / 2) + 2 * β * m ^ 2 * L * h ^ 2 ≤ m / 2 + m ^ 2 * h := by
    have hden : 0 < 2 * β * μ + 1 / h + m / 2 := by positivity
    rw [le_div_iff₀ hden] at hL2
    have k2 := mul_le_mul_of_nonneg_left hL2 (sq_nonneg h)
    rw [← hμ2, ← hs2] at k2
    have e1 : h ^ 2 * (L * (2 * β * m ^ 2 + 1 / h + m / 2))
        = L * h * (1 + m * h / 2) + 2 * β * m ^ 2 * L * h ^ 2 := by
      field_simp; ring
    have e2 : h ^ 2 * (m / (2 * h ^ 2) + m ^ 2 / h) = m / 2 + m ^ 2 * h := by
      field_simp
    rw [e1, e2] at k2
    exact k2
  have hmβ : m * β ≤ 1 / 8 := by
    have : m ^ 2 * (8 * β) ≤ L * (8 * β) := mul_le_mul_of_nonneg_right (by rw [hμ2]; exact hLμ) (by positivity)
    have h8 : m * (8 * (m * β)) ≤ m * 1 := by nlinarith
    have := le_of_mul_le_mul_left h8 hm
    linarith
  have hmh1 : m * h ≤ 1 := by
    have hLm : m ^ 2 ≤ L := by rw [hμ2]; exact hLμ
    have t1 : 0 ≤ 2 * β * m ^ 2 * L * h ^ 2 := by positivity
    have t2 : m ^ 2 * h * (1 + m * h / 2) ≤ L * h * (1 + m * h / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLm hh.le) (by positivity)
    have t3 : m * (m * (m * h ^ 2)) ≤ m * 1 := by nlinarith
    have t4 := le_of_mul_le_mul_left t3 hm
    nlinarith
  have hstep := fun k (hk : 1 ≤ k) =>
    IGAHDSCAux.step f hfd μ hμ hsc L hL hLip xstar hxstar hgx β s hs hβ0 hmβ hmh1 hLc x hrun k hk
  have ha : 0 < Real.sqrt (μ * s) := Real.sqrt_pos.2 (mul_pos hμ hs)
  set a := Real.sqrt (μ * s) with ha_def
  have hq0 : 0 < HessianDamping.IPAHDSC.qRate μ s := by
    unfold HessianDamping.IPAHDSC.qRate; positivity
  have hθ0 : 0 < HessianDamping.IPAHDSC.thetaRate μ s := by
    unfold HessianDamping.IPAHDSC.thetaRate; positivity
  have hθq : HessianDamping.IPAHDSC.thetaRate μ s < HessianDamping.IPAHDSC.qRate μ s := by
    unfold HessianDamping.IPAHDSC.thetaRate HessianDamping.IPAHDSC.qRate
    apply one_div_lt_one_div_of_lt (by positivity)
    linarith
  set q := HessianDamping.IPAHDSC.qRate μ s with hq_def
  set θ := HessianDamping.IPAHDSC.thetaRate μ s with hθ_def
  have hqa : q * (1 + 1 / 2 * a) = 1 := by
    rw [hq_def]; unfold HessianDamping.IPAHDSC.qRate; rw [← ha_def]; field_simp
  have hEF : ∀ k, f (x k) - f xstar ≤ EK f μ β s x xstar k := by
    intro k; simp only [EK]
    have := sq_nonneg ‖vK f μ β s x xstar k‖
    linarith
  have hEnn : ∀ k, 0 ≤ EK f μ β s x xstar k := fun k =>
    le_trans (by linarith [hxstar (x k)]) (hEF k)
  have hrec : ∀ k, 1 ≤ k → EK f μ β s x xstar (k + 1) ≤ q * EK f μ β s x xstar k := by
    intro k hk
    have h3 := hstep k hk
    calc EK f μ β s x xstar (k + 1) = q * ((1 + 1 / 2 * a) * EK f μ β s x xstar (k + 1)) := by
          rw [← mul_assoc, hqa, one_mul]
      _ ≤ q * EK f μ β s x xstar k := mul_le_mul_of_nonneg_left h3 hq0.le
  set E1 := EK f μ β s x xstar 1 with hE1
  have hpow : ∀ n : ℕ, EK f μ β s x xstar (n + 1) ≤ E1 * q ^ n := by
    intro n
    induction n with
    | zero => simp [hE1]
    | succ n ih =>
      calc EK f μ β s x xstar (n + 1 + 1) ≤ q * EK f μ β s x xstar (n + 1) := hrec (n + 1) (by omega)
        _ ≤ q * (E1 * q ^ n) := mul_le_mul_of_nonneg_left ih hq0.le
        _ = E1 * q ^ (n + 1) := by ring
  have hE1nn : 0 ≤ E1 := hEnn 1
  have hF0 : 0 ≤ f (x 0) - f xstar := by linarith [hxstar (x 0)]
  set C := E1 / q + (f (x 0) - f xstar) with hC
  have hCnn : 0 ≤ C := by positivity
  have hF : ∀ k, f (x k) - f xstar ≤ C * q ^ k := by
    intro k
    match k with
    | 0 =>
      have : 0 ≤ E1 / q := by positivity
      simp only [pow_zero, mul_one]; linarith
    | n + 1 =>
      have h1 := hEF (n + 1)
      have h2 := hpow n
      have e : E1 * q ^ n = E1 / q * q ^ (n + 1) := by field_simp; ring
      have h3 : 0 ≤ (f (x 0) - f xstar) * q ^ (n + 1) := by positivity
      calc f (x (n + 1)) - f xstar ≤ E1 / q * q ^ (n + 1) := by linarith
        _ ≤ C * q ^ (n + 1) := by rw [hC, add_mul]; linarith
  set D := 2 / μ * C with hD
  have hDnn : 0 ≤ D := by positivity
  have hdist : ∀ k, ‖x k - xstar‖ ^ 2 ≤ D * q ^ k := by
    intro k
    have s1 := IGAHDSCAux.sc_first_order f hfd μ hsc xstar (x k)
    rw [hgx, inner_zero_left] at s1
    have h1 : μ / 2 * ‖x k - xstar‖ ^ 2 ≤ C * q ^ k := by linarith [hF k]
    calc ‖x k - xstar‖ ^ 2 = 2 / μ * (μ / 2 * ‖x k - xstar‖ ^ 2) := by field_simp
      _ ≤ 2 / μ * (C * q ^ k) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = D * q ^ k := by rw [hD]; ring
  set K := L ^ 2 * D with hK
  have hKnn : 0 ≤ K := by positivity
  have hgrad : ∀ j : ℕ, ‖gradient f (x j)‖ ^ 2 ≤ K * q ^ j := by
    intro j
    have c1 := hLip (x j) xstar
    rw [hgx, sub_zero] at c1
    have c2 : ‖gradient f (x j)‖ ^ 2 ≤ (L * ‖x j - xstar‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) c1 2
    rw [mul_pow] at c2
    calc ‖gradient f (x j)‖ ^ 2 ≤ L ^ 2 * ‖x j - xstar‖ ^ 2 := c2
      _ ≤ L ^ 2 * (D * q ^ j) := mul_le_mul_of_nonneg_left (hdist j) (by positivity)
      _ = K * q ^ j := by rw [hK]; ring
  refine ⟨?_, ?_, ?_⟩
  · refine Asymptotics.IsBigO.of_bound (Real.sqrt D) (Filter.Eventually.of_forall fun k => ?_)
    rw [norm_norm, Real.norm_of_nonneg (by positivity)]
    have hsq : (Real.sqrt D * Real.sqrt q ^ k) ^ 2 = D * q ^ k := by
      rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul, Real.sq_sqrt hDnn, Real.sq_sqrt hq0.le]
    have h1 : ‖x k - xstar‖ ^ 2 ≤ (Real.sqrt D * Real.sqrt q ^ k) ^ 2 := by
      rw [hsq]; exact hdist k
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1
  · refine Asymptotics.IsBigO.of_bound C (Filter.Eventually.of_forall fun k => ?_)
    rw [Real.norm_of_nonneg (by linarith [hxstar (x k)]), Real.norm_of_nonneg (by positivity)]
    exact hF k
  · have hr1 : 1 < q / θ := (one_lt_div hθ0).2 hθq
    set r := q / θ with hr_def
    have hθr : θ * r = q := by rw [hr_def]; field_simp
    have hterm : ∀ j : ℕ, (1 / θ) ^ j * ‖gradient f (x j)‖ ^ 2 ≤ K * r ^ j := by
      intro j
      calc (1 / θ) ^ j * ‖gradient f (x j)‖ ^ 2 ≤ (1 / θ) ^ j * (K * q ^ j) :=
            mul_le_mul_of_nonneg_left (hgrad j) (by positivity)
        _ = K * r ^ j := by
            rw [← hθr, mul_pow, one_div_pow]
            field_simp
    have hS : ∀ k : ℕ, 0 ≤ θ ^ k *
        ∑ j ∈ Finset.range (k - 1), (1 / θ) ^ j * ‖gradient f (x j)‖ ^ 2 ∧
        θ ^ k * ∑ j ∈ Finset.range (k - 1), (1 / θ) ^ j * ‖gradient f (x j)‖ ^ 2
          ≤ K / (r - 1) * q ^ k := by
      intro k
      constructor
      · apply mul_nonneg (by positivity)
        apply Finset.sum_nonneg
        intro j _
        exact mul_nonneg (by positivity) (sq_nonneg _)
      · have s1 : ∑ j ∈ Finset.range (k - 1), (1 / θ) ^ j * ‖gradient f (x j)‖ ^ 2
            ≤ ∑ j ∈ Finset.range (k - 1), K * r ^ j := Finset.sum_le_sum (fun j _ => hterm j)
        have s2 : ∑ j ∈ Finset.range (k - 1), K * r ^ j ≤ ∑ j ∈ Finset.range k, K * r ^ j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le k 1))
            (fun j _ _ => by have : 0 < r := by linarith
                             positivity)
        have s3 : ∑ j ∈ Finset.range k, K * r ^ j = K * ((r ^ k - 1) / (r - 1)) := by
          rw [← Finset.mul_sum, geom_sum_eq (ne_of_gt hr1)]
        have s4 : θ ^ k * (K * ((r ^ k - 1) / (r - 1))) = K / (r - 1) * (θ ^ k * r ^ k - θ ^ k) := by
          ring
        have s5 : θ ^ k * r ^ k = q ^ k := by rw [← mul_pow, hθr]
        have hθk : 0 ≤ θ ^ k := by positivity
        have hKr : 0 ≤ K / (r - 1) := div_nonneg hKnn (by linarith)
        calc θ ^ k * ∑ j ∈ Finset.range (k - 1), (1 / θ) ^ j * ‖gradient f (x j)‖ ^ 2
            ≤ θ ^ k * (K * ((r ^ k - 1) / (r - 1))) :=
              mul_le_mul_of_nonneg_left (by linarith) hθk
          _ = K / (r - 1) * (θ ^ k * r ^ k - θ ^ k) := s4
          _ ≤ K / (r - 1) * q ^ k := by
              rw [s5]; exact mul_le_mul_of_nonneg_left (by linarith) hKr
    refine Asymptotics.IsBigO.of_bound (K / (r - 1)) (Filter.Eventually.of_forall fun k => ?_)
    rw [Real.norm_of_nonneg (hS k).1, Real.norm_of_nonneg (by positivity)]
    exact (hS k).2
