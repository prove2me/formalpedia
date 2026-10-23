-- Prove2me | solution 1 for HessianDamping.IPAHDSC.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T15:34:45.210994+00:00
-- url     : https://prove2.me/submissions/ff315cbd-d362-4f13-a22c-a982d8646a86

import Mathlib
import Definitions.Def_HessianDamping_IPAHDSC_Setting

set_option autoImplicit false

namespace IPAHDSCAux

open Set Filter Topology InnerProductSpace

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

/-- Optimality condition of the proximal step. -/
theorem prox_grad {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (hfd : Differentiable ℝ f) (γ : ℝ) (y X : H)
    (hP : GoldenRatioVI.Shared.IsProxPoint (fun z => ((γ * f z : ℝ) : EReal)) y X) :
    X = y - γ • gradient f X := by
  have hmin : IsLocalMin (fun z => γ * f z + (1 / 2 : ℝ) * ‖z - y‖ ^ 2) X := by
    refine Filter.Eventually.of_forall (fun z => ?_)
    have := hP z
    dsimp only at this
    have h2 : γ * f X + ‖X - y‖ ^ 2 / 2 ≤ γ * f z + ‖z - y‖ ^ 2 / 2 := by
      exact_mod_cast this
    show γ * f X + (1 / 2 : ℝ) * ‖X - y‖ ^ 2 ≤ γ * f z + (1 / 2 : ℝ) * ‖z - y‖ ^ 2
    linarith
  have h1 := (hfd X).hasFDerivAt.const_mul γ
  have h2 := ((hasFDerivAt_id X).sub_const y).norm_sq.const_mul (1 / 2 : ℝ)
  have hd := h1.add h2
  have h0 := hmin.hasFDerivAt_eq_zero hd
  have hv : inner ℝ (γ • gradient f X + (X - y)) (γ • gradient f X + (X - y)) = 0 := by
    have := congrArg (fun L : H →L[ℝ] ℝ => L (γ • gradient f X + (X - y))) h0
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.zero_apply, smul_eq_mul, nsmul_eq_mul] at this
    rw [← inner_gradient_left] at this
    simp only [innerSL_apply_apply, id_eq, Nat.cast_ofNat] at this
    rw [inner_add_left, real_inner_smul_left]
    linarith
  have hv' : γ • gradient f X + (X - y) = 0 := inner_self_eq_zero.1 hv
  calc X = y - γ • gradient f X + (γ • gradient f X + (X - y)) := by abel
    _ = y - γ • gradient f X := by rw [hv', add_zero]

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

/-- The scalar heart of the Lyapunov step `(1 + √(μs)/2) E_{k+1} + (s/4)‖∇f(x_{k+1})‖² ≤ E_k`. -/
theorem key {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (e u g : H) (m h β F0 F1 : ℝ) (hm : 0 < m) (hh : 0 < h) (hβ0 : 0 ≤ β) (hβm : β * m ≤ 1 / 2)
    (I1 : F1 - h * inner ℝ u g + m ^ 2 * h ^ 2 / 2 * ‖u‖ ^ 2 ≤ F0)
    (I2 : F1 + m ^ 2 / 2 * ‖e‖ ^ 2 ≤ inner ℝ e g) (I3 : 0 ≤ F1) :
    (1 + 1 / 2 * (m * h)) * (F1 + 1 / 2 * ‖m • e + (1 : ℝ) • u + β • g‖ ^ 2) + h ^ 2 / 4 * ‖g‖ ^ 2
      ≤ F0 + 1 / 2 * ‖m • e + (1 + m * h) • u + (β + h) • g‖ ^ 2 := by
  rw [norm3, norm3]
  have hmb : 0 ≤ m * β := by positivity
  have hA : 0 < m ^ 3 / 4 * (1 - m * β) := by
    have : 0 < 1 - m * β := by linarith
    positivity
  have P1 := quadform e u (m ^ 3 / 4 * (1 - m * β)) (m ^ 2 / 4) (m / 2) hA (by
    nlinarith [mul_nonneg (pow_nonneg hm.le 4) (by linarith : (0 : ℝ) ≤ 1 / 2 - m * β)])
  have hB : 0 < m ^ 2 * h + m / 4 := by positivity
  have P2 := quadform u g (m ^ 2 * h + m / 4) (β * m / 4 + h * m / 2) (β + h / 4 - m * β ^ 2 / 4) hB (by
    have hx1 : 0 ≤ m ^ 2 * h * β * (1 / 2 - m * β) :=
      mul_nonneg (by positivity) (by linarith)
    have hx2 : 0 ≤ m * β * (1 / 2 - m * β) := mul_nonneg hmb (by linarith)
    have hx3 : 0 ≤ m ^ 2 * h * β := by positivity
    have hx4 : 0 ≤ m * h := by positivity
    nlinarith)
  have hc : 0 ≤ h * m - m ^ 2 * h * β / 2 := by
    have : 0 ≤ h * m * (1 - m * β / 2) := mul_nonneg (by positivity) (by linarith)
    linarith
  have hc' : 0 ≤ h * m * (1 - m * β) / 2 := by
    have : 0 ≤ h * m * (1 - m * β) := mul_nonneg (by positivity) (by linarith)
    linarith
  have Q1 := mul_le_mul_of_nonneg_left I2 hc
  have Q2 := mul_nonneg hc' I3
  have Q3 := mul_nonneg hh.le P1
  have Q4 := mul_nonneg hh.le P2
  linarith

/-- The vector identity `v_k = v_{k+1} + √μ (x_{k+1}-x_k) + √s ∇f(x_{k+1})` from the prox step. -/
theorem vid {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X1 X0 Xm xs g g0 : H) (m h β s : ℝ) (hm : 0 < m) (hh : 0 < h) (hs : h ^ 2 = s)
    (hR : X1 = X0 + (1 - 2 * (m * h) / (1 + 2 * (m * h))) • (X0 - Xm)
      + (β * h * (1 - 2 * (m * h) / (1 + 2 * (m * h)))) • g0
      - ((β * h + s) / (1 + 2 * (m * h))) • g) :
    m • (X0 - xs) + (1 / h) • (X0 - Xm) + β • g0
      = m • (X1 - xs) + (1 + m * h) • ((1 / h) • (X1 - X0)) + (β + h) • g := by
  subst hR
  subst hs
  have h1 : (1 + 2 * (m * h)) ≠ 0 := by positivity
  have h2 : h ≠ 0 := hh.ne'
  match_scalars <;> field_simp <;> ring

end IPAHDSCAux

open HessianDamping.IPAHDSC IPAHDSCAux in
theorem IPAHDSCAux_step {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfd : Differentiable ℝ f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : HessianDamping.DINSC.IsStronglyConvex f μ)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (β s : ℝ) (hs : 0 < s) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (2 * Real.sqrt μ))
    (x : ℕ → H) (hrun : IsIPAHDSCRun f μ β s x) (k : ℕ) (hk : 1 ≤ k) :
    (1 + 1 / 2 * Real.sqrt (μ * s)) * EK f μ β s x xstar (k + 1)
      + s / 4 * ‖gradient f (x (k + 1))‖ ^ 2 ≤ EK f μ β s x xstar k := by
  have hm : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have hh : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hmh : Real.sqrt (μ * s) = Real.sqrt μ * Real.sqrt s := Real.sqrt_mul hμ.le s
  have hs2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hμ2 : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ.le
  have hβm : β * Real.sqrt μ ≤ 1 / 2 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt μ)).1 hβ
    linarith
  have hX := prox_grad f hfd _ _ _ (hrun k hk)
  simp only [yK, gammaStep] at hX
  rw [hmh] at hX
  have hv := vid (x (k + 1)) (x k) (x (k - 1)) xstar (gradient f (x (k + 1))) (gradient f (x k))
    (Real.sqrt μ) (Real.sqrt s) β s hm hh hs2 hX
  set e := x (k + 1) - xstar with he
  set u := (1 / Real.sqrt s) • (x (k + 1) - x k) with hu
  set g := gradient f (x (k + 1)) with hg
  have hd : x (k + 1) - x k = Real.sqrt s • u := by
    rw [hu, smul_smul, mul_one_div_cancel hh.ne', one_smul]
  have I1 : (f (x (k + 1)) - f xstar) - Real.sqrt s * inner ℝ u g
      + Real.sqrt μ ^ 2 * Real.sqrt s ^ 2 / 2 * ‖u‖ ^ 2 ≤ f (x k) - f xstar := by
    have := sc_first_order f hfd μ hsc (x (k + 1)) (x k)
    have e1 : x k - x (k + 1) = -(Real.sqrt s • u) := by rw [← hd]; abel
    rw [e1, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos hh, real_inner_comm] at this
    rw [hμ2]
    nlinarith
  have I2 : (f (x (k + 1)) - f xstar) + Real.sqrt μ ^ 2 / 2 * ‖e‖ ^ 2 ≤ inner ℝ e g := by
    have := sc_first_order f hfd μ hsc (x (k + 1)) xstar
    have e1 : xstar - x (k + 1) = -e := by rw [he]; abel
    rw [e1, inner_neg_right, norm_neg, real_inner_comm] at this
    rw [hμ2]
    linarith
  have I3 : 0 ≤ f (x (k + 1)) - f xstar := by linarith [hxstar (x (k + 1))]
  have K := key e u g (Real.sqrt μ) (Real.sqrt s) β _ _ hm hh hβ0 hβm I1 I2 I3
  have hvk : vK f μ β s x xstar k = Real.sqrt μ • e + (1 + Real.sqrt μ * Real.sqrt s) • u
      + (β + Real.sqrt s) • g := by
    simp only [vK]
    exact hv
  have hvk1 : vK f μ β s x xstar (k + 1) = Real.sqrt μ • e + (1 : ℝ) • u + β • g := by
    simp only [vK, Nat.add_sub_cancel, one_smul]
    rfl
  simp only [EK]
  rw [hvk, hvk1, hmh]
  rw [hs2] at K
  linarith

open HessianDamping.IPAHDSC in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC1 : ContDiff ℝ 1 f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : HessianDamping.DINSC.IsStronglyConvex f μ)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (β s : ℝ) (hs : 0 < s) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (2 * Real.sqrt μ))
    (hsβ : Real.sqrt s ≤ β)
    (x : ℕ → H) (hrun : IsIPAHDSCRun f μ β s x) :
    (0 < qRate μ s ∧ qRate μ s < 1 ∧ 0 < thetaRate μ s ∧ thetaRate μ s < 1) ∧
    (∀ k : ℕ, 1 ≤ k →
      μ / 2 * ‖x k - xstar‖ ^ 2 ≤ f (x k) - f xstar ∧
        f (x k) - f xstar ≤ E1 f μ β s x xstar * qRate μ s ^ (k - 1)) ∧
    (fun k : ℕ => thetaRate μ s ^ k *
        ∑ j ∈ Finset.range (k - 1), thetaRate μ s ^ (-(j : ℤ)) * ‖gradient f (x j)‖ ^ 2)
      =O[Filter.atTop] (fun k : ℕ => qRate μ s ^ k) := by
  have hfd : Differentiable ℝ f := hfC1.differentiable (by norm_num)
  have ha : 0 < Real.sqrt (μ * s) := Real.sqrt_pos.2 (mul_pos hμ hs)
  set a := Real.sqrt (μ * s) with ha_def
  have hq0 : 0 < qRate μ s := by unfold qRate; positivity
  have hq1 : qRate μ s < 1 := by
    unfold qRate; rw [div_lt_one (by positivity)]; linarith
  have hθ0 : 0 < thetaRate μ s := by unfold thetaRate; positivity
  have hθ1 : thetaRate μ s < 1 := by
    unfold thetaRate; rw [div_lt_one (by positivity)]; linarith
  have hθq : thetaRate μ s < qRate μ s := by
    unfold thetaRate qRate
    apply one_div_lt_one_div_of_lt (by positivity)
    linarith
  set q := qRate μ s with hq_def
  set θ := thetaRate μ s with hθ_def
  have hqa : q * (1 + 1 / 2 * a) = 1 := by
    rw [hq_def]; unfold qRate; rw [← ha_def]; field_simp
  have hstep := fun k (hk : 1 ≤ k) =>
    IPAHDSCAux_step f hfd μ hμ hsc xstar hxstar β s hs hβ0 hβ x hrun k hk
  have hEF : ∀ k, f (x k) - f xstar ≤ EK f μ β s x xstar k := by
    intro k; simp only [EK]
    have := sq_nonneg ‖vK f μ β s x xstar k‖
    linarith
  have hEnn : ∀ k, 0 ≤ EK f μ β s x xstar k := fun k =>
    le_trans (by linarith [hxstar (x k)]) (hEF k)
  have hrec : ∀ k, 1 ≤ k → EK f μ β s x xstar (k + 1) ≤ q * EK f μ β s x xstar k := by
    intro k hk
    have h1 := hstep k hk
    have h2 : 0 ≤ s / 4 * ‖gradient f (x (k + 1))‖ ^ 2 := by positivity
    have h3 : (1 + 1 / 2 * a) * EK f μ β s x xstar (k + 1) ≤ EK f μ β s x xstar k := by linarith
    calc EK f μ β s x xstar (k + 1) = q * ((1 + 1 / 2 * a) * EK f μ β s x xstar (k + 1)) := by
          rw [← mul_assoc, hqa, one_mul]
      _ ≤ q * EK f μ β s x xstar k := mul_le_mul_of_nonneg_left h3 hq0.le
  have hE1 : E1 f μ β s x xstar = EK f μ β s x xstar 1 := rfl
  have hpow : ∀ n : ℕ, EK f μ β s x xstar (n + 1) ≤ E1 f μ β s x xstar * q ^ n := by
    intro n
    induction n with
    | zero => rw [hE1]; simp
    | succ n ih =>
      calc EK f μ β s x xstar (n + 1 + 1) ≤ q * EK f μ β s x xstar (n + 1) := hrec (n + 1) (by omega)
        _ ≤ q * (E1 f μ β s x xstar * q ^ n) := mul_le_mul_of_nonneg_left ih hq0.le
        _ = E1 f μ β s x xstar * q ^ (n + 1) := by ring
  have hE1nn : 0 ≤ E1 f μ β s x xstar := by rw [hE1]; exact hEnn 1
  -- gradient at the minimizer vanishes
  have hgx : gradient f xstar = 0 := by
    have hlm : IsLocalMin f xstar := Filter.Eventually.of_forall hxstar
    have := hlm.fderiv_eq_zero
    simp [gradient, this]
  refine ⟨⟨hq0, hq1, hθ0, hθ1⟩, ?_, ?_⟩
  · intro k hk
    constructor
    · have := IPAHDSCAux.sc_first_order f hfd μ hsc xstar (x k)
      rw [hgx, inner_zero_left] at this
      linarith
    · have hk' : k = (k - 1) + 1 := by omega
      calc f (x k) - f xstar ≤ EK f μ β s x xstar k := hEF k
        _ = EK f μ β s x xstar ((k - 1) + 1) := by rw [← hk']
        _ ≤ E1 f μ β s x xstar * q ^ (k - 1) := hpow (k - 1)
  · -- gradient bound ‖∇f(x_j)‖² ≤ K q^j
    set K := 4 / s * E1 f μ β s x xstar / q ^ 2 + ‖gradient f (x 0)‖ ^ 2
      + ‖gradient f (x 1)‖ ^ 2 / q with hK
    have hKnn1 : 0 ≤ 4 / s * E1 f μ β s x xstar / q ^ 2 := by positivity
    have hKnn2 : 0 ≤ ‖gradient f (x 0)‖ ^ 2 := by positivity
    have hKnn3 : 0 ≤ ‖gradient f (x 1)‖ ^ 2 / q := by positivity
    have hKnn : 0 ≤ K := by linarith
    have hgrad : ∀ j : ℕ, ‖gradient f (x j)‖ ^ 2 ≤ K * q ^ j := by
      intro j
      match j with
      | 0 => simp only [pow_zero, mul_one]; linarith
      | 1 =>
        have : ‖gradient f (x 1)‖ ^ 2 = ‖gradient f (x 1)‖ ^ 2 / q * q := by
          field_simp
        rw [pow_one, this]
        apply mul_le_mul_of_nonneg_right _ hq0.le
        linarith
      | n + 2 =>
        have h1 := hstep (n + 1) (by omega)
        have h2 := hpow n
        have h3 : 0 ≤ (1 + 1 / 2 * a) * EK f μ β s x xstar (n + 1 + 1) := by
          have := hEnn (n + 1 + 1); positivity
        have h4 : s / 4 * ‖gradient f (x (n + 1 + 1))‖ ^ 2 ≤ E1 f μ β s x xstar * q ^ n := by
          linarith
        have h5 : ‖gradient f (x (n + 1 + 1))‖ ^ 2 ≤ 4 / s * E1 f μ β s x xstar / q ^ 2 * q ^ (n + 2) := by
          have e : 4 / s * E1 f μ β s x xstar / q ^ 2 * q ^ (n + 2)
              = 4 / s * (E1 f μ β s x xstar * q ^ n) := by
            field_simp; ring
          have e2 : ‖gradient f (x (n + 1 + 1))‖ ^ 2
              = 4 / s * (s / 4 * ‖gradient f (x (n + 1 + 1))‖ ^ 2) := by
            field_simp
          rw [e, e2]
          exact mul_le_mul_of_nonneg_left h4 (by positivity)
        have h6 : 4 / s * E1 f μ β s x xstar / q ^ 2 * q ^ (n + 2) ≤ K * q ^ (n + 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        exact le_trans h5 h6
    have hr1 : 1 < q / θ := (one_lt_div hθ0).2 hθq
    set r := q / θ with hr_def
    have hθr : θ * r = q := by rw [hr_def]; field_simp
    have hterm : ∀ j : ℕ, θ ^ (-(j : ℤ)) * ‖gradient f (x j)‖ ^ 2 ≤ K * r ^ j := by
      intro j
      have hz : θ ^ (-(j : ℤ)) = (θ ^ j)⁻¹ := by rw [zpow_neg, zpow_natCast]
      rw [hz]
      calc (θ ^ j)⁻¹ * ‖gradient f (x j)‖ ^ 2 ≤ (θ ^ j)⁻¹ * (K * q ^ j) :=
            mul_le_mul_of_nonneg_left (hgrad j) (by positivity)
        _ = K * r ^ j := by
            rw [← hθr, mul_pow]
            field_simp
    have hS : ∀ k : ℕ, 0 ≤ θ ^ k *
        ∑ j ∈ Finset.range (k - 1), θ ^ (-(j : ℤ)) * ‖gradient f (x j)‖ ^ 2 ∧
        θ ^ k * ∑ j ∈ Finset.range (k - 1), θ ^ (-(j : ℤ)) * ‖gradient f (x j)‖ ^ 2
          ≤ K / (r - 1) * q ^ k := by
      intro k
      constructor
      · apply mul_nonneg (by positivity)
        apply Finset.sum_nonneg
        intro j _
        exact mul_nonneg (zpow_nonneg hθ0.le _) (sq_nonneg _)
      · have s1 : ∑ j ∈ Finset.range (k - 1), θ ^ (-(j : ℤ)) * ‖gradient f (x j)‖ ^ 2
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
        calc θ ^ k * ∑ j ∈ Finset.range (k - 1), θ ^ (-(j : ℤ)) * ‖gradient f (x j)‖ ^ 2
            ≤ θ ^ k * (K * ((r ^ k - 1) / (r - 1))) :=
              mul_le_mul_of_nonneg_left (by linarith) hθk
          _ = K / (r - 1) * (θ ^ k * r ^ k - θ ^ k) := s4
          _ ≤ K / (r - 1) * q ^ k := by
              rw [s5]; exact mul_le_mul_of_nonneg_left (by linarith) hKr
    refine Asymptotics.IsBigO.of_bound (K / (r - 1)) (Filter.Eventually.of_forall fun k => ?_)
    rw [Real.norm_of_nonneg (hS k).1, Real.norm_of_nonneg (by positivity)]
    exact (hS k).2
