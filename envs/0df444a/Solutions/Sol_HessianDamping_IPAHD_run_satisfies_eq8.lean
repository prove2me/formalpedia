-- Prove2me | solution 1 for HessianDamping.IPAHD.run_satisfies_eq8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:44:12.505168+00:00
-- url     : https://prove2.me/submissions/eee27309-c282-4905-8fb2-bcca3cdb6e5e

import Mathlib
import Definitions.Def_GoldenRatioVI_Shared_IsProxPoint
import Definitions.Def_HessianDamping_IPAHD_Setting
set_option autoImplicit false
open GoldenRatioVI.Shared HessianDamping.IPAHD

theorem prox_opt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hf : Differentiable ℝ f) (γ : ℝ) (z xbar : H)
    (h : IsProxPoint (fun z => ((γ * f z : ℝ) : EReal)) z xbar) :
    γ • gradient f xbar + (xbar - z) = 0 := by
  have hmin : IsLocalMin (fun x => γ * f x + 1 / 2 * ‖x - z‖ ^ 2) xbar := by
    apply Filter.Eventually.of_forall
    intro x
    have := h x
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    show γ * f xbar + 1 / 2 * ‖xbar - z‖ ^ 2 ≤ γ * f x + 1 / 2 * ‖x - z‖ ^ 2
    linarith
  have hg : HasGradientAt f (gradient f xbar) xbar := (hf xbar).hasGradientAt
  have h1 : HasFDerivAt f (InnerProductSpace.toDual ℝ H (gradient f xbar)) xbar := hg.hasFDerivAt
  have h2 := ((hasFDerivAt_id xbar).sub_const z).norm_sq
  have h3 := (h1.const_mul γ).add (h2.const_mul (1 / 2 : ℝ))
  have h4 := hmin.hasFDerivAt_eq_zero h3
  set w := γ • gradient f xbar + (xbar - z) with hw
  have h5 := congrArg (fun L => L w) h4
  simp at h5
  have h6 : fderiv ℝ f xbar w = inner ℝ (gradient f xbar) w := by
    rw [h1.fderiv]; simp [InnerProductSpace.toDual_apply_apply]
  have h7 : inner ℝ w w = γ * inner ℝ (gradient f xbar) w + (inner ℝ xbar w - inner ℝ z w) := by
    conv_lhs => rw [hw]
    rw [inner_add_left, real_inner_smul_left, inner_sub_left]
  have : inner ℝ w w = 0 := by
    rw [h7, ← h6]; exact h5
  exact inner_self_eq_zero.mp this

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC1 : ContDiff ℝ 1 f)
    (α : ℝ) (hα : 1 ≤ α)
    (h s : ℝ) (hh : 0 < h) (hs : s = h ^ 2)
    (β b : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (hb : ∀ k, 0 ≤ b k)
    (x : ℕ → H) (hx : IsIPAHDRun f α s β b x)
    (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) • (x (k + 1) - (2 : ℝ) • x k + x (k - 1)) + α • (x (k + 1) - x k)
      + (β k * h * k) • (gradient f (x (k + 1)) - gradient f (x k))
      + (b k * h ^ 2 * k) • gradient f (x (k + 1)) = 0 := by
  have hP := prox_opt f (hfC1.differentiable (by norm_num)) _ _ _ (hx k hk)
  unfold muK yK at hP
  subst hs
  rw [Real.sqrt_sq hh.le] at hP
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : (k : ℝ) + α ≠ 0 := by positivity
  have key : (k : ℝ) • (x (k + 1) - (2 : ℝ) • x k + x (k - 1)) + α • (x (k + 1) - x k)
      + (β k * h * k) • (gradient f (x (k + 1)) - gradient f (x k))
      + (b k * h ^ 2 * k) • gradient f (x (k + 1)) =
      ((k : ℝ) + α) •
        (((k : ℝ) / ((k : ℝ) + α) * (β k * h + h ^ 2 * b k)) • gradient f (x (k + 1)) +
          (x (k + 1) - (x k + (1 - α / ((k : ℝ) + α)) • (x k - x (k - 1)) +
            (β k * h * (1 - α / ((k : ℝ) + α))) • gradient f (x k)))) := by
    match_scalars <;> field_simp <;> ring
  rw [key, hP, smul_zero]
