-- Prove2me | solution 1 for HessianDamping.IPAHDSC.vK_succ_sub
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:39:43.438325+00:00
-- url     : https://prove2.me/submissions/6f58f55b-396b-45a1-b4c8-a1121d7e6e88

import Mathlib
import Definitions.Def_GoldenRatioVI_Shared_IsProxPoint
import Definitions.Def_HessianDamping_IPAHDSC_Setting
set_option autoImplicit false
open GoldenRatioVI.Shared HessianDamping.IPAHDSC

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

theorem eq20_aux {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfC1 : ContDiff ℝ 1 f)
    (μ : ℝ) (hμ : 0 < μ) (β s : ℝ) (hs : 0 < s)
    (x : ℕ → H) (hrun : IsIPAHDSCRun f μ β s x) (k : ℕ) (hk : 1 ≤ k) :
    (1 / Real.sqrt s) • (x (k + 1) - (2 : ℝ) • x k + x (k - 1)) +
        (2 * Real.sqrt μ) • (x (k + 1) - x k) +
        β • (gradient f (x (k + 1)) - gradient f (x k)) +
        Real.sqrt s • gradient f (x (k + 1)) = 0 := by
  have hP := prox_opt f (hfC1.differentiable (by norm_num)) _ _ _ (hrun k hk)
  unfold gammaStep yK at hP
  have hrs : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hrm : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  rw [Real.sqrt_mul hμ.le] at hP
  have hθ : 1 + 2 * (Real.sqrt μ * Real.sqrt s) ≠ 0 := by positivity
  have hss : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have key : (1 / Real.sqrt s) • (x (k + 1) - (2 : ℝ) • x k + x (k - 1)) +
        (2 * Real.sqrt μ) • (x (k + 1) - x k) +
        β • (gradient f (x (k + 1)) - gradient f (x k)) +
        Real.sqrt s • gradient f (x (k + 1)) =
      ((1 + 2 * (Real.sqrt μ * Real.sqrt s)) / Real.sqrt s) •
        (((β * Real.sqrt s + s) / (1 + 2 * (Real.sqrt μ * Real.sqrt s))) • gradient f (x (k + 1)) +
          (x (k + 1) - (x k +
            (1 - 2 * (Real.sqrt μ * Real.sqrt s) / (1 + 2 * (Real.sqrt μ * Real.sqrt s))) •
              (x k - x (k - 1)) +
            (β * Real.sqrt s * (1 - 2 * (Real.sqrt μ * Real.sqrt s) /
                (1 + 2 * (Real.sqrt μ * Real.sqrt s)))) • gradient f (x k)))) := by
    match_scalars <;> field_simp <;> nlinarith [hss]
  rw [key, hP, smul_zero]

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC1 : ContDiff ℝ 1 f)
    (μ : ℝ) (hμ : 0 < μ) (β s : ℝ) (hs : 0 < s) (hβ0 : 0 ≤ β)
    (xstar : H) (x : ℕ → H) (hrun : IsIPAHDSCRun f μ β s x) (k : ℕ) (hk : 1 ≤ k) :
    vK f μ β s x xstar (k + 1) - vK f μ β s x xstar k =
      -(Real.sqrt μ • (x (k + 1) - x k)) - Real.sqrt s • gradient f (x (k + 1)) := by
  have h20 := eq20_aux f hfC1 μ hμ β s hs x hrun k hk
  unfold vK
  simp only [Nat.add_sub_cancel]
  refine sub_eq_zero.mp (Eq.trans ?_ h20)
  module
