-- Prove2me | solution 1 for HessianDamping.IPAHD.EK_succ_sub_add_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:49:51.191173+00:00
-- url     : https://prove2.me/submissions/a533a8c0-8674-4c9f-b2cf-1a4dc4672301

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

theorem grad_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfd : Differentiable ℝ f) (x y : H) :
    f x + inner ℝ (gradient f x) (y - x) ≤ f y := by
  set φ : ℝ → ℝ := fun t => f (x + t • (y - x)) with hφ
  have hconv : ConvexOn ℝ Set.univ φ := by
    refine ⟨convex_univ, fun a _ b _ p q hp hq hpq => ?_⟩
    have hq' : q = 1 - p := by linarith
    subst hq'
    have e : x + (p * a + (1 - p) * b) • (y - x) =
        p • (x + a • (y - x)) + (1 - p) • (x + b • (y - x)) := by module
    have := hfconv.2 (Set.mem_univ (x + a • (y - x))) (Set.mem_univ (x + b • (y - x))) hp hq hpq
    simp only [hφ, smul_eq_mul]
    rw [e]
    exact this
  have hg : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const (y - x)).const_add x
    simpa using this
  have hgrad : HasGradientAt f (gradient f x) x := (hfd x).hasGradientAt
  have hl : HasFDerivAt f (InnerProductSpace.toDual ℝ H (gradient f x)) (x + (0:ℝ) • (y - x)) := by
    simpa using hgrad.hasFDerivAt
  have hd : HasDerivAt φ (inner ℝ (gradient f x) (y - x)) 0 := by
    have := hl.comp_hasDerivAt (0:ℝ) hg
    have e : InnerProductSpace.toDual ℝ H (gradient f x) (y - x) = inner ℝ (gradient f x) (y - x) := by
      simp
    rw [e] at this
    exact this
  have := hconv.le_slope_of_hasDerivAt (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ)) zero_lt_one hd
  rw [slope_def_field, sub_zero, div_one] at this
  have e1 : φ 1 = f y := by simp [hφ]
  have e0 : φ 0 = f x := by simp [hφ]
  rw [e1, e0] at this
  linarith

theorem real_master (h P α κ β1 G A1 A2 f1 fk fs d1 : ℝ) (hh : 0 < h) (hP : 0 ≤ P) (hα : 1 ≤ α)
    (hκ : 0 ≤ κ) (hβ : 0 ≤ β1) (hG : 0 ≤ G) (hA1 : f1 - fs ≤ A1) (hA2 : f1 - fk ≤ A2) :
    (d1 * (f1 - fs) - h * P * (κ + 1) * (fk - fs) +
      (h * (-P) * ((α - 1) * A1 + (κ + 1) * A2 + (κ + 1) * (β1 * h) * G) - 1 / 2 * (h * (-P)) ^ 2 * G)) +
      h * (h / 2 * (-P) ^ 2 + h * P * (κ + 1) * β1) * G ≤
    (d1 - h * P * (κ + 1) - (α - 1) * (h * P * (κ + 1)) / (κ + 1)) * (f1 - fs) := by
  have hκ1 : κ + 1 ≠ 0 := by positivity
  have e : (α - 1) * (h * P * (κ + 1)) / (κ + 1) = (α - 1) * (h * P) := by field_simp
  rw [e]
  have m1 : 0 ≤ h * P * (α - 1) * (A1 - (f1 - fs)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hh.le hP) (by linarith)) (by linarith)
  have m2 : 0 ≤ h * P * (κ + 1) * (A2 - (f1 - fk)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hh.le hP) (by linarith)) (by linarith)
  nlinarith [m1, m2]

theorem eq8_aux
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

theorem vK_aux
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (xstar : H) (α h : ℝ) (β b : ℕ → ℝ) (x : ℕ → H)
    (k : ℕ) (hk : 1 ≤ k)
    (h8 : (k : ℝ) • (x (k + 1) - (2 : ℝ) • x k + x (k - 1)) + α • (x (k + 1) - x k)
      + (β k * h * k) • (gradient f (x (k + 1)) - gradient f (x k))
      + (b k * h ^ 2 * k) • gradient f (x (k + 1)) = 0) :
    vK f α h β x xstar (k + 1) - vK f α h β x xstar k
      = (h * (β (k + 1) + k * (β (k + 1) - β k) - b k * h * k)) • gradient f (x (k + 1)) := by
  unfold vK
  simp only [Nat.add_sub_cancel]
  push_cast
  refine sub_eq_zero.mp (Eq.trans ?_ h8)
  module


theorem master
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC1 : ContDiff ℝ 1 f)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (α : ℝ) (hα : 1 ≤ α)
    (h s : ℝ) (hh : 0 < h) (hs : s = h ^ 2)
    (β b : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (hb : ∀ k, 0 ≤ b k)
    (x : ℕ → H) (hx : IsIPAHDRun f α s β b x)
    (k : ℕ) (hk : 1 ≤ k)
    (hG2 : 0 < b k * h * k - β (k + 1) - k * (β (k + 1) - β k)) :
    EK f α h β b x xstar (k + 1) - EK f α h β b x xstar k
      + h * (h / 2 * CK h β b k ^ 2 + deltaK h β b k * β (k + 1))
        * ‖gradient f (x (k + 1))‖ ^ 2 ≤
      (deltaK h β b (k + 1) - deltaK h β b k - (α - 1) * deltaK h β b k / ((k : ℝ) + 1))
        * (f (x (k + 1)) - f xstar) := by
  have hfd : Differentiable ℝ f := hfC1.differentiable (by norm_num)
  have h8 := eq8_aux f hfconv hfC1 α hα h s hh hs β b hβ hb x hx k hk
  have hv := vK_aux f xstar α h β b x k hk h8
  set P : ℝ := b k * h * k - β (k + 1) - k * (β (k + 1) - β k) with hPdef
  have hP : 0 ≤ P := hG2.le
  have hCK : CK h β b k = -P := by unfold CK; rw [hPdef]; ring
  have hdk : deltaK h β b k = h * P * ((k : ℝ) + 1) := by unfold deltaK; rw [hPdef]
  set g := gradient f (x (k + 1)) with hg
  have hv2 : vK f α h β x xstar (k + 1) - vK f α h β x xstar k = (h * (-P)) • g := by
    have e : h * (β (k + 1) + (k : ℝ) * (β (k + 1) - β k) - b k * h * k) = h * (-P) := by
      rw [hPdef]; ring
    rw [hv, e]
  have hv' : vK f α h β x xstar k = vK f α h β x xstar (k + 1) - (h * (-P)) • g := by
    rw [← hv2]; abel
  have hnorm : 1 / 2 * ‖vK f α h β x xstar (k + 1)‖ ^ 2 - 1 / 2 * ‖vK f α h β x xstar k‖ ^ 2 =
      inner ℝ ((h * (-P)) • g) (vK f α h β x xstar (k + 1)) - 1 / 2 * ‖(h * (-P)) • g‖ ^ 2 := by
    rw [hv', norm_sub_sq_real, real_inner_comm]
    ring
  have hv1 : vK f α h β x xstar (k + 1) =
      (α - 1) • (x (k + 1) - xstar) +
        ((k : ℝ) + 1) • (x (k + 1) - x k + (β (k + 1) * h) • g) := by
    unfold vK; simp only [Nat.add_sub_cancel]; push_cast; rfl
  have hin : inner ℝ ((h * (-P)) • g) (vK f α h β x xstar (k + 1)) =
      h * (-P) * ((α - 1) * inner ℝ g (x (k + 1) - xstar) +
        ((k : ℝ) + 1) * inner ℝ g (x (k + 1) - x k) +
        ((k : ℝ) + 1) * (β (k + 1) * h) * ‖g‖ ^ 2) := by
    rw [hv1, real_inner_smul_left, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hsq : ‖(h * (-P)) • g‖ ^ 2 = (h * (-P)) ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hA1 : f (x (k + 1)) - f xstar ≤ inner ℝ g (x (k + 1) - xstar) := by
    have := grad_ineq f hfconv hfd (x (k + 1)) xstar
    have e : inner ℝ g (xstar - x (k + 1)) = - inner ℝ g (x (k + 1) - xstar) := by
      rw [← inner_neg_right, neg_sub]
    rw [e] at this
    linarith
  have hA2 : f (x (k + 1)) - f (x k) ≤ inner ℝ g (x (k + 1) - x k) := by
    have := grad_ineq f hfconv hfd (x (k + 1)) (x k)
    have e : inner ℝ g (x k - x (k + 1)) = - inner ℝ g (x (k + 1) - x k) := by
      rw [← inner_neg_right, neg_sub]
    rw [e] at this
    linarith
  have hrm := real_master h P α (k : ℝ) (β (k + 1)) (‖g‖ ^ 2) (inner ℝ g (x (k + 1) - xstar))
    (inner ℝ g (x (k + 1) - x k)) (f (x (k + 1))) (f (x k)) (f xstar)
    (deltaK h β b (k + 1)) hh hP hα (by positivity) (hβ _) (by positivity) hA1 hA2
  have hEK : EK f α h β b x xstar (k + 1) - EK f α h β b x xstar k =
      deltaK h β b (k + 1) * (f (x (k + 1)) - f xstar) - deltaK h β b k * (f (x k) - f xstar) +
        (1 / 2 * ‖vK f α h β x xstar (k + 1)‖ ^ 2 - 1 / 2 * ‖vK f α h β x xstar k‖ ^ 2) := by
    unfold EK; ring
  rw [hEK, hnorm, hin, hsq, hCK, hdk]
  linarith [hrm]

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC1 : ContDiff ℝ 1 f)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (α : ℝ) (hα : 1 ≤ α)
    (h s : ℝ) (hh : 0 < h) (hs : s = h ^ 2)
    (β b : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (hb : ∀ k, 0 ≤ b k)
    (x : ℕ → H) (hx : IsIPAHDRun f α s β b x)
    (k : ℕ) (hk : 1 ≤ k)
    (hG2 : 0 < b k * h * k - β (k + 1) - k * (β (k + 1) - β k))
    (hG3 : deltaK h β b (k + 1) - deltaK h β b k ≤ (α - 1) * deltaK h β b k / ((k : ℝ) + 1)) :
    EK f α h β b x xstar (k + 1) - EK f α h β b x xstar k
      + h * (h / 2 * CK h β b k ^ 2 + deltaK h β b k * β (k + 1))
        * ‖gradient f (x (k + 1))‖ ^ 2 ≤ 0 := by
  have hm := master f hfconv hfC1 xstar hxstar α hα h s hh hs β b hβ hb x hx k hk hG2
  have hf : 0 ≤ f (x (k + 1)) - f xstar := sub_nonneg.mpr (hxstar _)
  have hK : (deltaK h β b (k + 1) - deltaK h β b k - (α - 1) * deltaK h β b k / ((k : ℝ) + 1))
      * (f (x (k + 1)) - f xstar) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hf
  linarith
