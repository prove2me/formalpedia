-- Prove2me | solution 1 for LanglandsTunnell.exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/fc45d490-6b7c-537e-9d20-6e66edcae91e

import Mathlib
import Theorems.Thm_LanglandsTunnell_linearDependent_of_whittaker_ode_of_moderateGrowth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth

set_option autoImplicit false

open Polynomial

namespace RS11HW

noncomputable def a (n m : ℕ) (c : ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => -(c * ((m : ℝ) - j) / (((j : ℝ) + 1) * ((j : ℝ) + n + 1))) * a n m c j

theorem a_zero (n m : ℕ) (c : ℝ) : a n m c 0 = 1 := rfl

theorem a_succ (n m : ℕ) (c : ℝ) (j : ℕ) :
    a n m c (j + 1) = -(c * ((m : ℝ) - j) / (((j : ℝ) + 1) * ((j : ℝ) + n + 1))) * a n m c j := rfl

theorem a_rec (n m : ℕ) (c : ℝ) (j : ℕ) :
    ((j : ℝ) + 1) * ((j : ℝ) + n + 1) * a n m c (j + 1) + c * ((m : ℝ) - j) * a n m c j = 0 := by
  rw [a_succ]
  have h1 : ((j : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((j : ℝ) + n + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem a_eq_zero_of_lt (n m : ℕ) (c : ℝ) : ∀ j, m < j → a n m c j = 0 := by
  intro j hj
  induction j with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ j ih =>
    rw [a_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · rw [ih h, mul_zero]
    · rw [h, sub_self, mul_zero, zero_div, neg_zero, zero_mul]

noncomputable def p (n m : ℕ) (c : ℝ) : ℝ[X] := ∑ j ∈ Finset.range (m + 1), C (a n m c j) * X ^ j

theorem coeff_p (n m : ℕ) (c : ℝ) (i : ℕ) : (p n m c).coeff i = a n m c i := by
  unfold p
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    exact (a_eq_zero_of_lt n m c i (by omega)).symm

theorem p_ne_zero (n m : ℕ) (c : ℝ) : p n m c ≠ 0 := by
  intro h
  have := coeff_p n m c 0
  rw [h, coeff_zero, a_zero] at this
  exact zero_ne_one this

theorem laguerre (n m : ℕ) (c : ℝ) :
    X * derivative (derivative (p n m c)) + (C ((n : ℝ) + 1) - C c * X) * derivative (p n m c) +
      C (c * m) * p n m c = 0 := by
  ext i
  rw [coeff_zero, coeff_add, coeff_add, sub_mul, coeff_sub, coeff_C_mul, coeff_C_mul, mul_assoc, coeff_C_mul]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [mul_comm X, coeff_mul_X_zero, mul_comm X, coeff_mul_X_zero, coeff_derivative]
    simp only [coeff_p]
    have h := a_rec n m c 0
    push_cast at h ⊢
    linear_combination h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    rw [Nat.succ_eq_add_one, mul_comm X, coeff_mul_X, mul_comm X, coeff_mul_X, coeff_derivative, coeff_derivative,
      coeff_derivative]
    simp only [coeff_p]
    have h := a_rec n m c (j + 1)
    push_cast at h ⊢
    linear_combination h

section Calculus

variable (n m : ℕ)

noncomputable def s (n : ℕ) : ℝ := ((n : ℝ) + 1) / 2

theorem s_pos : 0 < s n := by unfold s; positivity

noncomputable def P : ℝ[X] := p n m (4 * Real.pi)

noncomputable def h (y : ℝ) : ℝ := (P n m).eval y * Real.exp (-(2 * Real.pi * y))
noncomputable def h1 (y : ℝ) : ℝ :=
  ((derivative (P n m)).eval y - 2 * Real.pi * (P n m).eval y) * Real.exp (-(2 * Real.pi * y))
noncomputable def h2 (y : ℝ) : ℝ :=
  ((derivative (derivative (P n m))).eval y - 4 * Real.pi * (derivative (P n m)).eval y +
    4 * Real.pi ^ 2 * (P n m).eval y) * Real.exp (-(2 * Real.pi * y))

private theorem _root_.RS11HW.hasDerivAt_exp (y : ℝ) :
    HasDerivAt (fun y => Real.exp (-(2 * Real.pi * y))) (-(2 * Real.pi) * Real.exp (-(2 * Real.pi * y))) y := by
  have h1 : HasDerivAt (fun y : ℝ => -(2 * Real.pi * y)) (-(2 * Real.pi)) y := by
    have h__af := ((hasDerivAt_id y).const_mul (2 * Real.pi)).neg
    simp at h__af
    exact h__af
  have := (Real.hasDerivAt_exp _).comp y h1
  simp [mul_comm] at this ⊢
  exact this

p2m_export "RS11HW" "hasDerivAt_exp"
theorem hasDerivAt_h (y : ℝ) : HasDerivAt (h n m) (h1 n m y) y := by
  have hp := (P n m).hasDerivAt y
  have he := hasDerivAt_exp y
  have := hp.mul he
  unfold h h1
  convert this using 1
  · rfl
  · rfl
  · rfl
  ring

theorem hasDerivAt_h1 (y : ℝ) : HasDerivAt (h1 n m) (h2 n m y) y := by
  have hp := (P n m).hasDerivAt y
  have hp' := (derivative (P n m)).hasDerivAt y
  have he := hasDerivAt_exp y
  have := (hp'.sub (hp.const_mul (2 * Real.pi))).mul he
  unfold h1 h2
  convert this using 1
  · rfl
  · rfl
  · rfl
  simp only [Pi.sub_apply]
  ring

noncomputable def g (y : ℝ) : ℝ := y ^ s n * h n m y
noncomputable def g1 (y : ℝ) : ℝ := s n * y ^ (s n - 1) * h n m y + y ^ s n * h1 n m y
noncomputable def g2 (y : ℝ) : ℝ :=
  s n * (s n - 1) * y ^ (s n - 1 - 1) * h n m y + 2 * s n * y ^ (s n - 1) * h1 n m y + y ^ s n * h2 n m y

theorem hasDerivAt_g {y : ℝ} (hy : 0 < y) : HasDerivAt (g n m) (g1 n m y) y := by
  have hr := Real.hasDerivAt_rpow_const (x := y) (p := s n) (Or.inl hy.ne')
  have := hr.mul (hasDerivAt_h n m y)
  unfold g g1
  convert this using 1
  rfl
  rfl
  rfl

theorem hasDerivAt_g1 {y : ℝ} (hy : 0 < y) : HasDerivAt (g1 n m) (g2 n m y) y := by
  have hr := Real.hasDerivAt_rpow_const (x := y) (p := s n) (Or.inl hy.ne')
  have hr' := Real.hasDerivAt_rpow_const (x := y) (p := s n - 1) (Or.inl hy.ne')
  have := ((hr'.const_mul (s n)).mul (hasDerivAt_h n m y)).add (hr.mul (hasDerivAt_h1 n m y))
  unfold g1 g2
  convert this using 1; rfl; rfl; rfl; ring

theorem deriv_g_eqOn : Set.EqOn (deriv (g n m)) (g1 n m) (Set.Ioi 0) := fun _ hy => (hasDerivAt_g n m hy).deriv

noncomputable def F (y : ℝ) : ℂ := ((g n m y : ℝ) : ℂ)

theorem hasDerivAt_F {y : ℝ} (hy : 0 < y) : HasDerivAt (F n m) ((g1 n m y : ℝ) : ℂ) y :=
  (hasDerivAt_g n m hy).ofReal_comp

theorem deriv_F_eventuallyEq {y : ℝ} (hy : 0 < y) :
    deriv (F n m) =ᶠ[nhds y] fun y => ((g1 n m y : ℝ) : ℂ) := by
  filter_upwards [Ioi_mem_nhds hy] with z hz
  exact (hasDerivAt_F n m hz).deriv

theorem hasDerivAt_deriv_F {y : ℝ} (hy : 0 < y) : HasDerivAt (deriv (F n m)) ((g2 n m y : ℝ) : ℂ) y := by
  have h := (hasDerivAt_g1 n m hy).ofReal_comp
  exact h.congr_of_eventuallyEq (deriv_F_eventuallyEq n m hy)

theorem differentiableOn_F : DifferentiableOn ℝ (F n m) (Set.Ioi 0) := fun _ hy =>
  (hasDerivAt_F n m hy).differentiableAt.differentiableWithinAt

theorem differentiableOn_deriv_F : DifferentiableOn ℝ (deriv (F n m)) (Set.Ioi 0) := fun _ hy =>
  (hasDerivAt_deriv_F n m hy).differentiableAt.differentiableWithinAt

theorem laguerre_eval (y : ℝ) :
    y * (derivative (derivative (P n m))).eval y + (((n : ℝ) + 1) - 4 * Real.pi * y) * (derivative (P n m)).eval y +
      4 * Real.pi * m * (P n m).eval y = 0 := by
  have h := congrArg (fun q => q.eval y) (laguerre n m (4 * Real.pi))
  simp only [eval_add, eval_mul, eval_X, eval_sub, eval_C, eval_zero] at h
  unfold P
  linear_combination h

theorem ode_F (k : ℝ) (ν : ℂ) (hk : k = n + 1 + 2 * m) (hν : ν = (n : ℂ) / 2) {y : ℝ} (hy : 0 < y) :
    (y : ℂ) ^ 2 * deriv (deriv (F n m)) y
        + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * F n m y = 0 := by
  rw [(hasDerivAt_deriv_F n m hy).deriv, F, hν, hk]

  have hreal : ((y : ℂ) ^ 2 * ((g2 n m y : ℝ) : ℂ)
        + (1 / 4 - ((n : ℂ) / 2) ^ 2 + 2 * (Real.pi : ℂ) * (((n + 1 + 2 * m : ℝ)) : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) *
          ((g n m y : ℝ) : ℂ)) =
      (((y ^ 2 * g2 n m y + (1 / 4 - ((n : ℝ) / 2) ^ 2 + 2 * Real.pi * (n + 1 + 2 * m) * y - 4 * Real.pi ^ 2 * y ^ 2) * g n m y : ℝ)) : ℂ) := by
    push_cast; ring
  rw [hreal, Complex.ofReal_eq_zero]

  have hY1 : y * y ^ (s n - 1) = y ^ s n := by
    rw [Real.rpow_sub_one hy.ne', mul_div_cancel₀ _ hy.ne']
  have hY2 : y ^ 2 * y ^ (s n - 1 - 1) = y ^ s n := by
    rw [Real.rpow_sub_one hy.ne', Real.rpow_sub_one hy.ne']
    field_simp
  have hL := laguerre_eval n m y
  unfold g2 g h h1 h2
  have hs : s n = ((n : ℝ) + 1) / 2 := rfl

  have key : y ^ 2 * (s n * (s n - 1) * y ^ (s n - 1 - 1)) = s n * (s n - 1) * y ^ s n := by
    rw [← hY2]; ring
  have key2 : y ^ 2 * (2 * s n * y ^ (s n - 1)) = 2 * s n * y * y ^ s n := by
    rw [← hY1]; ring
  set Y := y ^ s n with hYdef
  set E := Real.exp (-(2 * Real.pi * y)) with hE
  set P0 := (P n m).eval y
  set P1 := (derivative (P n m)).eval y
  set P2 := (derivative (derivative (P n m))).eval y
  have expand : y ^ 2 * (s n * (s n - 1) * y ^ (s n - 1 - 1) * (P0 * E) + 2 * s n * y ^ (s n - 1) * ((P1 - 2 * Real.pi * P0) * E) +
        Y * ((P2 - 4 * Real.pi * P1 + 4 * Real.pi ^ 2 * P0) * E)) =
      Y * E * (s n * (s n - 1) * P0 + 2 * s n * y * (P1 - 2 * Real.pi * P0) + y ^ 2 * (P2 - 4 * Real.pi * P1 + 4 * Real.pi ^ 2 * P0)) := by
    have e1 : y ^ 2 * (s n * (s n - 1) * y ^ (s n - 1 - 1) * (P0 * E)) = s n * (s n - 1) * Y * (P0 * E) := by
      rw [hYdef, ← key]; ring
    have e2 : y ^ 2 * (2 * s n * y ^ (s n - 1) * ((P1 - 2 * Real.pi * P0) * E)) = 2 * s n * y * Y * ((P1 - 2 * Real.pi * P0) * E) := by
      rw [hYdef, ← key2]; ring
    calc _ = y ^ 2 * (s n * (s n - 1) * y ^ (s n - 1 - 1) * (P0 * E)) + y ^ 2 * (2 * s n * y ^ (s n - 1) * ((P1 - 2 * Real.pi * P0) * E)) +
          y ^ 2 * (Y * ((P2 - 4 * Real.pi * P1 + 4 * Real.pi ^ 2 * P0) * E)) := by ring
      _ = _ := by rw [e1, e2]; ring
  rw [expand, hs]
  linear_combination (y * Y * E) * hL

end Calculus

section Size

variable (n m : ℕ)

noncomputable def A : ℝ := ∑ i ∈ Finset.range ((P n m).natDegree + 1), |(P n m).coeff i|

theorem A_nonneg : 0 ≤ A n m := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_eval_le_of_le_one {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1) : |(P n m).eval y| ≤ A n m := by
  rw [eval_eq_sum_range, A]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_pow, abs_of_nonneg hy0]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hy0 hy)

theorem abs_eval_le_of_one_le {y : ℝ} (hy : 1 ≤ y) : |(P n m).eval y| ≤ A n m * y ^ (P n m).natDegree := by
  rw [eval_eq_sum_range, A, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_pow, abs_of_nonneg (show (0 : ℝ) ≤ y by linarith)]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact pow_le_pow_right₀ hy (by rw [Finset.mem_range] at hi; omega)

theorem norm_F (y : ℝ) (hy : 0 < y) : ‖F n m y‖ = y ^ s n * |(P n m).eval y| * Real.exp (-(2 * Real.pi * y)) := by
  unfold F g h
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hy _),
    abs_of_pos (Real.exp_pos _)]
  ring

theorem exp_le_one {y : ℝ} (hy : 0 ≤ y) : Real.exp (-(2 * Real.pi * y)) ≤ 1 := by
  rw [Real.exp_le_one_iff, neg_nonpos]; positivity

theorem norm_F_le_near_zero {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) : ‖F n m y‖ ≤ A n m * y ^ s n := by
  rw [norm_F n m y hy]
  have h1 := abs_eval_le_of_le_one n m hy.le hy1
  have h2 := exp_le_one (y := y) hy.le
  have hY : 0 ≤ y ^ s n := (Real.rpow_pos_of_pos hy _).le
  calc y ^ s n * |(P n m).eval y| * Real.exp (-(2 * Real.pi * y)) ≤ y ^ s n * A n m * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hY) h2 (Real.exp_pos _).le
        exact mul_nonneg hY (A_nonneg n m)
    _ = A n m * y ^ s n := by ring

theorem norm_F_le_at_infinity {y : ℝ} (hy : 1 ≤ y) : ‖F n m y‖ ≤ A n m * y ^ (s n + (P n m).natDegree) := by
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
  rw [norm_F n m y hy0, Real.rpow_add hy0, Real.rpow_natCast]
  have h1 := abs_eval_le_of_one_le n m hy
  have h2 := exp_le_one (y := y) hy0.le
  have hY : 0 ≤ y ^ s n := (Real.rpow_pos_of_pos hy0 _).le
  calc y ^ s n * |(P n m).eval y| * Real.exp (-(2 * Real.pi * y)) ≤ y ^ s n * (A n m * y ^ (P n m).natDegree) * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hY) h2 (Real.exp_pos _).le
        exact mul_nonneg hY (mul_nonneg (A_nonneg n m) (pow_nonneg hy0.le _))
    _ = A n m * (y ^ s n * y ^ (P n m).natDegree) := by ring

theorem exists_F_ne_zero : ∃ y : ℝ, 0 < y ∧ F n m y ≠ 0 := by
  classical
  obtain ⟨y, hy, hroot⟩ := (Set.Ioo_infinite (zero_lt_one' ℝ)).exists_notMem_finset (P n m).roots.toFinset
  refine ⟨y, hy.1, ?_⟩
  have hP : (P n m).eval y ≠ 0 := by
    intro h0
    apply hroot
    rw [Multiset.mem_toFinset, mem_roots (show P n m ≠ 0 from p_ne_zero n m _)]
    exact h0
  unfold F g h
  rw [Ne, Complex.ofReal_eq_zero]
  exact mul_ne_zero (Real.rpow_pos_of_pos hy.1 _).ne' (mul_ne_zero hP (Real.exp_pos _).ne')

end Size

end RS11HW

theorem solution
    (n m : ℕ) (k : ℝ) (ν : ℂ) (hk : k = n + 1 + 2 * m) (hν : ν = (n : ℂ) / 2) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (hfgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ δ := by

  have hFd := RS11HW.differentiableOn_F n m
  have hFd' := RS11HW.differentiableOn_deriv_F n m
  have hFeq : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv (RS11HW.F n m)) y
      + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * RS11HW.F n m y = 0 :=
    fun y hy => RS11HW.ode_F n m k ν hk hν hy
  have hFgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖RS11HW.F n m y‖ ≤ C * y ^ N :=
    ⟨RS11HW.A n m, RS11HW.s n + (RS11HW.P n m).natDegree, fun y hy => RS11HW.norm_F_le_at_infinity n m hy⟩

  have hν2 : (ν ^ 2).im = 0 := by
    rw [hν, show ((n : ℂ) / 2) = (((n : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_pow, Complex.ofReal_im]
  obtain ⟨c₁, c₂, hc, hrel⟩ :=
    LanglandsTunnell.linearDependent_of_whittaker_ode_of_moderateGrowth ν hν2 k f (RS11HW.F n m)
      hf hf' hfeq hfgr hFd hFd' hFeq hFgr

  obtain ⟨y₀, hy₀, hFy₀⟩ := RS11HW.exists_F_ne_zero n m
  have hc₁ : c₁ ≠ 0 := by
    intro h1
    have h2 : c₂ ≠ 0 := by
      intro h2; exact hc (by rw [h1, h2]; rfl)
    have := hrel y₀ hy₀
    rw [h1, zero_mul, zero_add] at this
    exact hFy₀ ((mul_eq_zero.mp this).resolve_left h2)
  refine ⟨RS11HW.s n, RS11HW.s_pos n, ‖c₂ / c₁‖ * RS11HW.A n m, fun y hy hy1 => ?_⟩
  have hfy : f y = -(c₂ / c₁) * RS11HW.F n m y := by
    have := hrel y hy
    field_simp
    linear_combination this
  rw [hfy, norm_mul, norm_neg, mul_assoc]
  exact mul_le_mul_of_nonneg_left (RS11HW.norm_F_le_near_zero n m hy hy1) (norm_nonneg _)

end S_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth
end P2MW
export P2MW.S_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth (solution)
