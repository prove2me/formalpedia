-- Prove2me | solution 1 for MasulloRH.coherent_lower_bound_damped_euler_cutoff_second_jet
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T12:24:45.603907+00:00
-- url     : https://prove2.me/submissions/3bace6cd-61b0-4be0-9cba-44f7445b5c79

import Mathlib
open MeasureTheory Finset
theorem solution (N : ℕ) (hN : 0 < N) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hrN : 1/2 ≤ r^(2*N)) :
    (N:ℝ)^5/64 ≤ ∫ x in (0:ℝ)..(1/(4*(N:ℝ))),
      (∑ j ∈ Finset.range (2*N), (j:ℝ)^2 * r^j * Real.cos ((j:ℝ)*x))^2 := by
  let F := fun x : ℝ => ∑ j ∈ Finset.range (2*N), (j:ℝ)^2*r^j*Real.cos ((j:ℝ)*x)
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hu : (0:ℝ) ≤ 1/(4*(N:ℝ)) := by positivity
  have bound (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) (1/(4*(N:ℝ)))) :
      (N:ℝ)^3/4 ≤ F x := by
    have hx' := (le_div_iff₀ (by positivity : 0 < 4*(N:ℝ))).mp hx.2
    have cs (j : ℕ) (hj : j < 2*N) : 1/2 ≤ Real.cos ((j:ℝ)*x) := by
      have hj' : (j:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hj.le
      rw [← Real.cos_pi_div_three]
      apply Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg (Nat.cast_nonneg _) hx.1) (by linarith [Real.pi_pos])
      nlinarith [mul_le_mul_of_nonneg_right hj' hx.1, Real.pi_gt_three]
    have jr (j : ℕ) (hj : j < 2*N) : 1/2 ≤ r^j :=
      hrN.trans (pow_le_pow_of_le_one hr hr1 hj.le)
    have first : 0 ≤ ∑ j ∈ Finset.range N, (j:ℝ)^2*r^j*Real.cos ((j:ℝ)*x) := by
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (by positivity) (by have := cs j (by have := Finset.mem_range.mp hj; omega); linarith)
    have second (j : ℕ) (hj : j ∈ Finset.range N) :
        (N:ℝ)^2/4 ≤ ((N+j:ℕ):ℝ)^2 * r^(N+j)*Real.cos (((N+j:ℕ):ℝ)*x) := by
      have hlt : N+j < 2*N := by have := Finset.mem_range.mp hj; omega
      have hsq : (N:ℝ)^2 ≤ ((N+j:ℕ):ℝ)^2 := by push_cast; nlinarith [sq_nonneg (j:ℝ),mul_nonneg hn.le (Nat.cast_nonneg j)]
      have hh := mul_le_mul hsq (jr _ hlt) (by norm_num : (0:ℝ) ≤ 1/2) (by positivity)
      have hhh := mul_le_mul hh (cs _ hlt) (by norm_num : (0:ℝ) ≤ 1/2) (by positivity)
      linarith
    have hs := Finset.sum_le_sum second
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
    dsimp only [F]
    rw [two_mul, Finset.sum_range_add]
    linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) hu
    (f := fun _ : ℝ => ((N:ℝ)^3/4)^2) (g := fun x : ℝ => (F x)^2)
    (continuous_const.intervalIntegrable _ _) ((hF.pow 2).intervalIntegrable _ _) (fun x hx =>
      pow_le_pow_left₀ (by positivity) (bound x hx) 2)
  rw [intervalIntegral.integral_const] at hi
  change _ ≤ ∫ x in (0:ℝ)..(1/(4*(N:ℝ))), (F x)^2
  apply le_trans (le_of_eq ?_) hi
  simp only [sub_zero, smul_eq_mul]
  field_simp [ne_of_gt hn]
  <;> ring
