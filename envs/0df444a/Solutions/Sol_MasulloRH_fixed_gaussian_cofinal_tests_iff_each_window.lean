-- Prove2me | solution 1 for MasulloRH.fixed_gaussian_cofinal_tests_iff_each_window
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T19:25:15.34847+00:00
-- url     : https://prove2.me/submissions/194126e5-11cb-413e-b2b7-b463185bf72d

import Definitions.Def_MasulloRH_FixedGaussianTest
import Theorems.Thm_MasulloRH_finite_theta_approximation_excludes_rectangle_zeros
import Theorems.Thm_MasulloRH_unit_gaussian_uniform_initial_energy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MasulloRH.FixedGaussianTest MasulloRH.GaussianApproximation MeasureTheory

private theorem ordered_left {j k : ℕ} (h : j≤k) : left k≤left j := by
  unfold left
  apply add_le_add_right
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact_mod_cast Nat.succ_le_succ h

private theorem wtIntegrable {m : ℕ} (a : Fin m → ℂ) (y : Fin m → ℝ) (k : ℕ) :
    Integrable (fun x : ℝ => Real.exp (2*fullCenter k*x+2*fullWidth k*|x|)*‖residual 0 a y x‖^2) := by
  apply (MasulloRH.finite_theta_approximation_excludes_rectangle_zeros.1
    m 0 (fullCenter k) (fullWidth k) 1 a y (by norm_num) (by norm_num) ?_ ?_).1
  · have e : fullCenter k-fullWidth k=left k := by unfold fullCenter fullWidth;ring
    rw [e]
    unfold left
    positivity
  · have e : fullCenter k+fullWidth k=upper k := by unfold fullCenter fullWidth;ring
    rw [e]
    exact max_lt (by norm_num [right]) (sub_lt_self _ (by positivity))

private theorem nested {m : ℕ} (a : Fin m → ℂ) (y : Fin m → ℝ) {j k : ℕ} (h : j≤k) :
    energy (fullCenter j) (fullWidth j) (residual 0 a y) ≤ energy (fullCenter k) (fullWidth k) (residual 0 a y) := by
  apply integral_mono (wtIntegrable a y j) (wtIntegrable a y k)
  intro x
  apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (sq_nonneg _)
  rcases le_total 0 x with hx|hx
  · rw [abs_of_nonneg hx]
    have cmp : upper j≤upper k := by
      apply max_le_max_left
      apply sub_le_sub_left
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.succ_le_succ h
    have at_x (i : ℕ) : 2*fullCenter i*x+2*fullWidth i*x=2*(upper i*x) := by
      unfold fullCenter fullWidth
      ring
    rw [at_x,at_x]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right cmp hx) (by norm_num)
  · rw [abs_of_nonpos hx]
    have at_x (i : ℕ) : 2*fullCenter i*x+2*fullWidth i*(-x)=2*(left i*x) := by
      unfold fullCenter fullWidth
      ring
    rw [at_x,at_x]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonpos_right (ordered_left h) hx) (by norm_num)

/-- A sequence of successful certificates may progress arbitrarily slowly
in its strip index, provided its weighted errors approach zero. -/
theorem solution : (∀ k : ℕ, FullApprox k) ↔
    ∀ j : ℕ, 0<j → ∃ k : ℕ, j+1≤k ∧ ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      energy (fullCenter k) (fullWidth k) (residual 0
        (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I) (fun i => (y i:ℝ))) < 1/((j:ℝ)+1) := by
  constructor
  · intro h j _
    exact ⟨j+1,le_rfl,h (j+1) _ (by positivity)⟩
  · intro h k ε hε
    obtain ⟨n,hn⟩ := exists_nat_gt (1/ε)
    let j := max k n
    have tests (i : ℕ) : ∃ K : ℕ, i+1≤K ∧ ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
        energy (fullCenter K) (fullWidth K) (residual 0
          (fun t => ((a t).1:ℂ)+((a t).2:ℂ)*Complex.I) (fun t => (y t:ℝ))) < 1/((i:ℝ)+1) := by
      cases i with
      | succ i => exact h (i+1) (Nat.succ_pos _)
      | zero =>
        refine ⟨1,le_rfl,0,Fin.elim0,Fin.elim0,?_⟩
        have ub := MasulloRH.unit_gaussian_uniform_initial_energy (fullCenter 1) (fullWidth 1)
          (by norm_num [fullCenter,fullWidth,left,upper,right]) (by norm_num [fullCenter,fullWidth,left,upper,right])
        have empty (a : Fin 0 → ℂ) (y : Fin 0 → ℝ) : residual 0 a y=pulse 0 := by
          funext x
          simp [MasulloRH.GaussianApproximation.residual]
        rw [empty]
        norm_num
        linarith
    obtain ⟨K,hK,m,a,y,he⟩ := tests j
    have hk : k≤K := (le_max_left k n).trans ((Nat.le_succ j).trans hK)
    have hn' : (n:ℝ)≤(j:ℝ) := by exact_mod_cast le_max_right k n
    have hbound : 1/((j:ℝ)+1)<ε := by
      apply (div_lt_iff₀ (by positivity)).2
      have hr := (div_lt_iff₀ hε).1 hn
      nlinarith [mul_nonneg (sub_nonneg.mpr hn') hε.le]
    exact ⟨m,a,y,(nested _ _ hk).trans_lt (he.trans hbound)⟩
