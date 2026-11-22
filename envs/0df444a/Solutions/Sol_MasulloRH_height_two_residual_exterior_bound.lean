-- Prove2me | solution 1 for MasulloRH.height_two_residual_exterior_bound
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T19:34:41.505411+00:00
-- url     : https://prove2.me/submissions/8a873d16-0b9c-45e2-a490-59c61b4a91b4

import Definitions.Def_MasulloRH_HeightTwoWitness
import Theorems.Thm_MasulloRH_finite_theta_residual_tail_bound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 2000000

open MeasureTheory Set
open scoped BigOperators
open _root_.MasulloRH.GaussianApproximation

namespace N5HeightTwoTailProof

open _root_.MasulloRH.HeightTwoWitness

/-- The actual witness has bounded real translates. -/
theorem shifts_bounds (i : Fin 11) :
    -(3/8 : ℝ) ≤ shifts i ∧ shifts i ≤ (19/8 : ℝ) := by
  fin_cases i <;> norm_num [shifts, shiftsQ]

/-- The coefficient budget is evaluated exactly, including the signs. -/
theorem coefficient_norm_sum :
    (∑ i : Fin 11, ‖coeffs i‖) = (6297/100 : ℝ) := by
  norm_num [Fin.sum_univ_succ, coeffs, coeffsQ, Complex.norm_ratCast]

theorem shifts_in_window (i : Fin 11) :
    |shifts i - Real.log 2| ≤ (4 : ℝ) := by
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hi := shifts_bounds i
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem dyadic_exp_decay (n : ℕ) :
    Real.exp (-(n : ℝ)) ≤ 1/(2 : ℝ)^n := by
  have h : (2 : ℝ)^n ≤ Real.exp n := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le n
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) h

private theorem exp_power_lower (n : ℕ) (x : ℝ) (hx : (n : ℝ) ≤ 2*x) :
    (5/2 : ℝ)^n ≤ (Real.exp x)^2 := by
  have h : (5/2 : ℝ)^n ≤ Real.exp n := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num)
      (by linarith [Real.exp_one_gt_d9]) n
  calc
    _ ≤ Real.exp n := h
    _ ≤ Real.exp (2*x) := Real.exp_le_exp.mpr hx
    _ = _ := Real.exp_nat_mul x 2

private theorem right_exponent_bound (i : Fin 11) :
    -Real.pi*(Real.exp (4-shifts i))^2 ≤ (-40 : ℝ) := by
  have hi := (shifts_bounds i).2
  have hs := exp_power_lower 3 (4-shifts i) (by norm_num; linarith)
  have hp := mul_le_mul Real.pi_gt_three.le hs
    (by positivity : (0 : ℝ) ≤ (5/2 : ℝ)^3) Real.pi_pos.le
  norm_num at hp
  linarith

private theorem left_exponent_bound (i : Fin 11) :
    4+shifts i-(Real.pi/16)*(Real.exp (4+shifts i))^2 ≤ (-40 : ℝ) := by
  have hi := shifts_bounds i
  have hs := exp_power_lower 7 (4+shifts i) (by norm_num; linarith)
  have hp := mul_le_mul
    (div_le_div_of_nonneg_right Real.pi_gt_three.le (by norm_num : (0 : ℝ) ≤ 16))
    hs (by positivity : (0 : ℝ) ≤ (5/2 : ℝ)^7)
    (by positivity : (0 : ℝ) ≤ Real.pi/16)
  norm_num at hp
  linarith

private theorem pulse_endpoint_bound :
    (3/Real.sqrt Real.pi)*Real.exp (-144 : ℝ) ≤ (3/(2:ℝ)^40) := by
  have hc : 3/Real.sqrt Real.pi ≤ (3 : ℝ) :=
    div_le_self (by norm_num)
      (Real.one_le_sqrt.mpr (by linarith [Real.pi_gt_three]))
  have he : Real.exp (-144 : ℝ) ≤ 1/(2 : ℝ)^40 :=
    (Real.exp_le_exp.mpr (by norm_num : (-144 : ℝ) ≤ -40)).trans
      (dyadic_exp_decay 40)
  simpa only [mul_one_div] using
    mul_le_mul hc he (Real.exp_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)

/-- A common small rational bound for both endpoint envelope constants.
Only coarse integer exponential inequalities are needed here. -/
theorem endpoint_constants_bound :
    let A : ℝ := (3/Real.sqrt Real.pi)*Real.exp (-144)
    let C : ℝ := A + ∑ i : Fin 11, ‖coeffs i‖ *
      (24*Real.exp (-Real.pi*(Real.exp (4-shifts i))^2))
    let D : ℝ := A + ∑ i : Fin 11, ‖coeffs i‖ *
      (12*Real.exp (4+shifts i-(Real.pi/16)*(Real.exp (4+shifts i))^2))
    (0 ≤ C ∧ C ≤ (1/100000000 : ℝ)) ∧
      (0 ≤ D ∧ D ≤ (1/100000000 : ℝ)) := by
  intro A C D
  have hright (i : Fin 11) :
      24*Real.exp (-Real.pi*(Real.exp (4-shifts i))^2) ≤ 24/(2 : ℝ)^40 := by
    have he := (Real.exp_le_exp.mpr (right_exponent_bound i)).trans
      (dyadic_exp_decay 40)
    simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 24)
  have hleft (i : Fin 11) :
      12*Real.exp (4+shifts i-(Real.pi/16)*(Real.exp (4+shifts i))^2) ≤
        12/(2 : ℝ)^40 := by
    have he := (Real.exp_le_exp.mpr (left_exponent_bound i)).trans
      (dyadic_exp_decay 40)
    simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 12)
  have hC : C ≤ 3/(2 : ℝ)^40 + (6297/100 : ℝ)*(24/(2 : ℝ)^40) := by
    dsimp [C, A]
    apply add_le_add pulse_endpoint_bound
    calc
      _ ≤ ∑ i : Fin 11, ‖coeffs i‖ * (24/(2 : ℝ)^40) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hright i) (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, coefficient_norm_sum]
  have hD : D ≤ 3/(2 : ℝ)^40 + (6297/100 : ℝ)*(12/(2 : ℝ)^40) := by
    dsimp [D, A]
    apply add_le_add pulse_endpoint_bound
    calc
      _ ≤ ∑ i : Fin 11, ‖coeffs i‖ * (12/(2 : ℝ)^40) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hleft i) (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, coefficient_norm_sum]
  refine ⟨⟨by dsimp [C, A]; positivity, hC.trans ?_⟩,
    ⟨by dsimp [D, A]; positivity, hD.trans ?_⟩⟩ <;> norm_num

private theorem exterior_weight_bound : Real.exp (47/6 : ℝ) ≤ 6561 := by
  have hp := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le 8
  norm_num [Real.exp_one_pow] at hp
  exact (Real.exp_le_exp.mpr (by norm_num : (47/6 : ℝ) ≤ 8)).trans hp

private theorem endpoint_integral_bound (C D : ℝ)
    (hC : 0 ≤ C ∧ C ≤ (1/100000000 : ℝ))
    (hD : 0 ≤ D ∧ D ≤ (1/100000000 : ℝ)) :
    C^2*Real.exp (47/6 : ℝ)/(1/24) +
      D^2*Real.exp (-25/6 : ℝ)/(25/24) ≤ (1/10000000000 : ℝ) := by
  have hC2 := pow_le_pow_left₀ hC.1 hC.2 2
  have hD2 := pow_le_pow_left₀ hD.1 hD.2 2
  have hp : C^2*Real.exp (47/6 : ℝ)/(1/24) ≤
      (1/100000000 : ℝ)^2*6561/(1/24) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul hC2 exterior_weight_bound (Real.exp_nonneg _) (by positivity))
      (by norm_num)
  have hm : D^2*Real.exp (-25/6 : ℝ)/(25/24) ≤
      (1/100000000 : ℝ)^2/(25/24) := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    have he : Real.exp (-25/6 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    simpa only [mul_one] using
      mul_le_mul hD2 he (Real.exp_nonneg _) (by positivity : (0 : ℝ) ≤ (1/100000000)^2)
  exact (add_le_add hp hm).trans (by norm_num)

end N5HeightTwoTailProof

/-- The exact eleven-term height-two witness has integrable weighted square,
and its true exterior energy beyond `[-4,4]` is at most `10^(-10)`. -/
theorem solution :
    Integrable (fun x : ℝ =>
      Real.exp (2*(3/4)*x+2*(11/48)*|x|) *
        ‖_root_.MasulloRH.GaussianApproximation.residual 2 _root_.MasulloRH.HeightTwoWitness.coeffs _root_.MasulloRH.HeightTwoWitness.shifts x‖^2) ∧
    0 ≤ _root_.MasulloRH.GaussianApproximation.energy (3/4) (11/48) (_root_.MasulloRH.GaussianApproximation.residual 2 _root_.MasulloRH.HeightTwoWitness.coeffs _root_.MasulloRH.HeightTwoWitness.shifts) -
      (∫ x : ℝ in Icc (-4) 4,
        Real.exp (2*(3/4)*x+2*(11/48)*|x|) *
          ‖_root_.MasulloRH.GaussianApproximation.residual 2 _root_.MasulloRH.HeightTwoWitness.coeffs _root_.MasulloRH.HeightTwoWitness.shifts x‖^2) ∧
    _root_.MasulloRH.GaussianApproximation.energy (3/4) (11/48) (_root_.MasulloRH.GaussianApproximation.residual 2 _root_.MasulloRH.HeightTwoWitness.coeffs _root_.MasulloRH.HeightTwoWitness.shifts) -
      (∫ x : ℝ in Icc (-4) 4,
        Real.exp (2*(3/4)*x+2*(11/48)*|x|) *
          ‖_root_.MasulloRH.GaussianApproximation.residual 2 _root_.MasulloRH.HeightTwoWitness.coeffs _root_.MasulloRH.HeightTwoWitness.shifts x‖^2) ≤
      (1/10000000000 : ℝ) := by
  have h := _root_.MasulloRH.finite_theta_residual_tail_bound
    11 2 (3/4) (11/48) 4 _root_.MasulloRH.HeightTwoWitness.coeffs _root_.MasulloRH.HeightTwoWitness.shifts
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    _root_.N5HeightTwoTailProof.shifts_in_window
  have hnum := _root_.N5HeightTwoTailProof.endpoint_constants_bound
  dsimp only at h hnum
  refine ⟨h.1, h.2.1, h.2.2.trans ?_⟩
  norm_num only at hnum ⊢
  simpa only [neg_div] using
    _root_.N5HeightTwoTailProof.endpoint_integral_bound _ _ hnum.1 hnum.2

#print axioms solution
