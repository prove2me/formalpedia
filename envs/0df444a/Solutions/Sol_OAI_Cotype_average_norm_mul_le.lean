-- Prove2me | solution 1 for OAI.Cotype.average_norm_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:30:18.704993+00:00
-- url     : https://prove2.me/submissions/b4a7480d-cca3-49e2-9524-46b1fb40acb8

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality

open OAI OAI.Cotype
open scoped BigOperators
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
theorem t_avg {n : ℕ} (f : Cube n → X) (g : Cube n → Y) :
    average (fun u => ‖f u‖ * ‖g u‖) ≤ cubeL2 X f * cubeL2 Y g := by
  simp only [average, cubeL2, smul_eq_mul]
  have hN : (0 : ℝ) ≤ (Fintype.card (Cube n) : ℝ)⁻¹ := by positivity
  rw [Real.sqrt_mul hN, Real.sqrt_mul hN]
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun u => ‖f u‖) (fun u => ‖g u‖)
  calc (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ u, ‖f u‖ * ‖g u‖
      ≤ (Fintype.card (Cube n) : ℝ)⁻¹ * (√(∑ u, ‖f u‖ ^ 2) * √(∑ u, ‖g u‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h hN
    _ = _ := by
      rw [show √(Fintype.card (Cube n) : ℝ)⁻¹ * √(∑ u, ‖f u‖ ^ 2) * (√(Fintype.card (Cube n) : ℝ)⁻¹ *
        √(∑ u, ‖g u‖ ^ 2)) = (√(Fintype.card (Cube n) : ℝ)⁻¹ * √(Fintype.card (Cube n) : ℝ)⁻¹) *
        (√(∑ u, ‖f u‖ ^ 2) * √(∑ u, ‖g u‖ ^ 2)) by ring, Real.mul_self_sqrt hN]

theorem h50w_cubeL2_le_of_le {n : ℕ} (f : Cube n → Y) (c : ℝ) (hc : 0 ≤ c) (h : ∀ u, ‖f u‖ ≤ c) :
    cubeL2 Y f ≤ c := by
  unfold cubeL2
  rw [Real.sqrt_le_left hc]
  have hN : (Fintype.card (Cube n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [average, smul_eq_mul]
  calc (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ u, ‖f u‖ ^ 2 ≤ (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ _u : Cube n, c ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum fun u _ => pow_le_pow_left₀ (norm_nonneg _) (h u) 2
    _ = c ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

theorem h50w_cubeL2_map {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X) :
    cubeL2 Y (fun u => T (f u)) ≤ ‖T‖ * cubeL2 X f := by
  unfold cubeL2
  rw [← Real.sqrt_sq (norm_nonneg T), ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  simp only [average, smul_eq_mul]
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2

theorem h50w_opW_bound {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X) :
    cubeL2 Y (operatorWalsh T f) ≤ ‖T‖ * cubeL2 X f :=
  h50w_cubeL2_le_of_le _ _ (mul_nonneg (norm_nonneg _) (cubeL2_nonneg _)) fun v =>
    (vectorWalsh_bound (fun u => T (f u)) v).trans (h50w_cubeL2_map T f)

theorem h50w_opW_sub {n : ℕ} (A B : X →L[ℝ] Y) (f : Cube n → X) :
    operatorWalsh A f - operatorWalsh B f = operatorWalsh (A - B) f := by
  funext v
  simp only [operatorWalsh, vectorWalsh, average, Pi.sub_apply, ← smul_sub, ← Finset.sum_sub_distrib,
    ContinuousLinearMap.sub_apply]

omit [NormedSpace ℝ Y] in
theorem h50w_cubeL2_sub {n : ℕ} (f g : Cube n → Y) :
    |cubeL2 Y f - cubeL2 Y g| ≤ cubeL2 Y (f - g) := by
  have e : ∀ h : Cube n → Y, cubeL2 Y h = Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹) *
      ‖(WithLp.toLp 2 h : PiLp 2 (fun _ : Cube n => Y))‖ := fun h => by
    rw [PiLp.norm_eq_of_L2]
    simp only [cubeL2, average, smul_eq_mul]
    exact Real.sqrt_mul (by positivity) _
  rw [e, e, e, ← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have := abs_norm_sub_norm_le (WithLp.toLp 2 f : PiLp 2 (fun _ : Cube n => Y)) (WithLp.toLp 2 g)
  simpa [← WithLp.toLp_sub] using this

theorem t_opWL {n : ℕ} (A B : X →L[ℝ] Y) (f : Cube n → X) :
    |cubeL2 Y (operatorWalsh A f) - cubeL2 Y (operatorWalsh B f)| ≤ ‖A-B‖ * cubeL2 X f := by
  refine (h50w_cubeL2_sub _ _).trans ?_
  rw [h50w_opW_sub]
  exact h50w_opW_bound _ f

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
theorem solution {n : ℕ} (f : Cube n → X) (g : Cube n → Y) :
    average (fun u => ‖f u‖ * ‖g u‖) ≤ cubeL2 X f * cubeL2 Y g := by
  exact t_avg f g

