-- Prove2me | solution 1 for OAI.Cotype.cubeNoise_fourth_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:23:30.346985+00:00
-- url     : https://prove2.me/submissions/6c1ba1fd-5c92-4688-8fba-97be771b7877

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
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity

open OAI OAI.Cotype
open scoped BigOperators
theorem h50d_avg_succ {n : ℕ} (F : Cube (n+1) → ℝ) :
    average F = (average (fun v : Cube n => F (Fin.cons false v)) +
      average (fun v : Cube n => F (Fin.cons true v))) / 2 := by
  have hs : ∑ u, F u = ∑ v : Cube n, F (Fin.cons false v) + ∑ v : Cube n, F (Fin.cons true v) := by
    rw [← (cubeCons n).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [cubeCons, Equiv.coe_fn_mk]
    ring
  have hc : (Fintype.card (Cube (n+1)) : ℝ) = 2 * Fintype.card (Cube n) := by
    simp only [Cube, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    push_cast; ring
  have hc0 : (Fintype.card (Cube n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [average, smul_eq_mul, hs, hc]
  field_simp

theorem h50d_noise_lin {n : ℕ} (a b : ℝ) (f g : Cube n → ℝ) (u : Cube n) :
    cubeNoise (fun v => a * f v + b * g v) u = a * cubeNoise f u + b * cubeNoise g u := by
  induction n with
  | zero => simp [cubeNoise]
  | succ n ih =>
    rw [← Fin.cons_self_tail u]
    cases u 0
    · simp only [cubeNoise_cons_false, smul_eq_mul]
      rw [ih (fun v => f (Fin.cons false v)) (fun v => g (Fin.cons false v)),
        ih (fun v => f (Fin.cons true v)) (fun v => g (Fin.cons true v))]
      ring
    · simp only [cubeNoise_cons_true, smul_eq_mul]
      rw [ih (fun v => f (Fin.cons false v)) (fun v => g (Fin.cons false v)),
        ih (fun v => f (Fin.cons true v)) (fun v => g (Fin.cons true v))]
      ring

theorem h50d_avg_add {α : Type*} [Fintype α] (F G : α → ℝ) :
    average (fun u => F u + G u) = average F + average G := by
  simp only [average, smul_eq_mul, Finset.sum_add_distrib, mul_add]

theorem h50d_avg_mul {α : Type*} [Fintype α] (c : ℝ) (F : α → ℝ) :
    average (fun u => c * F u) = c * average F := by
  simp only [average, smul_eq_mul, ← Finset.mul_sum]; ring

theorem h50d_avg_nonneg {α : Type*} [Fintype α] (F : α → ℝ) (h : ∀ u, 0 ≤ F u) :
    0 ≤ average F := by
  simp only [average, smul_eq_mul]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun u _ => h u)

theorem h50d_avg_cs {α : Type*} [Fintype α] (F G : α → ℝ) :
    average (fun u => F u * G u) ^ 2 ≤ average (fun u => F u ^ 2) * average (fun u => G u ^ 2) := by
  simp only [average, smul_eq_mul]
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ F G
  have hc : 0 ≤ ((Fintype.card α : ℝ)⁻¹) ^ 2 := by positivity
  calc ((Fintype.card α : ℝ)⁻¹ * ∑ u, F u * G u) ^ 2
      = ((Fintype.card α : ℝ)⁻¹) ^ 2 * (∑ u, F u * G u) ^ 2 := by ring
    _ ≤ ((Fintype.card α : ℝ)⁻¹) ^ 2 * ((∑ u, F u ^ 2) * ∑ u, G u ^ 2) :=
        mul_le_mul_of_nonneg_left this hc
    _ = _ := by ring

theorem h50d_fourth {n : ℕ} (f : Cube n → ℝ) :
    average (fun u => cubeNoise f u ^ 4) ≤ average (fun u => f u ^ 2) ^ 2 := by
  induction n with
  | zero =>
    have hu : ∀ u : Cube 0, u = fun i => i.elim0 := fun u => funext fun i => i.elim0
    simp only [average, smul_eq_mul, cubeNoise]
    rw [Fintype.sum_eq_single (fun i => i.elim0) (fun u hu' => absurd (hu u) hu'),
      Fintype.sum_eq_single (fun i => i.elim0) (fun u hu' => absurd (hu u) hu')]
    simp only [Cube, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, pow_zero,
      Nat.cast_one, inv_one, one_mul]
    nlinarith [sq_nonneg (f (fun i => i.elim0))]
  | succ n ih =>
    set g : Cube n → ℝ := fun v => f (Fin.cons false v)
    set h : Cube n → ℝ := fun v => f (Fin.cons true v)
    set α : Cube n → ℝ := fun v => (1/2) * g v + (1/2) * h v
    set β : Cube n → ℝ := fun v => (1/2) * g v + (-1/2) * h v
    have ha : ∀ v, cubeNoise α v = (1/2) * cubeNoise g v + (1/2) * cubeNoise h v :=
      fun v => h50d_noise_lin _ _ g h v
    have hb : ∀ v, cubeNoise β v = (1/2) * cubeNoise g v + (-1/2) * cubeNoise h v :=
      fun v => h50d_noise_lin _ _ g h v
    set A : Cube n → ℝ := fun v => cubeNoise α v
    set B : Cube n → ℝ := fun v => cubeNoise β v
    have e1 : average (fun u => cubeNoise f u ^ 4) = average (fun v =>
        (1/2) * ((3/4) * cubeNoise g v + (1/4) * cubeNoise h v) ^ 4 +
        (1/2) * ((1/4) * cubeNoise g v + (3/4) * cubeNoise h v) ^ 4) := by
      rw [h50d_avg_succ, h50d_avg_add, h50d_avg_mul, h50d_avg_mul]
      simp only [cubeNoise_cons_false, cubeNoise_cons_true, smul_eq_mul]
      ring
    have e2 : average (fun v =>
        (1/2) * ((3/4) * cubeNoise g v + (1/4) * cubeNoise h v) ^ 4 +
        (1/2) * ((1/4) * cubeNoise g v + (3/4) * cubeNoise h v) ^ 4) =
        average (fun v => A v ^ 4 + (3/2) * (A v ^ 2 * B v ^ 2) + (1/16) * B v ^ 4) := by
      congr 1; funext v; simp only [A, B, ha, hb]; ring
    have e3 : average (fun v => A v ^ 4 + (3/2) * (A v ^ 2 * B v ^ 2) + (1/16) * B v ^ 4) =
        average (fun v => A v ^ 4) + (3/2) * average (fun v => A v ^ 2 * B v ^ 2) +
        (1/16) * average (fun v => B v ^ 4) := by
      rw [h50d_avg_add, h50d_avg_add, h50d_avg_mul, h50d_avg_mul]
    have e4 : average (fun u => f u ^ 2) =
        average (fun v => α v ^ 2) + average (fun v => β v ^ 2) := by
      rw [h50d_avg_succ, ← h50d_avg_add]
      rw [div_eq_mul_inv, mul_comm, ← h50d_avg_mul, ← h50d_avg_add]
      congr 1; funext v; simp only [α, β, g, h]; ring
    set P := average (fun v => α v ^ 2)
    set Q := average (fun v => β v ^ 2)
    have hP : 0 ≤ P := h50d_avg_nonneg _ fun v => sq_nonneg _
    have hQ : 0 ≤ Q := h50d_avg_nonneg _ fun v => sq_nonneg _
    have iA : average (fun v => A v ^ 4) ≤ P ^ 2 := ih α
    have iB : average (fun v => B v ^ 4) ≤ Q ^ 2 := ih β
    have hC0 : 0 ≤ average (fun v => A v ^ 2 * B v ^ 2) :=
      h50d_avg_nonneg _ fun v => by positivity
    have hcs := h50d_avg_cs (fun v => A v ^ 2) (fun v => B v ^ 2)
    have h4 : ∀ (F : Cube n → ℝ), (fun u => (F u ^ 2) ^ 2) = fun u => F u ^ 4 := by
      intro F; funext u; ring
    simp only [h4] at hcs
    have hA0 : 0 ≤ average (fun v => A v ^ 4) := h50d_avg_nonneg _ fun v => by positivity
    have hB0 : 0 ≤ average (fun v => B v ^ 4) := h50d_avg_nonneg _ fun v => by positivity
    have hC : average (fun v => A v ^ 2 * B v ^ 2) ≤ P * Q := by
      have : average (fun v => A v ^ 2 * B v ^ 2) ^ 2 ≤ (P * Q) ^ 2 := by
        calc _ ≤ _ := hcs
          _ ≤ P ^ 2 * Q ^ 2 := mul_le_mul iA iB hB0 (sq_nonneg _)
          _ = (P * Q) ^ 2 := by ring
      exact (pow_le_pow_iff_left₀ hC0 (mul_nonneg hP hQ) (by norm_num)).mp this
    rw [e1, e2, e3, e4]
    nlinarith [mul_nonneg hP hQ, sq_nonneg Q]

theorem solution {n : ℕ} (f : Cube n → ℝ) :
    average (fun u => cubeNoise f u ^ 4) ≤ average (fun u => f u ^ 2) ^ 2 := by
  exact h50d_fourth f

