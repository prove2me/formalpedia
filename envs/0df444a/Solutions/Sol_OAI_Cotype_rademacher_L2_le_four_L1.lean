-- Prove2me | solution 1 for OAI.Cotype.rademacher_L2_le_four_L1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:25:37.483268+00:00
-- url     : https://prove2.me/submissions/23f3d365-ec09-43eb-bf98-4f895bb4e4d8

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
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
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
theorem h50d_tnoise {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}
    (f : Cube n → X) (u : Cube n) :
    ‖cubeNoise f u‖ ≤ cubeNoise (fun v => ‖f v‖) u := by
  induction n with
  | zero => simp [cubeNoise]
  | succ n ih =>
    rw [← Fin.cons_self_tail u]
    cases u 0
    · rw [cubeNoise_cons_false, cubeNoise_cons_false]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by norm_num),
        abs_of_pos (by norm_num)]
      have h1 := ih (fun v => f (Fin.cons false v)) (Fin.tail u)
      have h2 := ih (fun v => f (Fin.cons true v)) (Fin.tail u)
      simp only [smul_eq_mul]
      linarith
    · rw [cubeNoise_cons_true, cubeNoise_cons_true]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by norm_num),
        abs_of_pos (by norm_num)]
      have h1 := ih (fun v => f (Fin.cons false v)) (Fin.tail u)
      have h2 := ih (fun v => f (Fin.cons true v)) (Fin.tail u)
      simp only [smul_eq_mul]
      linarith

theorem h50d_noise_const {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}
    (y : X) (f : Cube n → X) (u : Cube n) :
    cubeNoise (fun v => y + f v) u = y + cubeNoise f u := by
  induction n with
  | zero => simp [cubeNoise]
  | succ n ih =>
    rw [← Fin.cons_self_tail u]
    cases u 0
    · rw [cubeNoise_cons_false, cubeNoise_cons_false]
      rw [ih (fun v => f (Fin.cons false v)), ih (fun v => f (Fin.cons true v))]
      module
    · rw [cubeNoise_cons_true, cubeNoise_cons_true]
      rw [ih (fun v => f (Fin.cons false v)), ih (fun v => f (Fin.cons true v))]
      module

theorem h50d_rad_cons {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}
    (x : Fin (n+1) → X) (b : Bool) (v : Cube n) :
    rademacherSum X x (Fin.cons b v) = sign b • x 0 + rademacherSum X (Fin.tail x) v := by
  simp only [rademacherSum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]

theorem h50d_noise_rad {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}
    (x : Fin n → X) (u : Cube n) :
    cubeNoise (rademacherSum X x) u = (1/2 : ℝ) • rademacherSum X x u := by
  induction n with
  | zero => simp [cubeNoise, rademacherSum]
  | succ n ih =>
    rw [← Fin.cons_self_tail u]
    have e : ∀ b, (fun v => rademacherSum X x (Fin.cons b v)) =
        fun v => sign b • x 0 + rademacherSum X (Fin.tail x) v := by
      intro b; funext v; exact h50d_rad_cons x b v
    cases u 0
    · rw [cubeNoise_cons_false, e, e, h50d_noise_const, h50d_noise_const, ih, h50d_rad_cons]
      simp only [sign_false, sign_true, one_smul, neg_smul]
      module
    · rw [cubeNoise_cons_true, e, e, h50d_noise_const, h50d_noise_const, ih, h50d_rad_cons]
      simp only [sign_false, sign_true, one_smul, neg_smul]
      module

theorem h50d_khin {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ} (x : Fin n → X) :
    cubeL2 X (rademacherSum X x) ≤ 4 * average (fun u => ‖rademacherSum X x u‖) := by
  set g : Cube n → ℝ := fun u => ‖rademacherSum X x u‖ with hg
  set Tg : Cube n → ℝ := cubeNoise g
  have hg0 : ∀ u, 0 ≤ g u := fun u => norm_nonneg _
  have hpt : ∀ u, g u ≤ 2 * Tg u := by
    intro u
    have h1 := h50d_tnoise (rademacherSum X x) u
    rw [h50d_noise_rad, norm_smul] at h1
    have : ‖(1/2 : ℝ)‖ = 1/2 := by norm_num
    rw [this] at h1
    show ‖rademacherSum X x u‖ ≤ 2 * cubeNoise g u
    linarith
  have hT0 : ∀ u, 0 ≤ Tg u := fun u => by linarith [hpt u, hg0 u]
  set a := average g
  set b := average (fun u => g u ^ 2)
  set c := average (fun u => g u * Tg u)
  set d := average (fun u => g u * Tg u ^ 2)
  have ha : 0 ≤ a := h50d_avg_nonneg _ hg0
  have hb : 0 ≤ b := h50d_avg_nonneg _ fun u => sq_nonneg _
  have hd : 0 ≤ d := h50d_avg_nonneg _ fun u => by have := hg0 u; have := hT0 u; positivity
  have h1 : b ≤ 2 * c := by
    rw [← h50d_avg_mul]
    exact average_mono fun u => by nlinarith [hpt u, hg0 u]
  have h2 : c ^ 2 ≤ a * d := by
    have := h50d_avg_cs (fun u => Real.sqrt (g u)) (fun u => Real.sqrt (g u) * Tg u)
    have e1 : (fun u => Real.sqrt (g u) * (Real.sqrt (g u) * Tg u)) = fun u => g u * Tg u := by
      funext u; rw [← mul_assoc, Real.mul_self_sqrt (hg0 u)]
    have e2 : (fun u => Real.sqrt (g u) ^ 2) = g := by
      funext u; rw [Real.sq_sqrt (hg0 u)]
    have e3 : (fun u => (Real.sqrt (g u) * Tg u) ^ 2) = fun u => g u * Tg u ^ 2 := by
      funext u; rw [mul_pow, Real.sq_sqrt (hg0 u)]
    rw [e1, e2, e3] at this
    exact this
  have h3 : d ^ 2 ≤ b * b ^ 2 := by
    have := h50d_avg_cs g (fun u => Tg u ^ 2)
    have e : (fun u => (Tg u ^ 2) ^ 2) = fun u => Tg u ^ 4 := by funext u; ring
    rw [e] at this
    have h4 : average (fun u => Tg u ^ 4) ≤ b ^ 2 := h50d_fourth g
    calc d ^ 2 ≤ _ := this
      _ ≤ b * b ^ 2 := mul_le_mul_of_nonneg_left h4 hb
  have key : b ≤ 16 * a ^ 2 := by
    rcases eq_or_lt_of_le hb with h0 | hpos
    · rw [← h0]; positivity
    · have hc0 : 0 ≤ c := by linarith
      have s1 : b ^ 2 ≤ 4 * (a * d) := by nlinarith
      have s2 : b ^ 4 ≤ 16 * a ^ 2 * b ^ 3 := by
        have : (b ^ 2) ^ 2 ≤ (4 * (a * d)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) s1 2
        nlinarith [sq_nonneg a]
      have hb3 : 0 < b ^ 3 := by positivity
      nlinarith
  show Real.sqrt b ≤ 4 * a
  rw [show 4 * a = Real.sqrt ((4 * a) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  exact Real.sqrt_le_sqrt (by nlinarith)

theorem solution {n : ℕ} (x : Fin n → X) :
    cubeL2 X (rademacherSum X x) ≤ 4 * average (fun u => ‖rademacherSum X x u‖) := by
  exact h50d_khin x

