-- Prove2me | solution 1 for OAI.Cotype.not_uniformL1_of_kConvex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:27:36.545667+00:00
-- url     : https://prove2.me/submissions/a98612ae-7103-41c5-8c88-a663a47badd3

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
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality

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
theorem h50d_avg_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    average (fun _ : α => c) = c := by
  have : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [average, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
  field_simp

theorem h50d_ES_lower (n : ℕ) :
    Real.sqrt n ≤ 4 * average (fun ε : Cube n => |∑ i, sign (ε i)|) := by
  have h := h50d_khin (X := ℝ) (fun _ : Fin n => (1 : ℝ))
  have e1 : (fun u : Cube n => ‖rademacherSum ℝ (fun _ : Fin n => (1 : ℝ)) u‖) =
      fun ε => |∑ i, sign (ε i)| := by
    funext ε; simp [rademacherSum, Real.norm_eq_abs]
  have e2 : cubeL2 ℝ (rademacherSum ℝ (fun _ : Fin n => (1 : ℝ))) = Real.sqrt n := by
    unfold cubeL2
    congr 1
    have : (fun ε : Cube n => ‖rademacherSum ℝ (fun _ : Fin n => (1 : ℝ)) ε‖ ^ 2) =
        fun ε => ∑ i, ∑ j, sign (ε i) * sign (ε j) := by
      funext ε
      simp only [rademacherSum, smul_eq_mul, mul_one, Real.norm_eq_abs, sq]
      rw [abs_mul_abs_self, Finset.sum_mul_sum]
    rw [this, average_sum]
    simp only [average_sum, coordinate_orthogonality]
    simp
  rw [e1, e2] at h
  exact h

theorem h50d_translate {n : ℕ} (δ : Cube n) :
    ∑ ε : Cube n, |∑ i, sign (δ i) * sign (ε i)| = ∑ ε : Cube n, |∑ i, sign (ε i)| := by
  rw [← (signCubeTwist δ).sum_comp (fun ε => |∑ i, sign (ε i)|)]
  refine Finset.sum_congr rfl fun ε _ => ?_
  simp [signCubeTwist]

theorem h50d_kconv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (h : KConvex X) : ¬ UniformL1 X := by
  rintro ⟨c, hc, hU⟩
  obtain ⟨K, hK0, hK⟩ := h
  have bound : ∀ n : ℕ, c * average (fun ε : Cube n => |∑ i, sign (ε i)|) ≤ K := by
    intro n
    obtain ⟨x, hx⟩ := hU (Fintype.card (Cube n))
    let y : Cube n → X := fun ε => x (Fintype.equivFin (Cube n) ε)
    have hy1 : ∀ ε, ‖y ε‖ ≤ 1 := fun ε => hx.1 _
    have hy2 : ∀ a : Cube n → ℝ, c * ∑ ε, |a ε| ≤ ‖∑ ε, a ε • y ε‖ := by
      intro a
      have := hx.2 (fun k => a ((Fintype.equivFin (Cube n)).symm k))
      rw [← (Fintype.equivFin (Cube n)).sum_comp, ← (Fintype.equivFin (Cube n)).sum_comp] at this
      simpa only [Equiv.symm_apply_apply] using this
    have hf : cubeL2 X y ≤ 1 := by
      unfold cubeL2
      rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      apply Real.sqrt_le_sqrt
      calc average (fun ε => ‖y ε‖ ^ 2) ≤ average (fun _ : Cube n => (1:ℝ)) :=
            average_mono fun ε => by
              have := hy1 ε; have := norm_nonneg (y ε); nlinarith
        _ = 1 := h50d_avg_const 1
    set N : ℝ := (Fintype.card (Cube n) : ℝ)
    have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
    have hrad : ∀ δ, radProjection X y δ =
        ∑ ε, (N⁻¹ * ∑ i, sign (δ i) * sign (ε i)) • y ε := by
      intro δ
      simp only [radProjection, rademacherSum, moment, average, Finset.smul_sum, smul_smul,
        Finset.sum_mul, Finset.sum_smul, N]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ε _ => ?_
      rw [← Finset.sum_smul]; congr 1; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hlow : ∀ δ, c * average (fun ε : Cube n => |∑ i, sign (ε i)|) ≤
        ‖radProjection X y δ‖ := by
      intro δ
      rw [hrad]
      refine le_trans (le_of_eq ?_) (hy2 _)
      simp only [abs_mul, abs_inv, abs_of_pos hN, ← Finset.mul_sum, h50d_translate, average,
        smul_eq_mul, N]
    have hL : c * average (fun ε : Cube n => |∑ i, sign (ε i)|) ≤ cubeL2 X (radProjection X y) :=
      calc _ = average (fun _ : Cube n => c * average (fun ε : Cube n => |∑ i, sign (ε i)|)) :=
            (h50d_avg_const _).symm
        _ ≤ average (fun δ => ‖radProjection X y δ‖) := average_mono hlow
        _ ≤ _ := average_norm_le_cubeL2 _
    calc _ ≤ cubeL2 X (radProjection X y) := hL
      _ ≤ K * cubeL2 X y := hK n y
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left hf hK0
      _ = K := mul_one K
  -- choose n large
  set M : ℝ := 4 * K / c + 1
  obtain ⟨n, hn⟩ := exists_nat_gt (M ^ 2)
  have hb := bound n
  have hE := h50d_ES_lower n
  have hM : 0 < M := by positivity
  have hsq : M < Real.sqrt n := by
    rw [show M = Real.sqrt (M ^ 2) from (Real.sqrt_sq hM.le).symm]
    exact Real.sqrt_lt_sqrt (by positivity) hn
  have : c * Real.sqrt n ≤ 4 * K := by nlinarith
  have : c * M ≤ 4 * K := by nlinarith
  have : c * M = 4 * K + c := by
    simp only [M]; field_simp
  linarith

theorem solution (h : KConvex X) : ¬ UniformL1 X := by
  exact h50d_kconv h

