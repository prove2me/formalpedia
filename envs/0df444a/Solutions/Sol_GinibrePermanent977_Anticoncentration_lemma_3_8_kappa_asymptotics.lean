-- Prove2me | solution 1 for GinibrePermanent977.Anticoncentration.lemma_3_8_kappa_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:11:10.536462+00:00
-- url     : https://prove2.me/submissions/cd407e50-e9b1-4ba4-8a30-412df6454f25

import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory Matrix Filter Asymptotics
open scoped Topology Real Nat
set_option autoImplicit false
namespace GinibrePermanent977.Anticoncentration

private lemma gamma_half_sq_upper {x : ℝ} (hx : 0 < x) :
    Real.Gamma (x + 1 / 2) ^ 2 ≤ x * Real.Gamma x ^ 2 := by
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
    (s := x) (t := x+1) (a := 1/2) (b := 1/2) hx (by linarith)
    (by norm_num) (by norm_num) (by norm_num)
  have he : (1/2:ℝ) * x + 1/2 * (x+1) = x+1/2 := by ring
  rw [he, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  have h0 := Real.Gamma_pos_of_pos (show 0 < x+1/2 by linarith)
  have h1 := Real.Gamma_pos_of_pos hx
  have h2 := Real.Gamma_pos_of_pos (show 0 < x+1 by linarith)
  have hsq := sq_le_sq₀ h0.le (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) |>.mpr h
  rw [mul_pow, Real.sq_sqrt h1.le, Real.sq_sqrt h2.le,
    Real.Gamma_add_one hx.ne'] at hsq
  nlinarith

private lemma gamma_half_sq_lower {x : ℝ} (hx : 1/2 ≤ x) :
    (x/2) * Real.Gamma x ^ 2 ≤ Real.Gamma (x + 1/2) ^ 2 := by
  have h := gamma_half_sq_upper (show 0 < x+1/2 by linarith)
  have he : x+1/2+1/2 = x+1 := by ring
  rw [he, Real.Gamma_add_one (show x ≠ 0 by linarith)] at h
  have hg := sq_nonneg (Real.Gamma (x+1/2))
  have hG := sq_nonneg (Real.Gamma x)
  nlinarith [mul_nonneg (show 0 ≤ x-1/2 by linarith) hg]

private lemma kappa_pos (F : Scalar) {n : ℕ} (hn : 1 ≤ n) : 0 < kappa F n := by
  have hb := beta_pos F
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  unfold kappa
  apply div_pos
  · apply mul_pos
    · positivity
    · exact Real.Gamma_pos_of_pos (by positivity)
  · exact Real.Gamma_pos_of_pos (by positivity)

private lemma kappa_complex {n : ℕ} (hn : 1 ≤ n) : kappa .complex n = n / Real.pi := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hG : Real.Gamma (n : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by exact_mod_cast (show 0 < n by omega))).ne'
  have hg := Real.Gamma_add_one hn'
  rw [Real.Gamma_nat_eq_factorial] at hg
  simp only [kappa, Scalar.beta]
  norm_num
  rw [Real.rpow_neg_one, hg]
  field_simp

private lemma kappa_real_square {n : ℕ} (hn : 1 ≤ n) :
    kappa .real n ^ 2 * Real.Gamma ((n : ℝ)/2)^2 =
      (n ! : ℝ) * (2 : ℝ) ^ (-(n : ℝ)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hg := (Real.Gamma_pos_of_pos (show 0 < (n : ℝ)/2 by positivity)).ne'
  simp only [kappa, Scalar.beta, Nat.cast_one, one_mul, one_div, mul_pow, div_pow]
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 hg)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (n ! : ℝ))]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ Real.pi)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ)⁻¹)]
  norm_num [Real.Gamma_one_half_eq, Real.sq_sqrt Real.pi_pos.le]
  rw [Real.rpow_neg_one, _root_.one_div_pow]
  field_simp


private lemma kappa_real_identity {n : ℕ} (hn : 1 ≤ n) :
    kappa .real n ^ 2 * (2 * Real.sqrt Real.pi) * Real.Gamma ((n : ℝ)/2) =
      (n : ℝ) * Real.Gamma ((n : ℝ)/2+1/2) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hg := (Real.Gamma_pos_of_pos (show 0 < (n : ℝ)/2 by positivity)).ne'
  have hf : (n ! : ℝ) = (n : ℝ) * Real.Gamma (n : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial, Real.Gamma_add_one hn'.ne']
  have hd := Real.Gamma_mul_Gamma_add_half ((n : ℝ)/2)
  have hp : (2 : ℝ) ^ (1-(n : ℝ)) = 2 * (2 : ℝ) ^ (-(n : ℝ)) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    ring
  norm_num only [mul_div_cancel₀ _ (two_ne_zero : (2:ℝ) ≠ 0)] at hd
  rw [hp] at hd
  apply mul_right_cancel₀ hg
  calc
    kappa .real n ^ 2 * (2 * Real.sqrt Real.pi) * Real.Gamma ((n : ℝ)/2) *
        Real.Gamma ((n : ℝ)/2) =
        (kappa .real n ^ 2 * Real.Gamma ((n : ℝ)/2)^2) * (2 * Real.sqrt Real.pi) := by ring
    _ = ((n ! : ℝ) * (2 : ℝ) ^ (-(n : ℝ))) * (2 * Real.sqrt Real.pi) := by
      rw [kappa_real_square hn]
    _ = (n : ℝ) * (Real.Gamma (n : ℝ) * (2 * (2 : ℝ)^(-(n : ℝ))) * Real.sqrt Real.pi) := by
      rw [hf]; ring
    _ = (n : ℝ) * (Real.Gamma ((n : ℝ)/2) * Real.Gamma ((n : ℝ)/2+1/2)) := by rw [← hd]
    _ = (n : ℝ) * Real.Gamma ((n : ℝ)/2+1/2) * Real.Gamma ((n : ℝ)/2) := by ring

private lemma kappa_real_fourth_bounds {n : ℕ} (hn : 1 ≤ n) :
    kappa .real n ^ 4 * (8 * Real.pi) ≤ (n : ℝ)^3 ∧
      (n : ℝ)^3 ≤ (16 * Real.pi) * kappa .real n ^ 4 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hg := sq_pos_of_pos (Real.Gamma_pos_of_pos (show 0 < (n : ℝ)/2 by linarith))
  have hid := congrArg (fun r : ℝ => r^2) (kappa_real_identity hn)
  simp only [mul_pow, ← pow_mul, Real.sq_sqrt Real.pi_pos.le] at hid
  have hu := mul_le_mul_of_nonneg_left
    (gamma_half_sq_upper (show 0 < (n : ℝ)/2 by linarith)) (sq_nonneg (n : ℝ))
  have hl := mul_le_mul_of_nonneg_left
    (gamma_half_sq_lower (show 1/2 ≤ (n : ℝ)/2 by linarith)) (sq_nonneg (n : ℝ))
  have hu' : kappa .real n ^ 4 * (4 * Real.pi) ≤ (n : ℝ)^3/2 := by
    apply (_root_.mul_le_mul_iff_right₀ hg).mp
    nlinarith [hid]
  have hl' : (n : ℝ)^3/4 ≤ kappa .real n ^ 4 * (4 * Real.pi) := by
    apply (_root_.mul_le_mul_iff_right₀ hg).mp
    nlinarith [hid]
  constructor <;> nlinarith

private lemma kappa_quaternion_identity {n : ℕ} (hn : 1 ≤ n) :
    kappa .quaternion n * Real.pi^2 * Real.Gamma ((n : ℝ)+1/2) =
      2 * Real.sqrt Real.pi * (n : ℝ)^2 * Real.Gamma (n : ℝ) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hg2 := (Real.Gamma_pos_of_pos (show 0 < 2*(n : ℝ) by positivity)).ne'
  have hf : (n ! : ℝ) = (n : ℝ) * Real.Gamma (n : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial, Real.Gamma_add_one hn'.ne']
  have hd := Real.Gamma_mul_Gamma_add_half (n : ℝ)
  have hp : (2 : ℝ) ^ (1-2*(n : ℝ)) = 2 / (2 : ℝ) ^ (2*(n : ℝ)) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one]
  have hpow := (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (2*(n : ℝ))).ne'
  rw [hp] at hd
  have hdf : Real.Gamma (n : ℝ) * Real.Gamma ((n : ℝ)+1/2) * (2 : ℝ)^(2*(n : ℝ)) =
      Real.Gamma (2*(n : ℝ)) * 2 * Real.sqrt Real.pi := by
    field_simp at hd ⊢
    nlinarith [hd]
  unfold kappa
  norm_num only [Scalar.beta, Nat.cast_ofNat]
  norm_num
  rw [hf]
  have he : (4 : ℝ) * n / 2 = 2 * (n : ℝ) := by ring
  rw [he]
  field_simp
  convert hdf using 1 <;> ring_nf

private lemma kappa_quaternion_square_bounds {n : ℕ} (hn : 1 ≤ n) :
    kappa .quaternion n ^ 2 * Real.pi^3 ≤ 8 * (n : ℝ)^3 ∧
      4 * (n : ℝ)^3 ≤ Real.pi^3 * kappa .quaternion n ^ 2 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hg := sq_pos_of_pos (Real.Gamma_pos_of_pos (show 0 < (n : ℝ) by linarith))
  have hid := congrArg (fun r : ℝ => r^2) (kappa_quaternion_identity hn)
  simp only [mul_pow, ← pow_mul, Real.sq_sqrt Real.pi_pos.le] at hid
  have hu := gamma_half_sq_upper (show 0 < (n : ℝ) by linarith)
  have hl := gamma_half_sq_lower (show 1/2 ≤ (n : ℝ) by linarith)
  have hk : 0 ≤ kappa .quaternion n ^ 2 * Real.pi^4 := by positivity
  have hupper := mul_le_mul_of_nonneg_left hu hk
  have hlower := mul_le_mul_of_nonneg_left hl hk
  have hc := mul_pos (mul_pos (show 0 < (n : ℝ) by linarith) Real.pi_pos) hg
  constructor
  · apply (_root_.mul_le_mul_iff_right₀ hc).mp
    nlinarith [hid, hlower]
  · apply (_root_.mul_le_mul_iff_right₀ hc).mp
    nlinarith [hid, hupper]

private lemma theta_of_powers (f : ℕ → ℝ) (m k : ℕ) (hm : m ≠ 0)
    (hf : ∀ n, 1 ≤ n → 0 ≤ f n) (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b)
    (h : ∀ n, 1 ≤ n → f n ^ m * a ≤ (n : ℝ)^k ∧ (n : ℝ)^k ≤ b * f n ^ m) :
    f =Θ[atTop] (fun n : ℕ => (n : ℝ)^((k : ℝ)/m)) := by
  have ht : (fun n => f n ^ m) =Θ[atTop] (fun n : ℕ => (n : ℝ)^k) := by
    constructor
    · apply isBigO_iff.mpr
      refine ⟨a⁻¹, eventually_atTop.mpr ⟨1, fun n hn => ?_⟩⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hf n hn) _),
        Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)^k)]
      have hu := (h n hn).1
      apply (_root_.mul_le_mul_iff_right₀ ha).mp
      simpa [mul_assoc, ha.ne', mul_comm] using hu
    · apply isBigO_iff.mpr
      refine ⟨b, eventually_atTop.mpr ⟨1, fun n hn => ?_⟩⟩
      simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hf n hn) _),
        abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)^k), abs_of_nonneg (hf n hn)] using (h n hn).2
  have hp := ht.rpow (r := (m : ℝ)⁻¹)
    (eventually_atTop.mpr ⟨1, fun n hn => pow_nonneg (hf n hn) _⟩)
    (Filter.Eventually.of_forall (fun n => by positivity))
  have hl : f =ᶠ[atTop] (fun n => (f n ^ m)^((m : ℝ)⁻¹)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (Real.pow_rpow_inv_natCast (hf n hn) hm).symm
  apply hl.trans_isTheta
  apply hp.trans_eventuallyEq
  filter_upwards [] with n
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  simp [div_eq_mul_inv]

private lemma kappa_real_theta :
    (fun n : ℕ => kappa .real n) =Θ[atTop] (fun n : ℕ => (n : ℝ)^(3/4:ℝ)) := by
  apply theta_of_powers (fun n => kappa .real n) 4 3 (by norm_num)
    (fun n hn => (kappa_pos .real hn).le) (8*Real.pi) (16*Real.pi)
    (by positivity) (by positivity)
  exact fun n hn => kappa_real_fourth_bounds hn

private lemma kappa_quaternion_theta :
    (fun n : ℕ => kappa .quaternion n) =Θ[atTop] (fun n : ℕ => (n : ℝ)^(3/2:ℝ)) := by
  apply theta_of_powers (fun n => kappa .quaternion n) 2 3 (by norm_num)
    (fun n hn => (kappa_pos .quaternion hn).le) (Real.pi^3/8) (Real.pi^3/4)
    (by positivity) (by positivity)
  intro n hn
  have h := kappa_quaternion_square_bounds hn
  constructor <;> nlinarith

private lemma kappa_complex_theta :
    (fun n : ℕ => kappa .complex n) =Θ[atTop] (fun n : ℕ => (n : ℝ)^(1:ℝ)) := by
  constructor
  · apply isBigO_iff.mpr
    refine ⟨Real.pi⁻¹, eventually_atTop.mpr ⟨1, fun n hn => ?_⟩⟩
    rw [kappa_complex hn, Real.rpow_one]
    simp [Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n), abs_of_pos Real.pi_pos,
      div_eq_mul_inv, mul_comm]
  · apply isBigO_iff.mpr
    refine ⟨Real.pi, eventually_atTop.mpr ⟨1, fun n hn => ?_⟩⟩
    rw [kappa_complex hn, Real.rpow_one]
    simp [Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n), abs_of_pos Real.pi_pos,
      div_eq_mul_inv, mul_comm, Real.pi_ne_zero]

end GinibrePermanent977.Anticoncentration

open GinibrePermanent977.Anticoncentration

theorem solution (F : Scalar) :
    (fun n : ℕ => kappa F n) =Θ[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (((F.beta : ℝ) + 2) / 4)) := by
  cases F
  · norm_num only [Scalar.beta, Nat.cast_one, show (1+2:ℝ)/4=3/4 by norm_num]
    exact kappa_real_theta
  · norm_num only [Scalar.beta, Nat.cast_ofNat, show (2+2:ℝ)/4=1 by norm_num]
    exact kappa_complex_theta
  · norm_num only [Scalar.beta, Nat.cast_ofNat, show (4+2:ℝ)/4=3/2 by norm_num]
    exact kappa_quaternion_theta





