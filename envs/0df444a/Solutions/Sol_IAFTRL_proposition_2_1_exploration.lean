-- Prove2me | solution 1 for IAFTRL.proposition_2_1_exploration
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T11:06:43.362782+00:00
-- url     : https://prove2.me/submissions/54123414-ede5-41fe-9adc-6f5554ef8c87

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_actionNorm
import Definitions.Def_IAFTRL_IsUniqueMin
import Definitions.Def_IAFTRL_IsCorrupted
import Definitions.Def_IAFTRL_regretVs
import Definitions.Def_IAFTRL_IsFeasibleAlloc
import Definitions.Def_IAFTRL_allocCost
import Definitions.Def_IAFTRL_allocMass
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_qSoft
import Definitions.Def_IAFTRL_proxyC
import Definitions.Def_IAFTRL_IsFeasible2_3
import Definitions.Def_IAFTRL_IsMin2_3
import Definitions.Def_IAFTRL_gapHat
import Definitions.Def_IAFTRL_Gam
import Definitions.Def_IAFTRL_Bc
import Definitions.Def_IAFTRL_chi
import Definitions.Def_IAFTRL_cR
import Theorems.Thm_IAFTRL_lemma_C_10
import Theorems.Thm_IAFTRL_lemma_C_13_good_event


namespace GE

lemma sum_inv_sq_le (T : ℕ) :
    ∑ t ∈ Finset.range T, 1 / ((t : ℝ) + 1) ^ 2 ≤ 2 - 2 / ((T : ℝ) + 1) := by
  induction T with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have key : 1 / ((n : ℝ) + 1) ^ 2 ≤ 2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 1 + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    push_cast
    linarith

lemma sum_inv_sq_le_two (T : ℕ) : ∑ t ∈ Finset.range T, 1 / ((t : ℝ) + 1) ^ 2 ≤ 2 := by
  have := sum_inv_sq_le T
  have : (0 : ℝ) ≤ 2 / ((T : ℝ) + 1) := by positivity
  linarith

/-- fourth roots -/
lemma qr_pow (s : ℝ) (hs : 0 ≤ s) (n : ℕ) : (s ^ ((1 : ℝ) / 4)) ^ n = s ^ ((n : ℝ) / 4) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
  ring_nf

lemma qr_four (s : ℝ) (hs : 0 ≤ s) : (s ^ ((1 : ℝ) / 4)) ^ 4 = s := by
  rw [qr_pow s hs 4]; norm_num

lemma qr_two (s : ℝ) (hs : 0 ≤ s) : (s ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt s := by
  rw [qr_pow s hs 2, Real.sqrt_eq_rpow]; norm_num

lemma qr_three (s : ℝ) (hs : 0 ≤ s) : (s ^ ((1 : ℝ) / 4)) ^ 3 = s ^ ((3 : ℝ) / 4) := by
  rw [qr_pow s hs 3]; norm_num

lemma qr_ge_one (s : ℝ) (hs : 1 ≤ s) : 1 ≤ s ^ ((1 : ℝ) / 4) :=
  Real.one_le_rpow hs (by norm_num)

lemma exp_neg_le (y : ℝ) (hy : 0 < y) : Real.exp (-y) ≤ (Nat.factorial 12 : ℝ) / y ^ 12 := by
  have h := Real.pow_div_factorial_le_exp y hy.le 12
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos y) (by positivity)]
  rw [div_le_iff₀ (by positivity)] at h
  linarith

/-- (C.172): the time envelope is summable, uniformly in the horizon. -/
lemma tail_sum (Cb : ℝ) (hCb : 0 < Cb) (T : ℕ) :
    ∑ t ∈ Finset.range T, Real.sqrt ((t : ℝ) + 1) *
        Real.exp (-(2 * ((t : ℝ) + 1) ^ ((1 : ℝ) / 4) / Cb)) ≤
      2 * ((Nat.factorial 12 : ℝ) * (Cb / 2) ^ 12) := by
  have hterm : ∀ t : ℕ, Real.sqrt ((t : ℝ) + 1) *
      Real.exp (-(2 * ((t : ℝ) + 1) ^ ((1 : ℝ) / 4) / Cb)) ≤
      (Nat.factorial 12 : ℝ) * (Cb / 2) ^ 12 * (1 / ((t : ℝ) + 1) ^ 2) := by
    intro t
    set s : ℝ := (t : ℝ) + 1 with hs
    have hs1 : 1 ≤ s := by simp only [s]; linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
    set u := s ^ ((1 : ℝ) / 4) with hu
    have hu1 : 1 ≤ u := qr_ge_one s hs1
    have hu0 : 0 < u := by linarith
    have hy : 0 < 2 * u / Cb := by positivity
    have h1 := exp_neg_le (2 * u / Cb) hy
    rw [← qr_two s (by linarith)]
    have hs2 : s ^ 2 = u ^ 8 := by rw [← qr_four s (by linarith)]; ring
    rw [hs2]
    calc u ^ 2 * Real.exp (-(2 * u / Cb))
        ≤ u ^ 2 * ((Nat.factorial 12 : ℝ) / (2 * u / Cb) ^ 12) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (Nat.factorial 12 : ℝ) * (Cb / 2) ^ 12 * (1 / u ^ 10) := by
          field_simp
      _ ≤ (Nat.factorial 12 : ℝ) * (Cb / 2) ^ 12 * (1 / u ^ 8) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply one_div_le_one_div_of_le (by positivity)
          exact pow_le_pow_right₀ hu1 (by norm_num)
  calc _ ≤ ∑ t ∈ Finset.range T, (Nat.factorial 12 : ℝ) * (Cb / 2) ^ 12 *
        (1 / ((t : ℝ) + 1) ^ 2) := Finset.sum_le_sum fun t _ => hterm t
    _ = (Nat.factorial 12 : ℝ) * (Cb / 2) ^ 12 *
        ∑ t ∈ Finset.range T, 1 / ((t : ℝ) + 1) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (Nat.factorial 12 : ℝ) * (Cb / 2) ^ 12 * 2 :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_le_two T) (by positivity)
    _ = 2 * ((Nat.factorial 12 : ℝ) * (Cb / 2) ^ 12) := by ring

/-- the learning-rate schedule `β_s = 16d + √(d s / L)`, `L = 1 + log K` -/
lemma beta_eq (d K s : ℕ) (hK : 1 ≤ K) :
    IAFTRL.beta d K s = 16 * d + Real.sqrt (d / (1 + Real.log K)) * Real.sqrt s := by
  have hlogK := Real.log_nonneg (show (1 : ℝ) ≤ K by exact_mod_cast hK)
  have hnn : (0 : ℝ) ≤ d / (1 + Real.log K) := by positivity
  unfold IAFTRL.beta
  rw [show (d : ℝ) * s / (1 + Real.log K) = d / (1 + Real.log K) * s by ring,
    Real.sqrt_mul hnn]

lemma beta_le (d K s : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s) :
    IAFTRL.beta d K s ≤ (16 * d + Real.sqrt (d / (1 + Real.log K))) * Real.sqrt s := by
  rw [beta_eq d K s hK]
  have h1 : 1 ≤ Real.sqrt (s : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by exact_mod_cast hs)
  have : (0 : ℝ) ≤ 16 * d := by positivity
  nlinarith

lemma beta_ge (d K s : ℕ) (hK : 1 ≤ K) :
    Real.sqrt (d / (1 + Real.log K)) * Real.sqrt s ≤ IAFTRL.beta d K s := by
  rw [beta_eq d K s hK]; have : (0 : ℝ) ≤ 16 * d := by positivity
  linarith

lemma cR_eq (d K : ℕ) (hK : 1 ≤ K) :
    IAFTRL.cR d K = Real.sqrt (d / (1 + Real.log K)) * (1 + Real.log K) := by
  have hL : 0 < 1 + Real.log K := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ K by exact_mod_cast hK); linarith
  unfold IAFTRL.cR
  rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
  rw [show (d : ℝ) * (1 + Real.log K) = (1 + Real.log K) ^ 2 * (d / (1 + Real.log K)) by
    field_simp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hL.le]
  ring

/-- (C.170a): `(β_{t+1} − β_t) log K ≤ c_R / √(t+1)` and `β_{t+1} − β_t ≤ c_β` -/
lemma beta_diff (d K t : ℕ) (hK : 1 ≤ K) :
    0 ≤ IAFTRL.beta d K (t + 1) - IAFTRL.beta d K t ∧
    IAFTRL.beta d K (t + 1) - IAFTRL.beta d K t ≤ Real.sqrt (d / (1 + Real.log K)) ∧
    (IAFTRL.beta d K (t + 1) - IAFTRL.beta d K t) * Real.log K ≤
      IAFTRL.cR d K / Real.sqrt ((t : ℝ) + 1) := by
  have hlogK := Real.log_nonneg (show (1 : ℝ) ≤ K by exact_mod_cast hK)
  rw [beta_eq d K (t + 1) hK, beta_eq d K t hK, cR_eq d K hK]
  set c := Real.sqrt (d / (1 + Real.log K))
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  push_cast
  set a := Real.sqrt ((t : ℝ) + 1)
  set b := Real.sqrt (t : ℝ)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = t + 1 := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = t := Real.sq_sqrt (by positivity)
  have hab : b ≤ a := Real.sqrt_le_sqrt (by linarith)
  have hd : a - b ≤ 1 / a := by
    rw [le_div_iff₀ ha]
    nlinarith
  have hd1 : a - b ≤ 1 := by
    have : 1 ≤ a := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by
      have := (Nat.cast_nonneg t : (0 : ℝ) ≤ t); linarith)
    calc a - b ≤ 1 / a := hd
      _ ≤ 1 := by rw [div_le_one ha]; exact this
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have e : 16 * (d : ℝ) + c * a - (16 * d + c * b) = c * (a - b) := by ring
  rw [e]
  calc c * (a - b) * Real.log K ≤ c * (1 / a) * (1 + Real.log K) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hd hc) (by linarith) hlogK
        exact mul_nonneg hc (by positivity)
    _ = c * (1 + Real.log K) / a := by ring

/-- (C.170b): `2d / β_{t+1} ≤ 2 c_R / √(t+1)` -/
lemma two_d_div_beta (d K t : ℕ) (hK : 1 ≤ K) (hd : 1 ≤ d) :
    2 * (d : ℝ) / IAFTRL.beta d K (t + 1) ≤ 2 * IAFTRL.cR d K / Real.sqrt ((t : ℝ) + 1) := by
  have hlogK := Real.log_nonneg (show (1 : ℝ) ≤ K by exact_mod_cast hK)
  have hL : 0 < 1 + Real.log K := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hge := beta_ge d K (t + 1) hK
  rw [cR_eq d K hK]
  set c := Real.sqrt (d / (1 + Real.log K)) with hcdef
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc2 : c ^ 2 = d / (1 + Real.log K) := Real.sq_sqrt (by positivity)
  set a := Real.sqrt ((t : ℝ) + 1)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  push_cast at hge
  have hβ : 0 < IAFTRL.beta d K (t + 1) := by unfold IAFTRL.beta; positivity
  calc 2 * (d : ℝ) / IAFTRL.beta d K (t + 1) ≤ 2 * d / (c * a) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hge
    _ = 2 * (c * (1 + Real.log K)) / a := by
        field_simp
        rw [hc2]
        field_simp

end GE

open Matrix IAFTRL

namespace GE

variable {d K : ℕ}

lemma qSoft_norm (β : ℝ) (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (jstar : Fin K)
    (a : Fin K) :
    qSoft β arms S a = Real.exp (-((arms a - arms jstar) ⬝ᵥ S / β)) /
      ∑ b, Real.exp (-((arms b - arms jstar) ⬝ᵥ S / β)) := by
  unfold qSoft
  have hfac : ∀ c, Real.exp (-(arms c ⬝ᵥ S) / β) = Real.exp (-(arms jstar ⬝ᵥ S) / β) *
      Real.exp (-((arms c - arms jstar) ⬝ᵥ S / β)) := by
    intro c; rw [← Real.exp_add]; congr 1; rw [sub_dotProduct]; ring
  rw [Finset.sum_congr rfl fun c _ => hfac c, hfac a, ← Finset.mul_sum,
    mul_div_mul_left _ _ (Real.exp_pos _).ne']

lemma Z_ge_one (β : ℝ) (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (jstar : Fin K) :
    1 ≤ ∑ b, Real.exp (-((arms b - arms jstar) ⬝ᵥ S / β)) := by
  have h := Finset.single_le_sum (f := fun b => Real.exp (-((arms b - arms jstar) ⬝ᵥ S / β)))
    (fun b _ => (Real.exp_pos _).le) (Finset.mem_univ jstar)
  simpa using h

lemma q_le (β : ℝ) (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (jstar : Fin K) (a : Fin K) :
    qSoft β arms S a ≤ Real.exp (-((arms a - arms jstar) ⬝ᵥ S / β)) := by
  rw [qSoft_norm β arms S jstar a]
  exact div_le_self (Real.exp_pos _).le (Z_ge_one β arms S jstar)

lemma q_pos (β : ℝ) (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (jstar : Fin K) (a : Fin K) :
    0 < qSoft β arms S a := by
  rw [qSoft_norm β arms S jstar a]
  exact div_pos (Real.exp_pos _) (lt_of_lt_of_le one_pos (Z_ge_one β arms S jstar))

lemma q_sum (β : ℝ) (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (jstar : Fin K) :
    ∑ a, qSoft β arms S a = 1 := by
  simp_rw [qSoft_norm β arms S jstar]
  rw [← Finset.sum_div]
  exact div_self (lt_of_lt_of_le one_pos (Z_ge_one β arms S jstar)).ne'

lemma one_add_mul_exp_neg (x : ℝ) : (1 + x) * Real.exp (-x) ≤ 2 * Real.exp (-(x / 2)) := by
  have h := Real.add_one_le_exp (x / 2)
  have e1 : Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (-(x / 2))
  rw [e1]
  nlinarith

/-- (C.168): entropy envelope under separation. -/
lemma entropy_env (β : ℝ) (hβ : 0 < β) (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ)
    (jstar : Fin K) (hsep : ∀ a, a ≠ jstar → 0 ≤ (arms a - arms jstar) ⬝ᵥ S) :
    -∑ a, qSoft β arms S a * Real.log (qSoft β arms S a) ≤
      2 * ∑ a ∈ Finset.univ.erase jstar,
        Real.exp (-((arms a - arms jstar) ⬝ᵥ S / (2 * β))) := by
  classical
  set x : Fin K → ℝ := fun a => (arms a - arms jstar) ⬝ᵥ S / β with hx
  have hx0 : x jstar = 0 := by simp [x]
  have hxnn : ∀ a, 0 ≤ x a := by
    intro a
    by_cases h : a = jstar
    · rw [h, hx0]
    · exact div_nonneg (hsep a h) hβ.le
  set Z := ∑ b, Real.exp (-x b) with hZ
  have hZ1 : 1 ≤ Z := Z_ge_one β arms S jstar
  have hZpos : 0 < Z := by linarith
  have hq : ∀ a, qSoft β arms S a = Real.exp (-x a) / Z := fun a => qSoft_norm β arms S jstar a
  have hlog : ∀ a, Real.log (qSoft β arms S a) = -x a - Real.log Z := by
    intro a; rw [hq a, Real.log_div (Real.exp_pos _).ne' hZpos.ne', Real.log_exp]
  have hsum1 := q_sum β arms S jstar
  have hH : -∑ a, qSoft β arms S a * Real.log (qSoft β arms S a) =
      ∑ a, qSoft β arms S a * x a + Real.log Z := by
    simp_rw [hlog]
    have : ∑ a, qSoft β arms S a * (-x a - Real.log Z) =
        -(∑ a, qSoft β arms S a * x a) - Real.log Z * ∑ a, qSoft β arms S a := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [this, hsum1]; ring
  rw [hH]
  have hlogZ : Real.log Z ≤ ∑ a ∈ Finset.univ.erase jstar, Real.exp (-x a) := by
    have h1 := Real.log_le_sub_one_of_pos hZpos
    have h2 : Z = Real.exp (-x jstar) + ∑ a ∈ Finset.univ.erase jstar, Real.exp (-x a) :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ jstar)).symm
    rw [h2, hx0] at h1 ⊢
    simp only [neg_zero, Real.exp_zero] at h1 ⊢
    linarith
  have hqx : ∑ a, qSoft β arms S a * x a ≤
      ∑ a ∈ Finset.univ.erase jstar, x a * Real.exp (-x a) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ jstar), hx0, mul_zero, zero_add]
    exact Finset.sum_le_sum fun a _ => by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (q_le β arms S jstar a) (hxnn a)
  have hfinal : ∑ a ∈ Finset.univ.erase jstar, (Real.exp (-x a) + x a * Real.exp (-x a)) ≤
      ∑ a ∈ Finset.univ.erase jstar, 2 * Real.exp (-(x a / 2)) :=
    Finset.sum_le_sum fun a _ => by
      have := one_add_mul_exp_neg (x a); nlinarith
  have hx2 : ∀ a, x a / 2 = (arms a - arms jstar) ⬝ᵥ S / (2 * β) := by
    intro a; simp only [x]; field_simp
  rw [Finset.mul_sum]
  simp_rw [← hx2]
  rw [Finset.sum_add_distrib] at hfinal
  linarith

/-- the reference action is `a*` when `a*` is the strict minimizer -/
lemma refArm_eq (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (jstar : Fin K)
    (hmin : ∀ a, a ≠ jstar → arms jstar ⬝ᵥ S < arms a ⬝ᵥ S) : refArm arms S = arms jstar := by
  classical
  unfold refArm
  have hne : (Finset.univ.filter fun j : Fin K => ∀ i, arms j ⬝ᵥ S ≤ arms i ⬝ᵥ S).Nonempty := by
    refine ⟨jstar, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => ?_⟩⟩
    by_cases hi : i = jstar
    · rw [hi]
    · exact (hmin i hi).le
  rw [dif_pos hne]
  have hmem := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  congr 1
  by_contra hj
  exact absurd (hmem jstar) (not_le.mpr (hmin _ hj))

lemma chi_le_exp_abs (x : ℝ) : chi x ≤ Real.exp |x| := by
  unfold chi
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    have : Real.exp (-x) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    linarith
  · rw [abs_of_neg h]
    have : Real.exp x ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    linarith

/-- centering inequality, finite form of Lemma J.4 (J.6) -/
lemma centering (q f : Fin K → ℝ) (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∑ a, q a = 1) :
    ∑ a, q a * chi (f a - ∑ c, q c * f c) ≤ ∑ a, q a * chi (2 * f a) := by
  set m := ∑ c, q c * f c with hm
  set A := ∑ a, q a * Real.exp (f a) with hA
  set B := ∑ a, q a * Real.exp (-f a) with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun a _ => mul_nonneg (hq0 a) (Real.exp_pos _).le
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun a _ => mul_nonneg (hq0 a) (Real.exp_pos _).le
  have hJ1 : Real.exp m ≤ A := by
    have := convexOn_exp.map_sum_le (t := Finset.univ) (w := q) (p := f)
      (fun a _ => hq0 a) hq1 (fun a _ => Set.mem_univ _)
    simpa [smul_eq_mul] using this
  have hJ2 : Real.exp (-m) ≤ B := by
    have := convexOn_exp.map_sum_le (t := Finset.univ) (w := q) (p := fun a => -f a)
      (fun a _ => hq0 a) hq1 (fun a _ => Set.mem_univ _)
    have e : ∑ a, q a • (-f a) = -m := by
      simp only [smul_eq_mul, mul_neg, Finset.sum_neg_distrib, m]
    simpa [smul_eq_mul, e] using this
  have hA2 : A ^ 2 ≤ ∑ a, q a * Real.exp (2 * f a) := by
    have := (convexOn_pow 2).map_sum_le (t := Finset.univ) (w := q)
      (p := fun a => Real.exp (f a)) (fun a _ => hq0 a) hq1
      (fun a _ => Set.mem_Ici.mpr (Real.exp_pos _).le)
    have e : ∀ a, Real.exp (f a) ^ 2 = Real.exp (2 * f a) := by
      intro a; rw [sq, ← Real.exp_add]; ring_nf
    simpa [smul_eq_mul, e] using this
  have hB2 : B ^ 2 ≤ ∑ a, q a * Real.exp (-(2 * f a)) := by
    have := (convexOn_pow 2).map_sum_le (t := Finset.univ) (w := q)
      (p := fun a => Real.exp (-f a)) (fun a _ => hq0 a) hq1
      (fun a _ => Set.mem_Ici.mpr (Real.exp_pos _).le)
    have e : ∀ a, Real.exp (-f a) ^ 2 = Real.exp (-(2 * f a)) := by
      intro a; rw [sq, ← Real.exp_add]; ring_nf
    simpa [smul_eq_mul, e] using this
  have hL : ∑ a, q a * chi (f a - m) = Real.exp (-m) * A + Real.exp m * B - 2 := by
    unfold chi
    have : ∀ a, q a * (Real.exp (f a - m) + Real.exp (-(f a - m)) - 2) =
        Real.exp (-m) * (q a * Real.exp (f a)) + Real.exp m * (q a * Real.exp (-f a)) - 2 * q a := by
      intro a
      rw [show f a - m = f a + -m by ring, Real.exp_add,
        show -(f a + -m) = -f a + m by ring, Real.exp_add]
      ring
    rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hq1]
    ring
  have hR : ∑ a, q a * chi (2 * f a) =
      ∑ a, q a * Real.exp (2 * f a) + ∑ a, q a * Real.exp (-(2 * f a)) - 2 := by
    unfold chi
    have : ∑ a, q a * (Real.exp (2 * f a) + Real.exp (-(2 * f a)) - 2) =
        ∑ a, q a * Real.exp (2 * f a) + ∑ a, q a * Real.exp (-(2 * f a)) - 2 * ∑ a, q a := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [this, hq1, mul_one]
  rw [hL, hR]
  have h1 : Real.exp (-m) * A ≤ B * A := mul_le_mul_of_nonneg_right hJ2 hA0
  have h2 : Real.exp m * B ≤ A * B := mul_le_mul_of_nonneg_right hJ1 hB0
  nlinarith [sq_nonneg (A - B)]

/-- (C.169): proxy-function envelope under strict separation, for any feasible law. -/
lemma proxy_env (arms : Fin K → Fin d → ℝ) (t : ℕ) (S : Fin d → ℝ) (p : Fin K → ℝ)
    (jstar : Fin K) (hfeas : IsFeasible2_3 arms t S p)
    (hsep : ∀ a, a ≠ jstar → 0 < (arms a - arms jstar) ⬝ᵥ S) (hB : 4 ≤ Bc K)
    (hβ : 0 < beta d K t) :
    proxyC arms t S p ≤ Real.exp 2 * beta d K t *
      ∑ a ∈ Finset.univ.erase jstar,
        Real.exp (-((arms a - arms jstar) ⬝ᵥ S / (2 * beta d K t))) := by
  classical
  obtain ⟨hp0, hp1, -, hrow, -, -⟩ := hfeas
  set β := beta d K t with hβdef
  set q := qSoft β arms S with hqdef
  set X : Fin K → ℝ := fun a => (arms a - arms jstar) ⬝ᵥ S with hXdef
  have hr : refArm arms S = arms jstar := by
    refine refArm_eq arms S jstar fun a ha => ?_
    have := hsep a ha
    rw [sub_dotProduct] at this; linarith
  have hZ : ∀ a, Zd arms S a = X a := by
    intro a; unfold Zd; rw [hr]; simp only [X, sub_dotProduct]
  have hq0 : ∀ a, 0 ≤ q a := fun a => (q_pos β arms S jstar a).le
  have hq1 : ∑ a, q a = 1 := q_sum β arms S jstar
  have hBpos : 0 < Bc K := by linarith
  set E := Real.exp 2 * ∑ a ∈ Finset.univ.erase jstar, Real.exp (-(X a / (2 * β))) with hE
  have hinner : ∀ b, ∑ a, q a * chi ((arms a - abar arms q) ⬝ᵥ vCoef arms p b / β) ≤ E := by
    intro b
    set v := vCoef arms p b
    set f : Fin K → ℝ := fun a => (arms a - arms jstar) ⬝ᵥ v / β with hfdef
    have habar : ∀ a, (arms a - abar arms q) ⬝ᵥ v / β = f a - ∑ c, q c * f c := by
      intro a
      simp only [f, abar, sub_dotProduct, sum_dotProduct, smul_dotProduct, smul_eq_mul]
      have : ∑ c, q c * ((arms c ⬝ᵥ v - arms jstar ⬝ᵥ v) / β) =
          (∑ c, q c * arms c ⬝ᵥ v) / β - (∑ c, q c) * (arms jstar ⬝ᵥ v) / β := by
        rw [Finset.sum_mul, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun c _ => by ring
      rw [this, hq1]
      ring
    simp_rw [habar]
    refine (centering q f hq0 hq1).trans ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ jstar)]
    have hf0 : f jstar = 0 := by simp [f]
    rw [hf0, mul_zero, show chi 0 = 0 by norm_num [chi], mul_zero, zero_add, hE, Finset.mul_sum]
    refine Finset.sum_le_sum fun a ha => ?_
    have haj : a ≠ jstar := Finset.ne_of_mem_erase ha
    have hXa : 0 < X a := hsep a haj
    have hrowa := hrow a b
    rw [hr, hZ a] at hrowa
    have habs : |2 * f a| ≤ 2 + 2 * X a / (Bc K * β) := by
      rw [abs_mul, abs_two, show f a = (arms a - arms jstar) ⬝ᵥ v / β from rfl, abs_div,
        abs_of_pos hβ]
      rw [show 2 + 2 * X a / (Bc K * β) = 2 * ((β + X a / Bc K) / β) by field_simp]
      gcongr
    have h1 : q a * chi (2 * f a) ≤ q a * Real.exp |2 * f a| :=
      mul_le_mul_of_nonneg_left (chi_le_exp_abs _) (hq0 a)
    have h2 : q a * Real.exp |2 * f a| ≤
        Real.exp (-(X a / β)) * Real.exp (2 + 2 * X a / (Bc K * β)) :=
      mul_le_mul (q_le β arms S jstar a) (Real.exp_le_exp.mpr habs) (Real.exp_pos _).le
        (Real.exp_pos _).le
    have h3 : Real.exp (-(X a / β)) * Real.exp (2 + 2 * X a / (Bc K * β)) ≤
        Real.exp 2 * Real.exp (-(X a / (2 * β))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hk : 2 * X a / (Bc K * β) ≤ X a / (2 * β) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg hXa.le hβ.le) (sub_nonneg.mpr hB)]
      have e1 : X a / (2 * β) = X a / β - X a / (2 * β) := by field_simp; ring
      linarith
    linarith
  unfold proxyC
  rw [← hβdef, ← hqdef]
  calc β * ∑ b, p b * ∑ a, q a * chi ((arms a - abar arms q) ⬝ᵥ vCoef arms p b / β)
      ≤ β * ∑ b, p b * E := by
        apply mul_le_mul_of_nonneg_left _ hβ.le
        exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hinner b) (hp0 b)
    _ = Real.exp 2 * β * ∑ a ∈ Finset.univ.erase jstar, Real.exp (-(X a / (2 * β))) := by
        rw [← Finset.sum_mul, hp1, one_mul, hE]; ring

end GE

namespace GE

open MeasureTheory

lemma int_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f g : Ω → ℝ)
    (hfg : ∀ ω, f ω ≤ g ω) (hg : Integrable g P) (hg0 : 0 ≤ ∫ ω, g ω ∂P) :
    ∫ ω, f ω ∂P ≤ ∫ ω, g ω ∂P := by
  by_cases hf : Integrable f P
  · exact integral_mono hf hg hfg
  · rw [integral_undef hf]; exact hg0

/-- the integral of a two-valued step function on `G` / `Gᶜ` -/
lemma int_split {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : Set Ω) (hG : MeasurableSet G) (f : Ω → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∀ ω, f ω ≤ G.indicator (fun _ => a) ω + Gᶜ.indicator (fun _ => b) ω) :
    ∫ ω, f ω ∂P ≤ a + b * (P Gᶜ).toReal := by
  have hint : Integrable (fun ω => G.indicator (fun _ => a) ω + Gᶜ.indicator (fun _ => b) ω) P :=
    ((integrable_const a).indicator hG).add ((integrable_const b).indicator hG.compl)
  have hval : ∫ ω, (G.indicator (fun _ => a) ω + Gᶜ.indicator (fun _ => b) ω) ∂P =
      P.real G * a + P.real Gᶜ * b := by
    rw [integral_add ((integrable_const a).indicator hG) ((integrable_const b).indicator hG.compl),
      integral_indicator_const _ hG, integral_indicator_const _ hG.compl, smul_eq_mul, smul_eq_mul]
  have hle := int_le P f _ hf hint (by rw [hval]; positivity)
  rw [hval] at hle
  have h1 : P.real G ≤ 1 := measureReal_le_one
  have h2 : P.real Gᶜ = (P Gᶜ).toReal := rfl
  nlinarith [measureReal_nonneg (μ := P) (s := G), measureReal_nonneg (μ := P) (s := Gᶜ)]

/-- envelope bookkeeping: under the separation `X_a ≥ 4(t+1)^{3/4}`, `e^{-X_a/(2β_{t+1})} ≤ e^{-2u/C_β}` -/
lemma sep_exp {d K : ℕ} (hd : 1 ≤ d) (hK : 1 ≤ K) (t : ℕ) (X : ℝ)
    (hX : 4 * ((t : ℝ) + 1) ^ ((3 : ℝ) / 4) ≤ X) :
    Real.exp (-(X / (2 * IAFTRL.beta d K (t + 1)))) ≤
      Real.exp (-(2 * ((t : ℝ) + 1) ^ ((1 : ℝ) / 4) /
        (16 * d + Real.sqrt (d / (1 + Real.log K))))) := by
  apply Real.exp_le_exp.mpr
  set Cb := 16 * (d : ℝ) + Real.sqrt (d / (1 + Real.log K)) with hCb
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hCbpos : 0 < Cb := by positivity
  set s : ℝ := (t : ℝ) + 1 with hs
  have hs1 : 1 ≤ s := by simp only [s]; linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  set u := s ^ ((1 : ℝ) / 4) with hu
  have hu1 : 1 ≤ u := qr_ge_one s hs1
  have hβle := beta_le d K (t + 1) hK (by omega)
  have hβpos : 0 < IAFTRL.beta d K (t + 1) := by unfold IAFTRL.beta; positivity
  push_cast at hβle
  rw [← hs, ← qr_two s (by linarith), ← hu] at hβle
  rw [← qr_three s (by linarith), ← hu] at hX
  have key : 2 * u / Cb ≤ X / (2 * IAFTRL.beta d K (t + 1)) := by
    rw [div_le_div_iff₀ hCbpos (by positivity)]
    have : 0 < u := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hβle (show (0 : ℝ) ≤ 4 * u by positivity)]
  linarith

end GE

namespace EX

open Matrix IAFTRL MeasureTheory

variable {d K : ℕ}

lemma abs_dot_le (arms : Fin K → Fin d → ℝ) (θ : Fin d → ℝ) (j : Fin K) :
    |arms j ⬝ᵥ θ| ≤ actionNorm arms θ :=
  le_ciSup (f := fun j => |arms j ⬝ᵥ θ|) (Set.finite_range _).bddAbove j

/-- `Δ(a) ≤ 2` from `‖θ‖_𝒜 ≤ 1` -/
lemma gap_le_two (arms : Fin K → Fin d → ℝ) (θ : Fin d → ℝ) (jstar a : Fin K)
    (hθ : actionNorm arms θ ≤ 1) : (arms a - arms jstar) ⬝ᵥ θ ≤ 2 := by
  rw [sub_dotProduct]
  have h1 := abs_dot_le arms θ a
  have h2 := abs_dot_le arms θ jstar
  have h3 := le_abs_self (arms a ⬝ᵥ θ)
  have h4 := neg_abs_le (arms jstar ⬝ᵥ θ)
  linarith

lemma gap_nonneg (arms : Fin K → Fin d → ℝ) (θ : Fin d → ℝ) (jstar a : Fin K)
    (hu : IsUniqueMin arms θ jstar) : 0 ≤ (arms a - arms jstar) ⬝ᵥ θ := by
  by_cases ha : a = jstar
  · rw [ha, sub_self, zero_dotProduct]
  · have := hu a ha; rw [sub_dotProduct]; linarith

/-- (C.73), last display: on every history `⟨p − q, Δ⟩ ≤ 2γ ≤ 2Γ ≤ 8 c_R / √(t+1)` -/
lemma crude (hd : 1 ≤ d) (hK : 1 ≤ K) (arms : Fin K → Fin d → ℝ) (θ : Fin d → ℝ)
    (jstar : Fin K) (hθ : actionNorm arms θ ≤ 1) (hu : IsUniqueMin arms θ jstar) (t : ℕ)
    (S : Fin d → ℝ) (p : Fin K → ℝ) (hp : IsFeasible2_3 arms (t + 1) S p) :
    ∑ a, (p a - qSoft (beta d K (t + 1)) arms S a) * ((arms a - arms jstar) ⬝ᵥ θ) ≤
      8 * cR d K / Real.sqrt ((t : ℝ) + 1) := by
  obtain ⟨-, -, ⟨w, hw0, hwΓ, hpw⟩, -⟩ := hp
  have hγ0 : 0 ≤ ∑ b, w b := Finset.sum_nonneg fun b _ => hw0 b
  have hterm : ∀ a, (p a - qSoft (beta d K (t + 1)) arms S a) * ((arms a - arms jstar) ⬝ᵥ θ) ≤
      2 * w a := by
    intro a
    have hpa : p a = (1 - ∑ b, w b) * qSoft (beta d K (t + 1)) arms S a + w a := by
      rw [hpw]
    rw [hpa]
    have hqa : 0 ≤ qSoft (beta d K (t + 1)) arms S a := (GE.q_pos _ arms S jstar a).le
    have h2 := gap_le_two arms θ jstar a hθ
    have h0 := gap_nonneg arms θ jstar a hu
    have e : (1 - ∑ b, w b) * qSoft (beta d K (t + 1)) arms S a + w a -
        qSoft (beta d K (t + 1)) arms S a =
        w a - (∑ b, w b) * qSoft (beta d K (t + 1)) arms S a := by ring
    rw [e]
    have h5 : 0 ≤ (∑ b, w b) * qSoft (beta d K (t + 1)) arms S a * ((arms a - arms jstar) ⬝ᵥ θ) :=
      mul_nonneg (mul_nonneg hγ0 hqa) h0
    have h6 : w a * ((arms a - arms jstar) ⬝ᵥ θ) ≤ w a * 2 := mul_le_mul_of_nonneg_left h2 (hw0 a)
    nlinarith
  have hb := GE.two_d_div_beta d K t hK hd
  calc _ ≤ ∑ a, 2 * w a := Finset.sum_le_sum fun a _ => hterm a
    _ = 2 * ∑ b, w b := by rw [← Finset.mul_sum]
    _ ≤ 2 * Gam d K (t + 1) := by linarith
    _ = 4 * (2 * d / beta d K (t + 1)) := by unfold Gam; ring
    _ ≤ 4 * (2 * cR d K / Real.sqrt ((t : ℝ) + 1)) := by linarith
    _ = 8 * cR d K / Real.sqrt ((t : ℝ) + 1) := by ring

/-- (B.4): `B ≤ 2^25 · 374 · log K` for `K ≥ 2` -/
lemma Bc_le (hK : 2 ≤ K) : Bc K ≤ 2 ^ 25 * 374 * Real.log K := by
  unfold Bc
  have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hlog2 := Real.log_two_gt_d9
  have hlogK : Real.log 2 ≤ Real.log K := Real.log_le_log (by norm_num) hK'
  have hlog2K : Real.log (2 * (K : ℝ)) = Real.log 2 + Real.log K :=
    Real.log_mul (by norm_num) (by positivity)
  have hceil : (⌈256 + Real.log (2 * (K : ℝ))⌉ : ℝ) ≤ 256 + Real.log (2 * (K : ℝ)) + 1 :=
    (Int.ceil_lt_add_one _).le
  have h : (⌈256 + Real.log (2 * (K : ℝ))⌉ : ℝ) ≤ 374 * Real.log K := by linarith
  calc (2 : ℝ) ^ 25 * (⌈256 + Real.log (2 * (K : ℝ))⌉ : ℝ) ≤ 2 ^ 25 * (374 * Real.log K) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 2 ^ 25 * 374 * Real.log K := by ring

lemma Bc_pos (hK : 1 ≤ K) : 0 < Bc K := by
  unfold Bc
  have h2K : (1 : ℝ) ≤ 2 * K := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hl := Real.log_nonneg h2K
  have hc := Int.le_ceil (256 + Real.log (2 * (K : ℝ)))
  have : (0 : ℝ) < (⌈256 + Real.log (2 * (K : ℝ))⌉ : ℝ) := by linarith
  positivity

/-- on the good event the FTRL law is exponentially concentrated on `a*` (C.73a) -/
lemma q_gap_le (hd : 1 ≤ d) (hK : 1 ≤ K) (arms : Fin K → Fin d → ℝ) (θ : Fin d → ℝ)
    (jstar : Fin K) (hθ : actionNorm arms θ ≤ 1) (t : ℕ) (S : Fin d → ℝ)
    (hsep : ∀ a, a ≠ jstar → 4 * ((t : ℝ) + 1) ^ ((3 : ℝ) / 4) ≤ (arms a - arms jstar) ⬝ᵥ S) :
    ∑ a, qSoft (beta d K (t + 1)) arms S a * ((arms a - arms jstar) ⬝ᵥ θ) ≤
      2 * K * Real.exp (-(2 * ((t : ℝ) + 1) ^ ((1 : ℝ) / 4) /
        (16 * d + Real.sqrt (d / (1 + Real.log K))))) := by
  set e1 := Real.exp (-(2 * ((t : ℝ) + 1) ^ ((1 : ℝ) / 4) /
    (16 * d + Real.sqrt (d / (1 + Real.log K))))) with he1
  have he0 : 0 ≤ e1 := (Real.exp_pos _).le
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hβ : 0 < beta d K (t + 1) := by unfold beta; positivity
  have hterm : ∀ a, qSoft (beta d K (t + 1)) arms S a * ((arms a - arms jstar) ⬝ᵥ θ) ≤ 2 * e1 := by
    intro a
    have hq0 := (GE.q_pos (beta d K (t + 1)) arms S jstar a).le
    by_cases ha : a = jstar
    · rw [ha, sub_self, zero_dotProduct, mul_zero]; positivity
    · have hX := hsep a ha
      have hX0 : 0 ≤ (arms a - arms jstar) ⬝ᵥ S := le_trans (by positivity) hX
      have h1 := GE.q_le (beta d K (t + 1)) arms S jstar a
      have h2 : Real.exp (-((arms a - arms jstar) ⬝ᵥ S / beta d K (t + 1))) ≤
          Real.exp (-((arms a - arms jstar) ⬝ᵥ S / (2 * beta d K (t + 1)))) := by
        apply Real.exp_le_exp.mpr
        have : (arms a - arms jstar) ⬝ᵥ S / (2 * beta d K (t + 1)) ≤
            (arms a - arms jstar) ⬝ᵥ S / beta d K (t + 1) :=
          div_le_div_of_nonneg_left hX0 hβ (by linarith)
        linarith
      have h3 := GE.sep_exp hd hK t _ hX
      have hq : qSoft (beta d K (t + 1)) arms S a ≤ e1 := h1.trans (h2.trans h3)
      have hΔ2 := gap_le_two arms θ jstar a hθ
      have h4 : qSoft (beta d K (t + 1)) arms S a * ((arms a - arms jstar) ⬝ᵥ θ) ≤
          qSoft (beta d K (t + 1)) arms S a * 2 := mul_le_mul_of_nonneg_left hΔ2 hq0
      linarith
  calc _ ≤ ∑ _a : Fin K, 2 * e1 := Finset.sum_le_sum fun a _ => hterm a
    _ = 2 * K * e1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- (C.69): objective comparison with the comparison law built from `n` -/
lemma on_W (q p Δ Dh n : Fin K → ℝ) (jstar : Fin K) (ρ L U : ℝ)
    (hmin : ∑ a, p a * Dh a ≤ ∑ a, ((1 - ∑ b, (if b = jstar then 0 else ρ * n b)) * q a +
      (if a = jstar then 0 else ρ * n a)) * Dh a)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) (hΔ : ∀ a, 0 ≤ Δ a) (hΔj : Δ jstar = 0)
    (hn : ∀ a, 0 ≤ n a) (hρ : 0 ≤ ρ) (hL : 1 ≤ L) (hU : 0 ≤ U)
    (hLD : ∀ a, Δ a ≤ L * Dh a) (hDU : ∀ a, Dh a ≤ U * Δ a) :
    ∑ a, p a * Δ a ≤ L * U * ∑ a, q a * Δ a + L * ρ * U * ∑ a, n a * Δ a := by
  have hL0 : 0 ≤ L := by linarith
  have hDh0 : ∀ a, 0 ≤ Dh a := fun a => by
    have h1 := hLD a
    have h2 := hΔ a
    by_contra h
    have h3 : L * Dh a < 0 := mul_neg_of_pos_of_neg (by linarith) (lt_of_not_ge h)
    linarith
  have hw0 : ∀ a, 0 ≤ (if a = jstar then 0 else ρ * n a) := fun a => by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg hρ (hn a)
  have hγ0 : 0 ≤ ∑ b, (if b = jstar then 0 else ρ * n b) := Finset.sum_nonneg fun b _ => hw0 b
  have h1 : ∑ a, p a * Δ a ≤ L * ∑ a, p a * Dh a := by
    rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro a _
    have := mul_le_mul_of_nonneg_left (hLD a) (hp a)
    linarith [this, show p a * (L * Dh a) = L * (p a * Dh a) by ring]
  have hqD : ∑ a, q a * Dh a ≤ U * ∑ a, q a * Δ a := by
    rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro a _
    have := mul_le_mul_of_nonneg_left (hDU a) (hq a)
    linarith [this, show q a * (U * Δ a) = U * (q a * Δ a) by ring]
  have hqD0 : 0 ≤ ∑ a, q a * Dh a := Finset.sum_nonneg fun a _ => mul_nonneg (hq a) (hDh0 a)
  have hwD : ∑ a, (if a = jstar then 0 else ρ * n a) * Dh a ≤ ρ * U * ∑ a, n a * Δ a := by
    rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro a _
    by_cases ha : a = jstar
    · rw [if_pos ha, ha, hΔj]; simp
    · rw [if_neg ha]
      have := mul_le_mul_of_nonneg_left (hDU a) (mul_nonneg hρ (hn a))
      linarith [this, show ρ * n a * (U * Δ a) = ρ * U * (n a * Δ a) by ring]
  have h2 : ∑ a, ((1 - ∑ b, (if b = jstar then 0 else ρ * n b)) * q a +
      (if a = jstar then 0 else ρ * n a)) * Dh a =
      (1 - ∑ b, (if b = jstar then 0 else ρ * n b)) * ∑ a, q a * Dh a +
        ∑ a, (if a = jstar then 0 else ρ * n a) * Dh a := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a _; ring
  have h3 : (1 - ∑ b, (if b = jstar then 0 else ρ * n b)) * ∑ a, q a * Dh a ≤
      ∑ a, q a * Dh a := by nlinarith
  have h4 : ∑ a, p a * Dh a ≤ U * ∑ a, q a * Δ a + ρ * U * ∑ a, n a * Δ a := by
    rw [h2] at hmin; linarith
  calc ∑ a, p a * Δ a ≤ L * ∑ a, p a * Dh a := h1
    _ ≤ L * (U * ∑ a, q a * Δ a + ρ * U * ∑ a, n a * Δ a) := mul_le_mul_of_nonneg_left h4 hL0
    _ = _ := by ring

lemma inv_sqrt_le (c x : ℝ) (hc : 0 ≤ c) (hx : 1 ≤ x) : c / Real.sqrt x ≤ c := by
  have h : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx
  exact div_le_self hc h

/-- rounds below the time threshold -/
lemma small_case (c x T₀ : ℝ) (hc : 0 ≤ c) (hx : 1 ≤ x) (hxT : x < T₀) :
    c / Real.sqrt x ≤ c * T₀ ^ 2 * (1 / x ^ 2) := by
  have h1 := inv_sqrt_le c x hc hx
  have h2 : 1 ≤ T₀ ^ 2 * (1 / x ^ 2) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]; nlinarith
  calc c / Real.sqrt x ≤ c := h1
    _ ≤ c * (T₀ ^ 2 * (1 / x ^ 2)) := le_mul_of_one_le_right hc h2
    _ = c * T₀ ^ 2 * (1 / x ^ 2) := by ring

/-- failure of the mass threshold `L² ≤ √t / a_n`, charged through `1{L² > x} ≤ L⁸/x⁴` -/
lemma fail_n (c x an aD L : ℝ) (hc : 0 ≤ c) (hx : 1 ≤ x) (han : 0 < an) (haD : 0 ≤ aD)
    (h : ¬ L ^ 2 ≤ Real.sqrt x / an) :
    c / Real.sqrt x ≤ c * (an ^ 4 + aD ^ 4) / x ^ 2 * L ^ 8 := by
  have h1 := inv_sqrt_le c x hc hx
  have h' : Real.sqrt x < L ^ 2 * an := by
    have := lt_of_not_ge h
    rwa [div_lt_iff₀ han] at this
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have h4 : (Real.sqrt x) ^ 4 < (L ^ 2 * an) ^ 4 := pow_lt_pow_left₀ h' hs0 (by norm_num)
  have hsx : (Real.sqrt x) ^ 4 = x ^ 2 := by
    rw [show (Real.sqrt x) ^ 4 = ((Real.sqrt x) ^ 2) ^ 2 by ring, Real.sq_sqrt (by linarith)]
  rw [hsx] at h4
  have hL8 : 0 ≤ L ^ 8 := by positivity
  have h5 : 1 ≤ (an ^ 4 + aD ^ 4) / x ^ 2 * L ^ 8 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have e : (L ^ 2 * an) ^ 4 = an ^ 4 * L ^ 8 := by ring
    nlinarith [mul_nonneg (pow_nonneg haD 4) hL8]
  calc c / Real.sqrt x ≤ c := h1
    _ ≤ c * ((an ^ 4 + aD ^ 4) / x ^ 2 * L ^ 8) := le_mul_of_one_le_right hc h5
    _ = _ := by ring

/-- failure of the leverage threshold `L² ≤ t / a_Δ` -/
lemma fail_D (c x an aD L : ℝ) (hc : 0 ≤ c) (hx : 1 ≤ x) (han : 0 ≤ an) (haD : 0 < aD)
    (h : ¬ L ^ 2 ≤ x / aD) :
    c / Real.sqrt x ≤ c * (an ^ 4 + aD ^ 4) / x ^ 2 * L ^ 8 := by
  have h1 := inv_sqrt_le c x hc hx
  have h' : x < L ^ 2 * aD := by
    have := lt_of_not_ge h
    rwa [div_lt_iff₀ haD] at this
  have h4 : x ^ 4 < (L ^ 2 * aD) ^ 4 := pow_lt_pow_left₀ h' (by linarith) (by norm_num)
  have hx2 : x ^ 2 ≤ x ^ 4 := pow_le_pow_right₀ hx (by norm_num)
  have hL8 : 0 ≤ L ^ 8 := by positivity
  have h5 : 1 ≤ (an ^ 4 + aD ^ 4) / x ^ 2 * L ^ 8 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have e : (L ^ 2 * aD) ^ 4 = aD ^ 4 * L ^ 8 := by ring
    nlinarith [mul_nonneg (pow_nonneg han 4) hL8]
  calc c / Real.sqrt x ≤ c := h1
    _ ≤ c * ((an ^ 4 + aD ^ 4) / x ^ 2 * L ^ 8) := le_mul_of_one_le_right hc h5
    _ = _ := by ring

/-- the integral of the pathwise envelope -/
lemma int_g {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : Set Ω) (hG : MeasurableSet G) (f1 f3 f8 : Ω → ℝ)
    (h1 : Integrable (G.indicator f1) P) (h3 : Integrable (G.indicator f3) P)
    (h8 : Integrable (G.indicator f8) P) (k1 k3 k8 kc k0 : ℝ) :
    Integrable (fun ω => k1 * G.indicator f1 ω + k3 * G.indicator f3 ω +
      k8 * G.indicator f8 ω + Gᶜ.indicator (fun _ => kc) ω + k0) P ∧
    ∫ ω, (k1 * G.indicator f1 ω + k3 * G.indicator f3 ω + k8 * G.indicator f8 ω +
        Gᶜ.indicator (fun _ => kc) ω + k0) ∂P =
      k1 * ∫ ω, G.indicator f1 ω ∂P + k3 * ∫ ω, G.indicator f3 ω ∂P +
        k8 * ∫ ω, G.indicator f8 ω ∂P + kc * (P Gᶜ).toReal + k0 := by
  have i1 := h1.const_mul k1
  have i3 := h3.const_mul k3
  have i8 := h8.const_mul k8
  have ic : Integrable (Gᶜ.indicator (fun _ => kc)) P := (integrable_const kc).indicator hG.compl
  have i0 : Integrable (fun _ : Ω => k0) P := integrable_const k0
  have j2 : Integrable (fun ω => k1 * G.indicator f1 ω + k3 * G.indicator f3 ω) P := i1.add i3
  have j3 : Integrable (fun ω => k1 * G.indicator f1 ω + k3 * G.indicator f3 ω +
      k8 * G.indicator f8 ω) P := j2.add i8
  have j4 : Integrable (fun ω => k1 * G.indicator f1 ω + k3 * G.indicator f3 ω +
      k8 * G.indicator f8 ω + Gᶜ.indicator (fun _ => kc) ω) P := j3.add ic
  refine ⟨j4.add i0, ?_⟩
  rw [integral_add j4 i0, integral_add j3 ic, integral_add j2 i8, integral_add i1 i3,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_indicator_const _ hG.compl, integral_const]
  simp [smul_eq_mul, measureReal_def]
  ring

end EX

namespace EX

open Matrix IAFTRL MeasureTheory

/-- (C.71)–(C.73): the expected exploration cost of one round -/
lemma round {d K : ℕ} (hd : 1 ≤ d) (hK : 1 ≤ K) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    (θ : Fin d → ℝ) (jstar : Fin K) (Δ₀ : ℝ) (hθ : actionNorm arms θ ≤ 1)
    (hu : IsUniqueMin arms θ jstar) (hΔ₀ : 0 < Δ₀) (hΔ₀1 : Δ₀ ≤ 1)
    (hgap : ∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ)
    (n : Fin K → ℝ) (hn : IsFeasibleAlloc arms θ jstar n)
    (Cb an aD T₀ : ℝ) (hCb : Cb = 16 * (d : ℝ) + Real.sqrt (d / (1 + Real.log K)))
    (han : an = max 1 (4 * Bc K * Cb * allocMass n / d)) (haD : aD = 64 * Bc K / Δ₀ ^ 2)
    (hT₀ : T₀ = (32 * Cb) ^ 8 + (4 * Cb * (1 + Real.log K)) ^ 4)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℕ) (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R)
    (G : Set Ω) (hGm : MeasurableSet G) (L U : Ω → ℝ) (t : ℕ) (ht : t < T)
    (hsep : ∀ ω ∈ G, ∀ a, a ≠ jstar →
      4 * (t + 1 : ℝ) ^ ((3 : ℝ) / 4) ≤ (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω)
    (hLU : ∀ ω ∈ G, 1 ≤ L ω ∧ 0 ≤ U ω ∧
      (∀ a, a ≠ jstar → (t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ) ≤
        L ω * ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω)) ∧
      ∀ a, (arms a - arms jstar) ⬝ᵥ θ ≤ L ω * gapHat arms (t + 1) (R.cumEst arms t ω) a ∧
        gapHat arms (t + 1) (R.cumEst arms t ω) a ≤ U ω * ((arms a - arms jstar) ⬝ᵥ θ))
    (h1 : Integrable (G.indicator fun ω => L ω * U ω) P)
    (h3 : Integrable (G.indicator fun ω => L ω ^ 3 * U ω) P)
    (h8 : Integrable (G.indicator fun ω => L ω ^ 8) P) :
    ∫ ω, ∑ a, (R.p t ω a -
      qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) a) * ((arms a - arms jstar) ⬝ᵥ θ) ∂P ≤
      2 * K * Real.exp (-(2 * ((t : ℝ) + 1) ^ ((1 : ℝ) / 4) / Cb)) *
        ∫ ω, G.indicator (fun ω => L ω * U ω) ω ∂P +
      16 * Bc K * allocCost arms θ jstar n *
        ((∫ ω, G.indicator (fun ω => L ω ^ 3 * U ω) ω ∂P) / ((t : ℝ) + 1)) +
      8 * cR d K * (an ^ 4 + aD ^ 4) * (∫ ω, G.indicator (fun ω => L ω ^ 8) ω ∂P) *
        (1 / ((t : ℝ) + 1) ^ 2) +
      8 * (cR d K * ((P Gᶜ).toReal / Real.sqrt ((t : ℝ) + 1))) +
      8 * cR d K * T₀ ^ 2 * (1 / ((t : ℝ) + 1) ^ 2) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have hBpos : 0 < Bc K := EX.Bc_pos hK
  have hcR : 0 ≤ cR d K := Real.sqrt_nonneg _
  have hCbpos : 0 < Cb := by rw [hCb]; positivity
  have hΔnn : ∀ a, 0 ≤ (arms a - arms jstar) ⬝ᵥ θ := fun a => EX.gap_nonneg arms θ jstar a hu
  set cn := allocCost arms θ jstar n with hcn
  have hcn0 : 0 ≤ cn := Finset.sum_nonneg fun j _ => mul_nonneg (hn.1 j) (hΔnn j)
  have hcnE : ∑ a, n a * ((arms a - arms jstar) ⬝ᵥ θ) = cn := rfl
  have han1 : 1 ≤ an := by rw [han]; exact le_max_left _ _
  have haD0 : 0 < aD := by rw [haD]; positivity
  have hT₀a : 0 ≤ (32 * Cb) ^ 8 := by positivity
  have hT₀b : 0 ≤ (4 * Cb * (1 + Real.log K)) ^ 4 := by positivity
  set e : ℕ → ℝ := fun t => 2 * K * Real.exp (-(2 * ((t : ℝ) + 1) ^ ((1 : ℝ) / 4) / Cb)) with he
  have he0 : ∀ t, 0 ≤ e t := fun t => by simp only [e]; positivity
  show _ ≤ e t * ∫ ω, G.indicator (fun ω => L ω * U ω) ω ∂P + _ + _ + _ + _
  have hx1 : (1 : ℝ) ≤ (t : ℝ) + 1 := by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  have hx0 : (0 : ℝ) < (t : ℝ) + 1 := by linarith
  have hsq0 : 0 < Real.sqrt ((t : ℝ) + 1) := Real.sqrt_pos.mpr hx0
  have hk30 : 0 ≤ 16 * Bc K * cn / ((t : ℝ) + 1) := by positivity
  have hk80 : 0 ≤ 8 * cR d K * (an ^ 4 + aD ^ 4) / ((t : ℝ) + 1) ^ 2 := by positivity
  have hkc0 : 0 ≤ 8 * cR d K / Real.sqrt ((t : ℝ) + 1) := by positivity
  have hk00 : 0 ≤ 8 * cR d K * T₀ ^ 2 * (1 / ((t : ℝ) + 1) ^ 2) := by positivity
  obtain ⟨hint, hval⟩ := EX.int_g P G (hGm) (fun ω => L ω * U ω)
    (fun ω => L ω ^ 3 * U ω) (fun ω => L ω ^ 8) h1 h3 h8
    (e t) (16 * Bc K * cn / ((t : ℝ) + 1)) (8 * cR d K * (an ^ 4 + aD ^ 4) / ((t : ℝ) + 1) ^ 2)
    (8 * cR d K / Real.sqrt ((t : ℝ) + 1)) (8 * cR d K * T₀ ^ 2 * (1 / ((t : ℝ) + 1) ^ 2))
  have hI1 : ∀ ω, 0 ≤ G.indicator (fun ω => L ω * U ω) ω :=
    Set.indicator_nonneg fun ω hω => by
      obtain ⟨hL1, hU0, -, -⟩ := hLU ω hω
      exact mul_nonneg (by linarith) hU0
  have hI3 : ∀ ω, 0 ≤ G.indicator (fun ω => L ω ^ 3 * U ω) ω :=
    Set.indicator_nonneg fun ω hω => by
      obtain ⟨hL1, hU0, -, -⟩ := hLU ω hω
      exact mul_nonneg (pow_nonneg (by linarith) 3) hU0
  have hI8 : ∀ ω, 0 ≤ G.indicator (fun ω => L ω ^ 8) ω :=
    Set.indicator_nonneg fun ω _ => by positivity
  have hIc : ∀ ω, 0 ≤ Gᶜ.indicator (fun _ => 8 * cR d K / Real.sqrt ((t : ℝ) + 1)) ω :=
    Set.indicator_nonneg fun ω _ => hkc0
  have hg0 : ∀ ω, 0 ≤ e t * G.indicator (fun ω => L ω * U ω) ω +
      16 * Bc K * cn / ((t : ℝ) + 1) * G.indicator (fun ω => L ω ^ 3 * U ω) ω +
      8 * cR d K * (an ^ 4 + aD ^ 4) / ((t : ℝ) + 1) ^ 2 *
        G.indicator (fun ω => L ω ^ 8) ω +
      Gᶜ.indicator (fun _ => 8 * cR d K / Real.sqrt ((t : ℝ) + 1)) ω +
      8 * cR d K * T₀ ^ 2 * (1 / ((t : ℝ) + 1) ^ 2) := fun ω => by
    have := mul_nonneg (he0 t) (hI1 ω)
    have := mul_nonneg hk30 (hI3 ω)
    have := mul_nonneg hk80 (hI8 ω)
    have := hIc ω
    linarith
  have hpath : ∀ ω, ∑ a, (R.p t ω a - qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) a) *
      ((arms a - arms jstar) ⬝ᵥ θ) ≤
      e t * G.indicator (fun ω => L ω * U ω) ω +
      16 * Bc K * cn / ((t : ℝ) + 1) * G.indicator (fun ω => L ω ^ 3 * U ω) ω +
      8 * cR d K * (an ^ 4 + aD ^ 4) / ((t : ℝ) + 1) ^ 2 *
        G.indicator (fun ω => L ω ^ 8) ω +
      Gᶜ.indicator (fun _ => 8 * cR d K / Real.sqrt ((t : ℝ) + 1)) ω +
      8 * cR d K * T₀ ^ 2 * (1 / ((t : ℝ) + 1) ^ 2) := by
    intro ω
    have hmin := (hR t ht).2.1.2 ω
    have hcrude := EX.crude hd hK arms θ jstar hθ hu t (R.cumEst arms t ω) (R.p t ω) hmin.1
    by_cases hω : ω ∈ G
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, Set.indicator_of_mem hω,
        Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hω)]
      obtain ⟨hL1, hU0, hLX, hDh⟩ := hLU ω hω
      have hL0 : 0 ≤ L ω := by linarith
      have hA0 : 0 ≤ e t * (L ω * U ω) := mul_nonneg (he0 t) (mul_nonneg hL0 hU0)
      have hB0 : 0 ≤ 16 * Bc K * cn / ((t : ℝ) + 1) * (L ω ^ 3 * U ω) :=
        mul_nonneg hk30 (mul_nonneg (pow_nonneg hL0 3) hU0)
      have hL8 : 0 ≤ L ω ^ 8 := by positivity
      have hC0 : 0 ≤ 8 * cR d K * (an ^ 4 + aD ^ 4) / ((t : ℝ) + 1) ^ 2 * L ω ^ 8 :=
        mul_nonneg hk80 hL8
      by_cases hsm : (t : ℝ) + 1 < T₀
      · have := EX.small_case (8 * cR d K) ((t : ℝ) + 1) T₀ (by positivity) hx1 hsm
        linarith
      · have hTle : T₀ ≤ (t : ℝ) + 1 := le_of_not_gt hsm
        by_cases hn1 : L ω ^ 2 ≤ Real.sqrt ((t : ℝ) + 1) / an
        · by_cases hn2 : L ω ^ 2 ≤ ((t : ℝ) + 1) / aD
          · -- (C.69): objective comparison with the comparison law built from `n`
            have hcast : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
            have hT1 : (32 * Cb) ^ 8 ≤ ((t + 1 : ℕ) : ℝ) := by rw [hcast]; linarith
            have hT2 : (4 * Cb * (1 + Real.log K)) ^ 4 ≤ ((t + 1 : ℕ) : ℝ) := by
              rw [hcast]; linarith
            have hsep' : ∀ a, a ≠ jstar → 4 * (((t + 1 : ℕ) : ℝ)) ^ ((3 : ℝ) / 4) ≤
                (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω := by
              intro a ha; rw [hcast]; exact hsep ω hω a ha
            have hLX' : ∀ a, a ≠ jstar → ((t + 1 : ℕ) : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ) ≤
                L ω * ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω) := by
              intro a ha; rw [hcast]; exact hLX a ha
            have hLn' : L ω ^ 2 ≤ Real.sqrt ((t + 1 : ℕ) : ℝ) / an := by rw [hcast]; exact hn1
            have hLD' : L ω ^ 2 ≤ ((t + 1 : ℕ) : ℝ) / aD := by rw [hcast]; exact hn2
            rw [hCb] at hT1 hT2
            rw [han, hCb] at hLn'
            rw [haD] at hLD'
            have hfeas := lemma_C_10 hd arms hA θ hθ jstar hu Δ₀ hΔ₀ hΔ₀1 hgap n hn (t + 1)
              (R.cumEst arms t ω) (L ω) hT1 hT2 hsep' hL1 hLX' hLn' hLD'
            have hW := EX.on_W (qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω)) (R.p t ω)
              (fun a => (arms a - arms jstar) ⬝ᵥ θ) (gapHat arms (t + 1) (R.cumEst arms t ω))
              n jstar (16 * Bc K * L ω ^ 2 / ((t + 1 : ℕ) : ℝ)) (L ω) (U ω)
              (hmin.2 _ hfeas) hmin.1.1 (fun a => (GE.q_pos _ arms _ jstar a).le) hΔnn
              (by simp) hn.1 (by positivity) hL1 hU0 (fun a => (hDh a).1) (fun a => (hDh a).2)
            beta_reduce at hW
            rw [hcnE] at hW
            have hq := EX.q_gap_le hd hK arms θ jstar hθ t (R.cumEst arms t ω)
              (hsep ω hω)
            rw [← hCb] at hq
            have hq0 : 0 ≤ ∑ a, qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) a *
                ((arms a - arms jstar) ⬝ᵥ θ) :=
              Finset.sum_nonneg fun a _ =>
                mul_nonneg (GE.q_pos _ arms _ jstar a).le (hΔnn a)
            have hsplit : ∑ a, (R.p t ω a - qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) a) *
                ((arms a - arms jstar) ⬝ᵥ θ) =
                ∑ a, R.p t ω a * ((arms a - arms jstar) ⬝ᵥ θ) -
                  ∑ a, qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) a *
                    ((arms a - arms jstar) ⬝ᵥ θ) := by
              rw [← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl fun a _ => by ring
            have hρ : L ω * (16 * Bc K * L ω ^ 2 / ((t + 1 : ℕ) : ℝ)) * U ω * cn =
                16 * Bc K * cn / ((t : ℝ) + 1) * (L ω ^ 3 * U ω) := by
              rw [hcast]; ring
            have hLUq : L ω * U ω * ∑ a, qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) a *
                ((arms a - arms jstar) ⬝ᵥ θ) ≤ e t * (L ω * U ω) := by
              have := mul_le_mul_of_nonneg_left hq (mul_nonneg hL0 hU0)
              simp only [e]
              linarith
            rw [hsplit]
            linarith
          · have := EX.fail_D (8 * cR d K) ((t : ℝ) + 1) an aD (L ω) (by positivity) hx1
              (by linarith) haD0 hn2
            linarith
        · have := EX.fail_n (8 * cR d K) ((t : ℝ) + 1) an aD (L ω) (by positivity) hx1
            (by linarith) haD0.le hn1
          linarith
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, Set.indicator_of_notMem hω,
        Set.indicator_of_mem (Set.mem_compl hω)]
      linarith
  have hle := GE.int_le P _ _ hpath hint (integral_nonneg hg0)
  rw [hval] at hle
  have e1 : 16 * Bc K * cn / ((t : ℝ) + 1) *
      ∫ ω, G.indicator (fun ω => L ω ^ 3 * U ω) ω ∂P =
      16 * Bc K * cn * ((∫ ω, G.indicator (fun ω => L ω ^ 3 * U ω) ω ∂P) /
        ((t : ℝ) + 1)) := by ring
  have e2 : 8 * cR d K * (an ^ 4 + aD ^ 4) / ((t : ℝ) + 1) ^ 2 *
      ∫ ω, G.indicator (fun ω => L ω ^ 8) ω ∂P =
      8 * cR d K * (an ^ 4 + aD ^ 4) * (∫ ω, G.indicator (fun ω => L ω ^ 8) ω ∂P) *
        (1 / ((t : ℝ) + 1) ^ 2) := by ring
  have e3 : 8 * cR d K / Real.sqrt ((t : ℝ) + 1) * (P Gᶜ).toReal =
      8 * (cR d K * ((P Gᶜ).toReal / Real.sqrt ((t : ℝ) + 1))) := by ring
  linarith

end EX

open Matrix IAFTRL MeasureTheory

theorem solution : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d K : ℕ}, 1 ≤ d → ∀ (arms : Fin K → Fin d → ℝ), IsActionSet arms →
      ∀ (θ : Fin d → ℝ) (jstar : Fin K) (Δ₀ : ℝ),
        actionNorm arms θ ≤ 1 → IsUniqueMin arms θ jstar → 0 < Δ₀ → Δ₀ ≤ 1 →
        (∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) →
        ∀ n : Fin K → ℝ, IsFeasibleAlloc arms θ jstar n →
        ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (T : ℕ) (C : ℝ) (R : Run d K Ω), 1 ≤ T → 0 ≤ C →
          IsIAFTRLRun P arms T R → IsCorrupted P arms θ C T R →
          ∑ t ∈ Finset.range T, ∫ ω, ∑ a, (R.p t ω a -
              qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) a) *
            ((arms a - arms jstar) ⬝ᵥ θ) ∂P ≤
            c₀ * (allocCost arms θ jstar n * Real.log K * Real.log T +
              Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) + M := by
  classical
  obtain ⟨c₁, hc₁, hG⟩ := lemma_C_13_good_event
  refine ⟨16 * (2 ^ 25 * 374) * c₁, by positivity, ?_⟩
  intro d K hd arms hA θ jstar Δ₀ hθ hu hΔ₀ hΔ₀1 hgap n hn
  obtain ⟨M₁, hM₁⟩ := hG hd arms hA θ jstar Δ₀ hθ hu hΔ₀ hΔ₀1 hgap
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ jstar).elim0)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have hBpos : 0 < Bc K := EX.Bc_pos hK
  have hcR : 0 ≤ cR d K := Real.sqrt_nonneg _
  set Cb := 16 * (d : ℝ) + Real.sqrt (d / (1 + Real.log K)) with hCb
  have hCbpos : 0 < Cb := by positivity
  have hΔnn : ∀ a, 0 ≤ (arms a - arms jstar) ⬝ᵥ θ := fun a => EX.gap_nonneg arms θ jstar a hu
  set cn := allocCost arms θ jstar n with hcn
  have hcn0 : 0 ≤ cn := Finset.sum_nonneg fun j _ => mul_nonneg (hn.1 j) (hΔnn j)
  have hcnE : ∑ a, n a * ((arms a - arms jstar) ⬝ᵥ θ) = cn := rfl
  set an := max 1 (4 * Bc K * Cb * allocMass n / d) with han
  have han1 : 1 ≤ an := le_max_left _ _
  set aD := 64 * Bc K / Δ₀ ^ 2 with haD
  have haD0 : 0 < aD := by positivity
  set T₀ := (32 * Cb) ^ 8 + (4 * Cb * (1 + Real.log K)) ^ 4 with hT₀
  have hT₀a : 0 ≤ (32 * Cb) ^ 8 := by positivity
  have hT₀b : 0 ≤ (4 * Cb * (1 + Real.log K)) ^ 4 := by positivity
  set S0 := 2 * ((Nat.factorial 12 : ℝ) * (Cb / 2) ^ 12) with hS0
  refine ⟨|M₁| * (2 * K * S0) + 16 * Bc K * cn * (c₁ + M₁) +
    16 * cR d K * (an ^ 4 + aD ^ 4) * c₁ + 8 * M₁ + 16 * cR d K * T₀ ^ 2, ?_⟩
  intro Ω _ P _ T C R hT hC hR hcor
  obtain ⟨G, L, U, hGm, hsep, hfail, hLU, h8, h1, h3i, h3⟩ := hM₁ P T C R hT hC hR hcor
  set e : ℕ → ℝ := fun t => 2 * K * Real.exp (-(2 * ((t : ℝ) + 1) ^ ((1 : ℝ) / 4) / Cb)) with he
  have he0 : ∀ t, 0 ≤ e t := fun t => by simp only [e]; positivity
  -- per-round bound (C.71)–(C.73)
  have hround : ∀ t < T, ∫ ω, ∑ a, (R.p t ω a -
      qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) a) * ((arms a - arms jstar) ⬝ᵥ θ) ∂P ≤
      e t * ∫ ω, (G t).indicator (fun ω => L t ω * U t ω) ω ∂P +
      16 * Bc K * cn * ((∫ ω, (G t).indicator (fun ω => L t ω ^ 3 * U t ω) ω ∂P) /
        ((t : ℝ) + 1)) +
      8 * cR d K * (an ^ 4 + aD ^ 4) * (∫ ω, (G t).indicator (fun ω => L t ω ^ 8) ω ∂P) *
        (1 / ((t : ℝ) + 1) ^ 2) +
      8 * (cR d K * ((P (G t)ᶜ).toReal / Real.sqrt ((t : ℝ) + 1))) +
      8 * cR d K * T₀ ^ 2 * (1 / ((t : ℝ) + 1) ^ 2) := fun t ht =>
    EX.round hd hK arms hA θ jstar Δ₀ hθ hu hΔ₀ hΔ₀1 hgap n hn Cb an aD T₀ hCb han haD hT₀
      P T R hR (G t) (hGm t) (L t) (U t) t ht (hsep t ht) (hLU t ht) (h1 t ht).1 (h3i t ht)
      (h8 t ht).1
  -- summation (C.54)–(C.56)
  have hsum := Finset.sum_le_sum fun t ht => hround t (Finset.mem_range.mp ht)
  simp only [Finset.sum_add_distrib] at hsum
  have hA1 : ∑ t ∈ Finset.range T, e t * ∫ ω, (G t).indicator (fun ω => L t ω * U t ω) ω ∂P ≤
      |M₁| * (2 * K * S0) := by
    calc _ ≤ ∑ t ∈ Finset.range T, |M₁| * e t := by
          apply Finset.sum_le_sum; intro t ht
          have hI := (h1 t (Finset.mem_range.mp ht)).2
          have hI' : ∫ ω, (G t).indicator (fun ω => L t ω * U t ω) ω ∂P ≤ |M₁| :=
            hI.trans (le_abs_self _)
          have := mul_le_mul_of_nonneg_left hI' (he0 t)
          linarith [mul_comm (e t) |M₁|]
      _ = |M₁| * ∑ t ∈ Finset.range T, e t := by rw [Finset.mul_sum]
      _ ≤ |M₁| * (2 * K * S0) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have hts := GE.tail_sum Cb hCbpos T
          calc ∑ t ∈ Finset.range T, e t ≤ ∑ t ∈ Finset.range T, 2 * K *
                (Real.sqrt ((t : ℝ) + 1) *
                  Real.exp (-(2 * ((t : ℝ) + 1) ^ ((1 : ℝ) / 4) / Cb))) := by
                apply Finset.sum_le_sum; intro t _
                simp only [e]
                have hs1 : 1 ≤ Real.sqrt ((t : ℝ) + 1) := by
                  have := Real.sqrt_le_sqrt
                    (show (1 : ℝ) ≤ (t : ℝ) + 1 by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)])
                  simpa using this
                have hex := (Real.exp_pos (-(2 * ((t : ℝ) + 1) ^ ((1 : ℝ) / 4) / Cb))).le
                have hK0 : (0 : ℝ) ≤ 2 * K := by positivity
                have := mul_le_mul_of_nonneg_right hs1 hex
                have := mul_le_mul_of_nonneg_left this hK0
                linarith
            _ = 2 * K * ∑ t ∈ Finset.range T, Real.sqrt ((t : ℝ) + 1) *
                  Real.exp (-(2 * ((t : ℝ) + 1) ^ ((1 : ℝ) / 4) / Cb)) := by
                rw [Finset.mul_sum]
            _ ≤ 2 * K * S0 := mul_le_mul_of_nonneg_left hts (by positivity)
  have hA2 : ∑ t ∈ Finset.range T, 16 * Bc K * cn *
      ((∫ ω, (G t).indicator (fun ω => L t ω ^ 3 * U t ω) ω ∂P) / ((t : ℝ) + 1)) ≤
      16 * Bc K * cn * (c₁ * (1 + Real.log T) + M₁) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have hA3 : ∑ t ∈ Finset.range T, 8 * cR d K * (an ^ 4 + aD ^ 4) *
      (∫ ω, (G t).indicator (fun ω => L t ω ^ 8) ω ∂P) * (1 / ((t : ℝ) + 1) ^ 2) ≤
      16 * cR d K * (an ^ 4 + aD ^ 4) * c₁ := by
    have hk : 0 ≤ 8 * cR d K * (an ^ 4 + aD ^ 4) := by positivity
    calc _ ≤ ∑ t ∈ Finset.range T, 8 * cR d K * (an ^ 4 + aD ^ 4) * c₁ *
          (1 / ((t : ℝ) + 1) ^ 2) := by
          apply Finset.sum_le_sum; intro t ht
          have hI := (h8 t (Finset.mem_range.mp ht)).2
          have hp : (0 : ℝ) ≤ 1 / ((t : ℝ) + 1) ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hI hk) hp
      _ = 8 * cR d K * (an ^ 4 + aD ^ 4) * c₁ *
          ∑ t ∈ Finset.range T, 1 / ((t : ℝ) + 1) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 8 * cR d K * (an ^ 4 + aD ^ 4) * c₁ * 2 :=
          mul_le_mul_of_nonneg_left (GE.sum_inv_sq_le_two T) (by positivity)
      _ = 16 * cR d K * (an ^ 4 + aD ^ 4) * c₁ := by ring
  have hA4 : ∑ t ∈ Finset.range T, 8 * (cR d K * ((P (G t)ᶜ).toReal / Real.sqrt ((t : ℝ) + 1))) ≤
      8 * (c₁ * (Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) +
        M₁) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    linarith
  have hA5 : ∑ t ∈ Finset.range T, 8 * cR d K * T₀ ^ 2 * (1 / ((t : ℝ) + 1) ^ 2) ≤
      16 * cR d K * T₀ ^ 2 := by
    rw [← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left (GE.sum_inv_sq_le_two T)
      (show 0 ≤ 8 * cR d K * T₀ ^ 2 by positivity)
    linarith
  -- constants (B.4): `B c^n log T ≤ 2^25 · 374 · c^n log K log T`
  have hBcn : Bc K * cn ≤ 2 ^ 25 * 374 * Real.log K * cn := by
    rcases Nat.lt_or_ge K 2 with hK2 | hK2
    · have hK1 : K = 1 := by omega
      have h0 : cn = 0 := by
        apply Finset.sum_eq_zero; intro j _
        have : j = jstar := Fin.ext (by have := j.isLt; have := jstar.isLt; omega)
        rw [this, sub_self, zero_dotProduct, mul_zero]
      rw [h0]; simp
    · exact mul_le_mul_of_nonneg_right (EX.Bc_le hK2) hcn0
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by exact_mod_cast hT)
  have hX0 : 0 ≤ Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hΔ₀.le _)) (Real.sqrt_nonneg _)
  have hk1 := mul_le_mul_of_nonneg_right hBcn (show 0 ≤ 16 * c₁ * Real.log T by positivity)
  have hk2 := mul_le_mul_of_nonneg_right
    (show 8 * c₁ ≤ 16 * (2 ^ 25 * 374) * c₁ by linarith) hX0
  linarith [hsum, hA1, hA2, hA3, hA4, hA5, hk1, hk2]
