-- Prove2me | solution 1 for IAFTRL.proposition_2_1_stability
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T09:54:23.394645+00:00
-- url     : https://prove2.me/submissions/d4ca05b1-2873-4846-b4b5-c9174215a4d0

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
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_qSoft
import Definitions.Def_IAFTRL_proxyC
import Definitions.Def_IAFTRL_IsFeasible2_3
import Definitions.Def_IAFTRL_chi
import Definitions.Def_IAFTRL_cR
import Theorems.Thm_IAFTRL_lemma_C_24_good_event


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

open Matrix MeasureTheory IAFTRL

theorem solution : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d K : ℕ}, 1 ≤ d → ∀ (arms : Fin K → Fin d → ℝ), IsActionSet arms →
      ∀ (θ : Fin d → ℝ) (jstar : Fin K) (Δ₀ : ℝ),
        actionNorm arms θ ≤ 1 → IsUniqueMin arms θ jstar → 0 < Δ₀ → Δ₀ ≤ 1 →
        (∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) →
        ∀ n : Fin K → ℝ, IsFeasibleAlloc arms θ jstar n →
        ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (T : ℕ) (C : ℝ) (R : Run d K Ω), 1 ≤ T → 0 ≤ C →
          IsIAFTRLRun P arms T R → IsCorrupted P arms θ C T R →
          ∑ t ∈ Finset.range T, ∫ ω, proxyC arms (t + 1) (R.cumEst arms t ω) (R.p t ω) ∂P ≤
            c₀ * (allocCost arms θ jstar n * Real.log K * Real.log T +
              Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) + M := by
  classical
  obtain ⟨cG, hcG, hG⟩ := lemma_C_24_good_event
  refine ⟨2 * cG, by positivity, ?_⟩
  intro d K hd arms hA θ jstar Δ₀ hθ huniq hΔ₀ hΔ₀1 hgap n hn
  obtain ⟨MG, hMG⟩ := hG hd arms hA θ jstar Δ₀ hθ huniq hΔ₀ hΔ₀1 hgap
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ jstar).elim0)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set Cb := 16 * (d : ℝ) + Real.sqrt (d / (1 + Real.log K)) with hCb
  have hCbpos : 0 < Cb := by positivity
  set S0 := 2 * ((Nat.factorial 12 : ℝ) * (Cb / 2) ^ 12) with hS0
  refine ⟨Real.exp 2 * Cb * K * S0 + 2 * |MG|, ?_⟩
  intro Ω _ P _ T C R hT hC hR hcor
  obtain ⟨G, hGm, hsep, hfail⟩ := hMG P T C R hT hC hR hcor
  have hB : 4 ≤ Bc K := by
    unfold Bc
    have h1 : (256 : ℝ) ≤ ⌈256 + Real.log (2 * (K : ℝ))⌉ := by
      have := Int.le_ceil (256 + Real.log (2 * (K : ℝ)))
      have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
      have h2 : 0 ≤ Real.log (2 * (K : ℝ)) := Real.log_nonneg (by linarith)
      linarith
    nlinarith
  -- per-round bound
  set env : ℕ → ℝ := fun t => Real.sqrt ((t : ℝ) + 1) *
    Real.exp (-(2 * ((t : ℝ) + 1) ^ ((1 : ℝ) / 4) / Cb)) with henv
  have hround : ∀ t < T, ∫ ω, proxyC arms (t + 1) (R.cumEst arms t ω) (R.p t ω) ∂P ≤
      Real.exp 2 * Cb * K * env t + 2 * cR d K * ((P (G t)ᶜ).toReal / Real.sqrt ((t : ℝ) + 1)) := by
    intro t ht
    have hβpos : 0 < beta d K (t + 1) := by unfold beta; positivity
    have hsq : 0 < Real.sqrt ((t : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hcR : 0 ≤ cR d K := Real.sqrt_nonneg _
    have hfeas := fun ω => ((hR t ht).2.1.2 ω).1
    have hpt : ∀ ω, proxyC arms (t + 1) (R.cumEst arms t ω) (R.p t ω) ≤
        (G t).indicator (fun _ => Real.exp 2 * Cb * K * env t) ω +
        (G t)ᶜ.indicator (fun _ => 2 * cR d K / Real.sqrt ((t : ℝ) + 1)) ω := by
      intro ω
      by_cases hω : ω ∈ G t
      · rw [Set.indicator_of_mem hω, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hω),
          add_zero]
        have hX := hsep t ht ω hω
        have hpos : ∀ a, a ≠ jstar → 0 < (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω := by
          intro a ha
          have := hX a ha
          have : 0 < 4 * ((t : ℝ) + 1) ^ ((3 : ℝ) / 4) := by positivity
          linarith
        have he := GE.proxy_env arms (t + 1) (R.cumEst arms t ω) (R.p t ω) jstar (hfeas ω) hpos hB
          hβpos
        have hsum : ∑ a ∈ Finset.univ.erase jstar, Real.exp (-((arms a - arms jstar) ⬝ᵥ
            R.cumEst arms t ω / (2 * beta d K (t + 1)))) ≤
            K * Real.exp (-(2 * ((t : ℝ) + 1) ^ ((1 : ℝ) / 4) / Cb)) := by
          calc _ ≤ ∑ a ∈ Finset.univ.erase jstar,
                Real.exp (-(2 * ((t : ℝ) + 1) ^ ((1 : ℝ) / 4) / Cb)) :=
                Finset.sum_le_sum fun a ha => GE.sep_exp hd hK t _ (hX a (Finset.ne_of_mem_erase ha))
            _ ≤ ∑ a : Fin K, Real.exp (-(2 * ((t : ℝ) + 1) ^ ((1 : ℝ) / 4) / Cb)) :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
                  (fun _ _ _ => (Real.exp_pos _).le)
            _ = K * Real.exp (-(2 * ((t : ℝ) + 1) ^ ((1 : ℝ) / 4) / Cb)) := by simp
        have hβle := GE.beta_le d K (t + 1) hK (by omega)
        push_cast at hβle
        refine he.trans ?_
        calc Real.exp 2 * beta d K (t + 1) * ∑ a ∈ Finset.univ.erase jstar,
              Real.exp (-((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω / (2 * beta d K (t + 1))))
            ≤ Real.exp 2 * (Cb * Real.sqrt ((t : ℝ) + 1)) *
                (K * Real.exp (-(2 * ((t : ℝ) + 1) ^ ((1 : ℝ) / 4) / Cb))) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left hβle (Real.exp_pos 2).le) hsum
                (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) (by positivity)
          _ = Real.exp 2 * Cb * K * env t := by simp only [env]; ring
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_mem (Set.mem_compl hω), zero_add]
        exact ((hfeas ω).2.2.2.2.2).trans (GE.two_d_div_beta d K t hK hd)
    have := GE.int_split P (G t) (hGm t) _ (Real.exp 2 * Cb * K * env t)
      (2 * cR d K / Real.sqrt ((t : ℝ) + 1)) (by simp only [env]; positivity) (by positivity) hpt
    calc _ ≤ Real.exp 2 * Cb * K * env t +
          2 * cR d K / Real.sqrt ((t : ℝ) + 1) * (P (G t)ᶜ).toReal := this
      _ = _ := by ring
  -- sum over rounds
  have hsumenv : ∑ t ∈ Finset.range T, env t ≤ S0 := GE.tail_sum Cb hCbpos T
  have hJX : Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C ≤
      allocCost arms θ jstar n * Real.log K * Real.log T +
        Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C := by
    have hcost : 0 ≤ allocCost arms θ jstar n := by
      unfold allocCost
      refine Finset.sum_nonneg fun j _ => mul_nonneg (hn.1 j) ?_
      by_cases hj : j = jstar
      · simp [hj]
      · have := huniq j hj
        rw [sub_dotProduct]; linarith
    have hlK := Real.log_nonneg (show (1 : ℝ) ≤ K by exact_mod_cast hK)
    have hlT := Real.log_nonneg (show (1 : ℝ) ≤ T by exact_mod_cast hT)
    have : 0 ≤ allocCost arms θ jstar n * Real.log K * Real.log T := by positivity
    linarith
  calc ∑ t ∈ Finset.range T, ∫ ω, proxyC arms (t + 1) (R.cumEst arms t ω) (R.p t ω) ∂P
      ≤ ∑ t ∈ Finset.range T, (Real.exp 2 * Cb * K * env t +
          2 * cR d K * ((P (G t)ᶜ).toReal / Real.sqrt ((t : ℝ) + 1))) :=
        Finset.sum_le_sum fun t ht => hround t (Finset.mem_range.mp ht)
    _ = Real.exp 2 * Cb * K * ∑ t ∈ Finset.range T, env t +
          2 * (cR d K * ∑ t ∈ Finset.range T, (P (G t)ᶜ).toReal / Real.sqrt ((t : ℝ) + 1)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
    _ ≤ Real.exp 2 * Cb * K * S0 + 2 * (cG * (Real.sqrt ((d : ℝ) * Real.log K) *
          Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) + MG) := by
        gcongr
    _ ≤ 2 * cG * (allocCost arms θ jstar n * Real.log K * Real.log T +
          Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) +
        (Real.exp 2 * Cb * K * S0 + 2 * |MG|) := by
        have := mul_le_mul_of_nonneg_left hJX hcG.le
        have := le_abs_self MG
        nlinarith
