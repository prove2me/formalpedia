-- Prove2me | solution 1 for ITPIRPreproc.MatchVec.polynomial_parameter_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Jesko
-- created : 2026-11-13T17:23:05.880421+00:00
-- url     : https://prove2.me/submissions/905d2118-9908-4649-8ee3-1cda7e78672a

import Definitions.Def_ITPIRPreproc_MatchVec_PolynomialParameters
import Theorems.Thm_ITPIRPreproc_MatchVec_polynomial_matching_vectors
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000

open Finset

namespace ITPIRPreproc.MatchVec.PolynomialConstruction

theorem wordLength_spec (h : ℕ) : 2^h ≤ (wordLength h)^(wordLength h) := by
  unfold wordLength
  exact Nat.find_spec (p := fun ell : ℕ => 2^h ≤ ell^ell) _

theorem wordLength_min (h t : ℕ) (ht : 2^h ≤ t^t) : wordLength h ≤ t :=
  Nat.find_min' _ ht

theorem wordLength_ge_two (h : ℕ) (hh : 3 ≤ h) : 2 ≤ wordLength h := by
  have hs := wordLength_spec h
  have hp : 8 ≤ 2^h := by
    change 2^3 ≤ 2^h
    exact Nat.pow_le_pow_right (by norm_num) hh
  by_contra hn
  have hc : wordLength h = 0 ∨ wordLength h = 1 := by omega
  rcases hc with hc | hc <;> rw [hc] at hs <;> norm_num at hs <;> omega

theorem log_two_bounds : (1:ℝ)/2 ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < (2:ℝ)⁻¹)
  rw [Real.log_inv] at h2
  constructor <;> linarith

theorem wordLength_log_bound (h : ℕ) (hh : 3 ≤ h) :
    (wordLength h : ℝ) * Real.log h ≤ 3 * h := by
  have hr : (3:ℝ) ≤ h := by exact_mod_cast hh
  have hp : (0:ℝ) < h := by linarith
  have hlog : 0 < Real.log h := Real.log_pos (by linarith)
  have hlogh : Real.log h ≤ h := (Real.log_le_sub_one_of_pos hp).trans (by linarith)
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.2 hp
  have hsq := Real.sq_sqrt hp.le
  have hlgs : Real.log h ≤ 2 * Real.sqrt h := by
    have hl := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt hp.le] at hl
    linarith
  let t := Nat.ceil (2 * (h:ℝ) / Real.log h)
  have htlo : 2 * (h:ℝ) / Real.log h ≤ t := Nat.le_ceil _
  have hthi : (t:ℝ) < 2 * h / Real.log h + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hsle : Real.sqrt h ≤ t := by
    apply le_trans _ htlo
    apply (le_div_iff₀ hlog).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hlgs hs.le, hsq]
  have htpos : (0:ℝ) < t := lt_of_lt_of_le hs hsle
  have hlogt : Real.log h / 2 ≤ Real.log t := by
    have hc := Real.log_le_log hs hsle
    rwa [Real.log_sqrt hp.le] at hc
  have htw : 2^h ≤ t^t := by
    have hprod : (h:ℝ) ≤ t * Real.log t := by
      have hx := (div_le_iff₀ hlog).mp htlo
      have hy := mul_le_mul_of_nonneg_left hlogt htpos.le
      nlinarith only [hx, hy]
    have hreal : (2:ℝ)^h ≤ (t:ℝ)^t := by
      apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
      rw [Real.log_pow, Real.log_pow]
      calc
        (h:ℝ)*Real.log 2 ≤ h := by nlinarith only [log_two_bounds.2, hp]
        _ ≤ _ := hprod
    exact_mod_cast hreal
  have hmin : (wordLength h : ℝ) ≤ t := by exact_mod_cast wordLength_min h t htw
  have htupper : (t:ℝ) * Real.log h < 2*h + Real.log h := by
    have hx := mul_lt_mul_of_pos_right hthi hlog
    simpa [add_mul, div_mul_cancel₀ _ hlog.ne'] using hx
  have hm := mul_le_mul_of_nonneg_right hmin hlog.le
  linarith

theorem prime_power_bounds (p ell : ℕ) (hp : 1 < p) (hell : 1 ≤ ell) :
    Nat.sqrt ell + 1 ≤ p ^ primeExponent p ell ∧
      p ^ primeExponent p ell ≤ p * (Nat.sqrt ell + 1) := by
  have hx : 1 < Nat.sqrt ell + 1 := by
    have hs : 0 < Nat.sqrt ell := Nat.sqrt_pos.mpr (by omega)
    omega
  constructor
  · exact Nat.le_pow_clog hp _
  · have ht := Nat.pow_pred_clog_lt_self hp hx
    have he : 0 < primeExponent p ell := Nat.clog_pos hp hx
    have hid : p ^ primeExponent p ell = p * p ^ (Nat.clog p (Nat.sqrt ell + 1)).pred := by
      rw [← pow_succ']
      congr 1
      exact (Nat.succ_pred_eq_of_pos he).symm
    rw [hid]
    exact Nat.mul_le_mul_left p ht.le

theorem canonical_degree_bounds (ell : ℕ) (hell : 1 ≤ ell) :
    1 ≤ degree (primeExponent 2 ell) (primeExponent 3 ell) ∧
    ell < 2^(primeExponent 2 ell) * 3^(primeExponent 3 ell) ∧
    (degree (primeExponent 2 ell) (primeExponent 3 ell) + 1 : ℝ) ≤ 6 * Real.sqrt ell := by
  have h2 := prime_power_bounds 2 ell (by norm_num) hell
  have h3 := prime_power_bounds 3 ell (by norm_num) hell
  have hspos : 0 < Nat.sqrt ell := Nat.sqrt_pos.mpr (by omega)
  have hmax : 1 ≤ max (2^primeExponent 2 ell) (3^primeExponent 3 ell) := by omega
  have hk : degree (primeExponent 2 ell) (primeExponent 3 ell) + 1 =
      max (2^primeExponent 2 ell) (3^primeExponent 3 ell) := by dsimp [degree]; omega
  refine ⟨?_, ?_, ?_⟩
  · dsimp [degree]
    omega
  · exact lt_of_lt_of_le (Nat.lt_succ_sqrt ell) (Nat.mul_le_mul h2.1 h3.1)
  · have hmx : max (2^primeExponent 2 ell) (3^primeExponent 3 ell) ≤
        3 * (Nat.sqrt ell+1) := by omega
    have hr : ((degree (primeExponent 2 ell) (primeExponent 3 ell) + 1 : ℕ) : ℝ) ≤
        3 * ((Nat.sqrt ell:ℝ)+1) := by exact_mod_cast (hk ▸ hmx)
    have hsn := Real.nat_sqrt_le_real_sqrt (a := ell)
    have hsone : (1:ℝ) ≤ Real.sqrt ell := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by exact_mod_cast hell)
    push_cast at hr
    linarith

theorem dimension_bound (h ell k d : ℕ) (hh : 3 ≤ h) (hell : 1 ≤ ell)
    (hl : (ell:ℝ) * Real.log h ≤ 3*h)
    (hk : (k:ℝ)+1 ≤ 6 * Real.sqrt ell)
    (hd : d ≤ (k+1)*ell^(2*k)) :
    (d:ℝ) ≤ (2:ℝ)^(1000 * Real.sqrt ((h:ℝ) * Real.log h)) := by
  have hr : (3:ℝ) ≤ h := by exact_mod_cast hh
  have hep : (0:ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
  have he1 : (1:ℝ) ≤ ell := by exact_mod_cast hell
  have hhp : (0:ℝ) < h := by linarith
  have hlh : (1:ℝ)/2 ≤ Real.log h :=
    log_two_bounds.1.trans (Real.log_le_log (by norm_num) (by linarith))
  have hlogpos : 0 < Real.log h := by linarith
  have hlell : 0 ≤ Real.log ell := Real.log_nonneg he1
  have hes : 0 ≤ Real.sqrt ell := Real.sqrt_nonneg _
  have hts : 0 ≤ Real.sqrt ((h:ℝ)*Real.log h) := Real.sqrt_nonneg _
  have hel : (ell:ℝ) ≤ 6*h := by
    have hx := mul_le_mul_of_nonneg_left hlh hep.le
    nlinarith only [hl, hx]
  have hll : Real.log ell ≤ 13 * Real.log h := by
    have hx := Real.log_le_log hep hel
    rw [Real.log_mul (by norm_num : (6:ℝ) ≠ 0) hhp.ne'] at hx
    have hy := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<6)
    linarith
  have hsquare : (Real.sqrt ell * Real.log h)^2 ≤
      (2 * Real.sqrt ((h:ℝ)*Real.log h))^2 := by
    rw [mul_pow, Real.sq_sqrt hep.le, mul_pow, Real.sq_sqrt (by positivity)]
    have hx := mul_le_mul_of_nonneg_right hl hlogpos.le
    nlinarith only [hx]
  have hsbound : Real.sqrt ell * Real.log h ≤
      2 * Real.sqrt ((h:ℝ)*Real.log h) := by
    nlinarith only [hsquare, hes, hts, hlogpos]
  have hb : ((k:ℝ)+1)*(ell:ℝ)^(2*k) ≤
      (2:ℝ)^(1000*Real.sqrt ((h:ℝ)*Real.log h)) := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_rpow (by norm_num : (0:ℝ)<2)]
    push_cast
    have hlogk := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<(k:ℝ)+1)
    have hkk : (k:ℝ) ≤ 6 * Real.sqrt ell := by linarith
    have hx := mul_le_mul_of_nonneg_right hkk hlell
    have hy := mul_le_mul_of_nonneg_left hll hes
    have hz := mul_le_mul_of_nonneg_left hlh hes
    have hw := mul_le_mul_of_nonneg_left log_two_bounds.1 hts
    nlinarith only [hlogk, hk, hx, hy, hz, hw, hsbound, hts]
  have hreal : (d:ℝ) ≤ ((k:ℝ)+1)*(ell:ℝ)^(2*k) := by exact_mod_cast hd
  exact hreal.trans hb

theorem canonical_parameter_bound (h d : ℕ) (hh : 3 ≤ h)
    (coords : Fin d ≃ Coordinate (wordLength h) (degree (exponent2 h) (exponent3 h))) :
    1 ≤ degree (exponent2 h) (exponent3 h) ∧
    wordLength h < 2^(exponent2 h) * 3^(exponent3 h) ∧
    (d:ℝ) ≤ (2:ℝ)^(1000 * Real.sqrt ((h:ℝ)*Real.log h)) := by
  have hell : 1 ≤ wordLength h := le_trans (by norm_num) (wordLength_ge_two h hh)
  have hk := canonical_degree_bounds (wordLength h) hell
  refine ⟨hk.1, hk.2.1, ?_⟩
  apply dimension_bound h (wordLength h) (degree (exponent2 h) (exponent3 h)) d hh hell
    (wordLength_log_bound h hh) hk.2.2
  exact (polynomial_matching_vectors (wordLength h) (exponent2 h) (exponent3 h) 0 d
    hk.1 hk.2.1 Function.Embedding.ofIsEmpty coords).2.2 hell

end ITPIRPreproc.MatchVec.PolynomialConstruction

open ITPIRPreproc.MatchVec ITPIRPreproc.MatchVec.PolynomialConstruction
theorem solution (h d : ℕ) (hh : 3 ≤ h)
    (coords : Fin d ≃ Coordinate (wordLength h) (degree (exponent2 h) (exponent3 h))) :
    2^h ≤ (wordLength h)^(wordLength h) ∧
    1 ≤ degree (exponent2 h) (exponent3 h) ∧
    wordLength h < 2^(exponent2 h) * 3^(exponent3 h) ∧
    (d:ℝ) ≤ (2:ℝ)^(1000 * Real.sqrt ((h:ℝ)*Real.log h)) := by
  exact ⟨wordLength_spec h, canonical_parameter_bound h d hh coords⟩
