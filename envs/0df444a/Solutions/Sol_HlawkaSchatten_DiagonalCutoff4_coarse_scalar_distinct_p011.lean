-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p011
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:19:07.978054+00:00
-- url     : https://prove2.me/submissions/d71cece5-cb7f-4b73-a2db-aadcb474fbbc

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff4

theorem rational_powers_le (a b c d m n : ℕ) (hb : 0 < b) (hd : 0 < d)
    (h : a^m*d^n ≤ c^n*b^m) :
    ((a : ℝ)/b)^m ≤ ((c : ℝ)/d)^n := by
  rw [div_pow,div_pow]
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  apply (div_le_div_iff₀ (pow_pos hb' m) (pow_pos hd' n)).mpr
  exact_mod_cast h

theorem rectangle_budgets {a lo hi c alpha pl ph : ℝ}
    (hl : lo^a ≤ pl) (hh : hi^a ≤ ph)
    (h00 : 1+2*pl ≤ (c+2*alpha*lo)^a)
    (h10 : 1+ph+pl ≤ (c+alpha*(hi+lo))^a)
    (h11 : 1+2*ph ≤ (c+2*alpha*hi)^a) :
    1+2*lo^a ≤ (c+2*alpha*lo)^a ∧
    1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a ∧
    1+2*hi^a ≤ (c+2*alpha*hi)^a := by
  constructor
  · linarith only [hl,h00]
  constructor
  · linarith only [hl,hh,h10]
  · linarith only [hh,h11]

theorem sum_two_bounds {x y X Y z : ℝ} (hx : x ≤ X) (hy : y ≤ Y)
    (hz : X+2*Y ≤ z) : x+2*y ≤ z := by
  linarith only [hx,hy,hz]

theorem three_bounds {x X : ℝ} (hx : x ≤ X) (hX : 3*X ≤ 1) : x+x+x ≤ 1 := by
  linarith only [hx,hX]

end HlawkaSchatten.DiagonalCutoff4
namespace HlawkaSchatten.DiagonalRealBundle
theorem le_rpow_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (m k : ℕ) (hk : 0 < k)
    (h : X ^ k ≤ x ^ m) : X ≤ x ^ ((m : ℝ) / k) := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (Real.rpow_nonneg hx _)
  · have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
    rw [e]
    calc X = (X ^ k) ^ ((k : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hX.le hk.ne').symm
      _ ≤ (x ^ m) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)
theorem rpow_le_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X) (m k : ℕ) (hk : 0 < k)
    (h : x ^ m ≤ X ^ k) : x ^ ((m : ℝ) / k) ≤ X := by
  have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  rw [e]
  calc (x ^ m) ^ ((k : ℝ)⁻¹) ≤ (X ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = X := Real.pow_rpow_inv_natCast hX hk.ne'
end HlawkaSchatten.DiagonalRealBundle
/- Bernoulli envelope transport, generalized from accepted submission 6ad9b901-e3db-45c8-84cd-c4345b3b35df (Yuxuan Xu, Apache-2.0) to real lower endpoints. -/
open HlawkaSchatten.DiagonalConstruction
set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff16Scalar
theorem bernoulli_scale (m : ℝ) (hm : 1 ≤ m) {p d : ℝ}
    (hp : m ≤ p) (hd : 0 ≤ d) (hdm : d < m) :
    (1-d/m)^m ≤ (1-d/p)^p := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hp0 : 0 < p := hm0.trans_le hp
  have hbase : 0 ≤ 1-d/p := by
    apply sub_nonneg.mpr
    exact (div_le_one hp0).mpr (by linarith)
  have he : (1 : ℝ) ≤ p/m := (le_div_iff₀ hm0).mpr (by simpa using hp)
  have hs : -1 ≤ -d/p := by
    have h := (div_le_one hp0).mpr (show d ≤ p by linarith)
    simpa only [neg_div] using neg_le_neg h
  have hb := one_add_mul_self_le_rpow_one_add hs he
  have hroot : 1-d/m ≤ (1-d/p)^(p/m) := by
    convert hb using 1 <;> field_simp <;> ring
  calc
    _ ≤ ((1-d/p)^(p/m))^m := Real.rpow_le_rpow
      (by apply sub_nonneg.mpr; exact (div_le_one hm0).mpr hdm.le) hroot hm0.le
    _ = (1-d/p)^p := by
      rw [← Real.rpow_mul hbase]
      congr 1
      field_simp

theorem envelope_linear_of_certificate (m : ℝ) (hm : 1 ≤ m)
    {p q c : ℝ} (hp : m ≤ p) (hq : 0 ≤ q) (hq1 : q < 1) (hc : 0 < c)
    (hdm : (1-q)/(2*c) < m)
    (hcert : (1+q^m)/2 < (1-((1-q)/(2*c))/m)^m) :
    scalarEnvelope p q < c*p := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hp0 : 0 < p := hm0.trans_le hp
  set d := (1-q)/(2*c) with hd_def
  have hd : 0 ≤ d := div_nonneg (by linarith) (by positivity)
  have hscale := bernoulli_scale m hm hp hd hdm
  have hqpow : q^p ≤ q^m := by
    exact Real.rpow_le_rpow_of_exponent_ge' hq hq1.le (by positivity) hp
  have hg0 : 0 ≤ scalarEnvelopeRoot p q := Real.rpow_nonneg (by positivity) _
  have hgpow : scalarEnvelopeRoot p q ^ p = (1+q^p)/2 := by
    unfold scalarEnvelopeRoot
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hp0.ne', Real.rpow_one]
  have hb0 : 0 ≤ 1-d/p := by
    apply sub_nonneg.mpr
    exact (div_le_one hp0).mpr (by linarith)
  have hpow : scalarEnvelopeRoot p q ^ p < (1-d/p)^p := by
    rw [hgpow]
    exact (show (1+q^p)/2 < (1-d/m)^m by linarith).trans_le hscale
  have hg : scalarEnvelopeRoot p q < 1-d/p :=
    (Real.rpow_lt_rpow_iff hg0 hb0 hp0).mp hpow
  have hgap : 0 < 2*(1-scalarEnvelopeRoot p q) := by
    have := div_nonneg hd hp0.le
    linarith
  have hdp : d < p*(1-scalarEnvelopeRoot p q) := by
    have ht : d/p < 1-scalarEnvelopeRoot p q := by linarith
    have hm := (div_lt_iff₀ hp0).mp ht
    simpa only [mul_comm] using hm
  have hmul := mul_lt_mul_of_pos_left hdp (show 0 < 2*c by positivity)
  have heq : 2*c*d = 1-q := by rw [hd_def]; field_simp
  unfold scalarEnvelope
  apply (div_lt_iff₀ hgap).mpr
  nlinarith

end HlawkaSchatten.DiagonalCutoff16Scalar
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_scalar_distinct_p011 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) :
    scalarEnvelope p (29943/50000 : ℝ) < (81174/221875 : ℝ)*p ∧ (19517/25000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by
  have hqpow : (29943/50000 : ℝ) ^ (71/16 : ℝ) ≤ (2569336898735499991/25000000000000000000 : ℝ) := by
    have hpowers : (29943/50000 : ℝ)^71 ≤ (2569336898735499991/25000000000000000000 : ℝ)^16 := by
      have hnat : (29943 : ℕ)^71*25000000000000000000^16 ≤ 2569336898735499991^16*50000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29943 50000 2569336898735499991 25000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29943/50000 : ℝ)) (X := (2569336898735499991/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have hbase : (27850727753704166833/50000000000000000000 : ℝ) ≤ (142291/162348 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (27850727753704166833/50000000000000000000 : ℝ)^16 ≤ (142291/162348 : ℝ)^71 := by
      have hnat : (27850727753704166833 : ℕ)^16*162348^71 ≤ 142291^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27850727753704166833 50000000000000000000 142291 162348 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (142291/162348 : ℝ)) (X := (27850727753704166833/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have hroot : (3 : ℝ) ^ (16/71 : ℝ) ≤ (25000/19517 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (25000/19517 : ℝ)^71 := by
      have hnat : (3 : ℕ)^16*19517^71 ≤ 25000^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 25000 19517 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3 : ℝ)) (X := (25000/19517 : ℝ)) (by norm_num) (by norm_num) 16 71 (by norm_num) hpowers
    exact h
  constructor
  · apply HlawkaSchatten.DiagonalCutoff16Scalar.envelope_linear_of_certificate (71/16 : ℝ)
      (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [show (1-(1-(29943/50000 : ℝ))/(2*(81174/221875 : ℝ))/(71/16 : ℝ))=(142291/162348 : ℝ) by norm_num]
    have hh : (1+(29943/50000 : ℝ)^(71/16 : ℝ))/2 < (27850727753704166833/50000000000000000000 : ℝ) := by
      have hmargin : (1+(2569336898735499991/25000000000000000000 : ℝ))/2 < (27850727753704166833/50000000000000000000 : ℝ) := by norm_num
      linarith only [hqpow,hmargin]
    exact hh.trans_le hbase
  · have hm := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
      (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < (71/16 : ℝ)) hpa)
    rw [show (1:ℝ)/(71/16 : ℝ)=(16/71 : ℝ) by norm_num] at hm
    nlinarith only [hm,hroot]
end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) :
    scalarEnvelope p (29943/50000 : ℝ) < (81174/221875 : ℝ)*p ∧ (19517/25000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p011 p hpa

#print axioms solution
