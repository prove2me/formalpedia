-- Prove2me | solution 1 for OAI.Laughlin.Spin.oscillatorArray_polynomial_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T12:41:09.77884+00:00
-- url     : https://prove2.me/submissions/cc760fdc-798f-4322-9ff2-47d574b4d258

import Mathlib
import Definitions.Def_OAIQ050L004
import Definitions.Def_OAIQ050L006
import Definitions.Def_OAIQ050L008

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Polynomial_OscillatorPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators
open Polynomial

theorem sqrtFactorial_pos (n : ℕ) : 0 < sqrtFactorial n := by
  apply Real.sqrt_pos.mpr
  exact_mod_cast Nat.factorial_pos n

theorem sqrtFactorial_succ (n : ℕ) :
    sqrtFactorial (n+1) = Real.sqrt ((n : ℝ)+1) * sqrtFactorial n := by
  unfold sqrtFactorial
  rw [Nat.factorial_succ,Nat.cast_mul,Real.sqrt_mul (by positivity)]
  push_cast; rfl

theorem sqrt_choose_factorial (z p : ℕ) (hp : p ≤ z) :
    (z.choose p : ℝ) * monomialNormFactor z p / sqrtFactorial z =
      Real.sqrt (z.choose p : ℝ) := by
  have he : (z.choose p : ℝ) * (p.factorial : ℝ) * ((z-p).factorial : ℝ) = (z.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hp
  have hc : 0 < (z.choose p : ℝ) := by exact_mod_cast Nat.choose_pos hp
  have hs : sqrtFactorial z = Real.sqrt (z.choose p : ℝ) * monomialNormFactor z p := by
    unfold monomialNormFactor sqrtFactorial
    rw [← he,Real.sqrt_mul (by positivity),Real.sqrt_mul (by positivity)]
    ring
  have hn := ne_of_gt (sqrtFactorial_pos z)
  apply (div_eq_iff hn).mpr
  rw [hs]
  rw [← mul_assoc,← pow_two,Real.sq_sqrt (le_of_lt hc)]

theorem couplingPolynomial_base_coeff (u v : ℝ) (hu : u ≠ 0) (z p : ℕ) :
    (couplingPolynomial u v z 0).coeff p =
      u^z * ((-v/u)^(z-p) * (z.choose p : ℝ)) := by
  have he : C u * X-C v = C u * (X+C (-v/u)) := by
    rw [mul_add,← C_mul]
    have hc : u*(-v/u) = -v := by field_simp
    rw [hc,C_neg]; ring
  simp only [couplingPolynomial,pow_zero,mul_one,he,mul_pow,← C_pow,coeff_C_mul,coeff_X_add_C_pow]

theorem couplingPolynomial_base_normalized (u v : ℝ) (hu : u ≠ 0) (z p : ℕ) (hp : p ≤ z) :
    couplingPolynomialCoefficient u v z 0 p = oscillatorHighest u v z p := by
  have hz : z=p+(z-p) := by omega
  have hupow : u^z = u^p*u^(z-p) := by rw [← pow_add,← hz]
  unfold couplingPolynomialCoefficient
  rw [couplingPolynomial_base_coeff u v hu]
  simp only [Nat.add_zero,sqrtFactorial,Nat.factorial_zero,Nat.cast_one,Real.sqrt_one,mul_one]
  change _ = (-1 : ℝ)^(z-p)*Real.sqrt (z.choose p : ℝ)*u^p*v^(z-p)
  have he : u^z*(-v/u)^(z-p) = (-1 : ℝ)^(z-p)*u^p*v^(z-p) := by
    rw [hupow,div_pow,neg_eq_neg_one_mul,mul_pow]
    field_simp
  calc
    _ = (u^z*(-v/u)^(z-p))*((z.choose p : ℝ)*monomialNormFactor z p / sqrtFactorial z) := by unfold sqrtFactorial; ring
    _ = _ := by rw [he,sqrt_choose_factorial z p hp]; ring

theorem couplingPolynomial_succ_coeff (u v : ℝ) (z n p : ℕ) :
    (couplingPolynomial u v z (n+1)).coeff p =
      (if p=0 then 0 else v*(couplingPolynomial u v z n).coeff (p-1)) +
        u*(couplingPolynomial u v z n).coeff p := by
  have he : couplingPolynomial u v z (n+1) =
      C v * (couplingPolynomial u v z n * X) + C u * couplingPolynomial u v z n := by
    unfold couplingPolynomial
    rw [pow_succ]
    ring
  rw [he,coeff_add,coeff_C_mul,coeff_C_mul]
  cases p with
  | zero => simp
  | succ p => simp [coeff_mul_X]

theorem couplingPolynomial_coeff_off (u v : ℝ) (hu : u ≠ 0) (z n p : ℕ) (hp : z+n < p) :
    (couplingPolynomial u v z n).coeff p = 0 := by
  induction n generalizing p with
  | zero => rw [couplingPolynomial_base_coeff u v hu,Nat.choose_eq_zero_of_lt (by omega)]; simp
  | succ n ih =>
    rw [couplingPolynomial_succ_coeff,ite_eq_right (by omega : p ≠ 0),ih (p-1) (by omega),ih p (by omega)]
    ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Polynomial_OscillatorPolynomialLadder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

 theorem monomialNormFactor_first (T p : ℕ) (hp : 0 < p) :
    monomialNormFactor (T+1) p = Real.sqrt (p : ℝ)*monomialNormFactor T (p-1) := by
  have he : sqrtFactorial p = Real.sqrt (p : ℝ)*sqrtFactorial (p-1) := by
    have hh := sqrtFactorial_succ (p-1)
    have hk : p-1+1=p := by omega
    have hc : ((p-1 : ℕ) : ℝ)+1=p := by exact_mod_cast hk
    rwa [hk,hc] at hh
  unfold monomialNormFactor
  rw [he,show T+1-p=T-(p-1) by omega]
  ring

 theorem monomialNormFactor_second (T p : ℕ) (hp : p ≤ T) :
    monomialNormFactor (T+1) p = Real.sqrt ((T+1-p : ℕ) : ℝ)*monomialNormFactor T p := by
  have hk : T+1-p=(T-p)+1 := by omega
  have hc : ((T-p : ℕ) : ℝ)+1=(T+1-p : ℕ) := by exact_mod_cast hk.symm
  have hf : sqrtFactorial (T+1-p) = Real.sqrt ((T+1-p : ℕ) : ℝ)*sqrtFactorial (T-p) := by
    calc
      _ = sqrtFactorial ((T-p)+1) := by rw [hk]
      _ = _ := by rw [sqrtFactorial_succ,hc]
  unfold monomialNormFactor
  rw [hf]; ring

theorem couplingPolynomialCoefficient_lowering (u v : ℝ) (hu : u ≠ 0)
    (z n p : ℕ) (hp : p ≤ z+n+1) :
    couplingPolynomialCoefficient u v z (n+1) p =
      ((if p=0 then 0 else v*Real.sqrt (p : ℝ)*couplingPolynomialCoefficient u v z n (p-1)) +
       (if p ≤ z+n then u*Real.sqrt ((z+n+1-p : ℕ) : ℝ)*couplingPolynomialCoefficient u v z n p else 0)) /
         Real.sqrt ((n : ℝ)+1) := by
  unfold couplingPolynomialCoefficient
  rw [couplingPolynomial_succ_coeff,sqrtFactorial_succ]
  have ht : z+(n+1)=z+n+1 := by omega
  rw [ht]
  by_cases hp0 : p=0
  · subst p
    simp only [ite_eq_left (by omega : 0 ≤ z+n)]
    rw [monomialNormFactor_second (z+n) 0 (by omega)]
    simp only [Nat.sub_zero]
    simp [div_eq_mul_inv,mul_inv_rev]; ring
  · simp only [ite_eq_right hp0]
    by_cases hpn : p ≤ z+n
    · simp only [ite_eq_left hpn]
      have hfirst := monomialNormFactor_first (z+n) p (by omega)
      have hsecond := monomialNormFactor_second (z+n) p hpn
      rw [add_mul]
      simp only [add_div]
      congr 1
      · rw [hfirst]
        simp only [div_eq_mul_inv,mul_inv_rev]; ring
      · rw [hsecond]
        simp only [div_eq_mul_inv,mul_inv_rev]; ring
    · simp only [ite_eq_right hpn]
      rw [couplingPolynomial_coeff_off u v hu z n p (by omega),mul_zero,add_zero,
        monomialNormFactor_first (z+n) p (by omega)]
      simp only [div_eq_mul_inv,mul_inv_rev]; ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem oscillatorArray_polynomial_s50_oai (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (z n p : ℕ) (hp : p ≤ z+n) :
    oscillatorArray b z n p =
      couplingPolynomialCoefficient (Real.sqrt b) (Real.sqrt (1-b)) z n p := by
  have hu : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hb0)
  induction n generalizing p with
  | zero => exact (couplingPolynomial_base_normalized _ _ hu z p (by omega)).symm
  | succ n ih =>
    have hf (c : ℝ) (hc : 0 ≤ c) (k : ℕ) :
        Real.sqrt ((((k : ℝ)+1)*c)/((n : ℝ)+1)) =
          Real.sqrt c * Real.sqrt ((k : ℝ)+1) / Real.sqrt ((n : ℝ)+1) := by
      rw [Real.sqrt_div (by positivity),Real.sqrt_mul (by positivity)]
      ring
    have hfirst :
        (if p=0 then 0 else Real.sqrt ((((p-1 : ℕ)+1 : ℝ)*(1-b))/((n : ℝ)+1))*oscillatorArray b z n (p-1)) =
        (if p=0 then 0 else Real.sqrt (1-b)*Real.sqrt (p : ℝ)*
          couplingPolynomialCoefficient (Real.sqrt b) (Real.sqrt (1-b)) z n (p-1)) / Real.sqrt ((n : ℝ)+1) := by
      by_cases hp0 : p=0
      · simp only [hp0,ite_true,zero_div]
      · simp only [hp0,ite_false]
        have hk : ((p-1 : ℕ) : ℝ)+1=p := by exact_mod_cast (show p-1+1=p by omega)
        rw [ih (p-1) (by omega),hf (1-b) (by linarith),hk]
        ring
    have hsecond :
        (if p ≤ z+n then Real.sqrt ((((z+n-p : ℕ)+1 : ℝ)*b)/((n : ℝ)+1))*oscillatorArray b z n p else 0) =
        (if p ≤ z+n then Real.sqrt b*Real.sqrt ((z+n+1-p : ℕ) : ℝ)*
          couplingPolynomialCoefficient (Real.sqrt b) (Real.sqrt (1-b)) z n p else 0) / Real.sqrt ((n : ℝ)+1) := by
      by_cases hpn : p ≤ z+n
      · simp only [hpn,ite_true]
        have hk : ((z+n-p : ℕ) : ℝ)+1=(z+n+1-p : ℕ) := by
          exact_mod_cast (show z+n-p+1=z+n+1-p by omega)
        rw [ih p hpn,hf b (le_of_lt hb0),hk]
        ring
      · simp only [hpn,ite_false,zero_div]
    rw [oscillatorArray,couplingPolynomialCoefficient_lowering _ _ hu z n p (by omega),hfirst,hsecond,← add_div]

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.oscillatorArray_polynomial_s50_oai := @OAI.Laughlin.Spin.oscillatorArray_polynomial_s50_oai
