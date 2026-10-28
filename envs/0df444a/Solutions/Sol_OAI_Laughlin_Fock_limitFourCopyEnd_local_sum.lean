-- Prove2me | solution 1 for OAI.Laughlin.Fock.limitFourCopyEnd_local_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:31:52.700703+00:00
-- url     : https://prove2.me/submissions/eb2460c4-d194-4f05-9ff0-4dc80d70df0b

import Mathlib
import Definitions.Def_OAIQ047L002
import Definitions.Def_OAIQ047L003

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_HighestSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem highestRaw_zero (A B z : ℕ) :
    highestRaw A B z 0 = 1 / Real.sqrt (B.choose z : ℝ) := by
  simp [highestRaw]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_RelativeHighest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem highestRaw_zero_pos (A B z : ℕ) (hB : z ≤ B) :
    0 < highestRaw A B z 0 := by
  rw [highestRaw_zero]
  apply one_div_pos.mpr
  apply Real.sqrt_pos.mpr
  exact_mod_cast Nat.choose_pos hB

theorem relativeHighest_zero (A B z : ℕ) (hB : z ≤ B) :
    relativeHighest A B z 0 = 1 := by
  exact div_self (ne_of_gt (highestRaw_zero_pos A B z hB))

theorem relativeHighest_succ (A B z p : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hp : p < z) :
    relativeHighest A B z (p+1) =
      -(ladder B (z-p-1)/ladder A p)*relativeHighest A B z p := by
  have he := highestRaw_raising A B z p hA hB hp
  have ha := ne_of_gt (ladder_pos A p (by omega))
  have hr := ne_of_gt (highestRaw_zero_pos A B z hB)
  unfold relativeHighest
  field_simp
  nlinarith only [he]

theorem highestNorm_relative (A B z : ℕ) (hB : z ≤ B) :
    highestNorm A B z = highestRaw A B z 0 * relativeHighestNorm A B z := by
  have hp := highestRaw_zero_pos A B z hB
  have he : (∑ p ∈ Finset.range (z+1), (highestRaw A B z p)^2) =
      (highestRaw A B z 0)^2 * ∑ p ∈ Finset.range (z+1), (relativeHighest A B z p)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp'
    unfold relativeHighest
    field_simp
  unfold highestNorm relativeHighestNorm
  rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (le_of_lt hp)]

theorem highestUnit_eq_relative (A B z p : ℕ) (hB : z ≤ B) :
    highestUnit A B z p = relativeHighest A B z p / relativeHighestNorm A B z := by
  unfold highestUnit relativeHighest
  rw [highestNorm_relative A B z hB]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_OscillatorHighest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem oscillatorRelative_zero (t : ℝ) (z : ℕ) :
    oscillatorRelative t z 0 = 1 := by simp [oscillatorRelative]

theorem sqrt_choose_ratio (z p : ℕ) (hp : p < z) :
    Real.sqrt (z.choose (p+1) : ℝ) =
      Real.sqrt ((z-p : ℕ)/(p+1 : ℝ)) * Real.sqrt (z.choose p : ℝ) := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  have he := choose_step_real z p (by omega)
  apply (mul_left_cancel₀ (show (p+1 : ℝ) ≠ 0 by positivity))
  field_simp
  nlinarith only [he]

theorem oscillatorRelative_succ (b : ℝ) (hb : 0 ≤ b) (z p : ℕ) (hp : p < z) :
    oscillatorRelative (Real.sqrt (b/(1-b))) z (p+1) =
      -Real.sqrt ((((z-p : ℕ) : ℝ)*b)/(((p : ℝ)+1)*(1-b))) *
        oscillatorRelative (Real.sqrt (b/(1-b))) z p := by
  have he : (((z-p : ℕ) : ℝ)*b)/(((p : ℝ)+1)*(1-b)) =
      ((z-p : ℕ)/(p+1 : ℝ))*(b/(1-b)) := by rw [mul_div_mul_comm]
  rw [he,Real.sqrt_mul (by positivity),Real.sqrt_div hb]
  unfold oscillatorRelative
  rw [sqrt_choose_ratio z p hp,pow_succ,pow_succ]
  ring

theorem oscillatorHighest_norm (u v : ℝ) (huv : u^2+v^2=1) (z : ℕ) :
    (∑ p ∈ Finset.range (z+1), (oscillatorHighest u v z p)^2) = 1 := by
  have hs := add_pow (u^2) (v^2) z
  rw [huv,one_pow] at hs
  apply Eq.trans ?_ hs.symm
  apply Finset.sum_congr rfl
  intro p hp
  unfold oscillatorHighest
  rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
  have hn : ((-1 : ℝ)^(z-p))^2 = 1 := by rw [← pow_mul,mul_comm _ 2,pow_mul]; norm_num
  rw [hn,one_mul]
  ring

theorem oscillatorHighest_relative (u v : ℝ) (hv : v ≠ 0) (z p : ℕ) (hp : p ≤ z) :
    (-1 : ℝ)^z * oscillatorRelative (u/v) z p * v^z = oscillatorHighest u v z p := by
  have hz : z=p+(z-p) := by omega
  have hsign : (-1 : ℝ)^z*(-1 : ℝ)^p = (-1 : ℝ)^(z-p) := by
    conv_lhs => arg 1; rw [hz,pow_add]
    have he : ((-1 : ℝ)^p)^2 = 1 := by rw [← pow_mul,mul_comm _ 2,pow_mul]; norm_num
    calc
      _ = ((-1 : ℝ)^p)^2 * (-1 : ℝ)^(z-p) := by ring
      _ = _ := by rw [he,one_mul]
  unfold oscillatorRelative oscillatorHighest
  calc
    _ = ((-1 : ℝ)^z*(-1 : ℝ)^p)*Real.sqrt (z.choose p : ℝ)*u^p*(v^z/v^p) := by rw [div_pow]; ring
    _ = _ := by
      have hpows : v^z = v^p*v^(z-p) := by rw [← pow_add,← hz]
      rw [hsign,hpows]; field_simp

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_OscillatorHighestNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem oscillatorRelativeNorm_pos (t : ℝ) (z : ℕ) : 0 < oscillatorRelativeNorm t z := by
  apply Real.sqrt_pos.mpr
  apply Finset.sum_pos'
  · intro p hp; exact sq_nonneg _
  · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
    rw [oscillatorRelative_zero]; norm_num

theorem oscillatorRelativeNorm_scale (u v : ℝ) (hv : 0 < v) (huv : u^2+v^2=1) (z : ℕ) :
    v^z * oscillatorRelativeNorm (u/v) z = 1 := by
  have hvz : 0 < v^z := pow_pos hv z
  have he : (v^z)^2 * ∑ p ∈ Finset.range (z+1), (oscillatorRelative (u/v) z p)^2 = 1 := by
    rw [Finset.mul_sum,← oscillatorHighest_norm u v huv z]
    apply Finset.sum_congr rfl
    intro p hp
    have hh := congrArg (fun x : ℝ => x^2)
      (oscillatorHighest_relative u v (ne_of_gt hv) z p (by have := Finset.mem_range.mp hp; omega))
    have hsign : ((-1 : ℝ)^z)^2 = 1 := by rw [← pow_mul,mul_comm _ 2,pow_mul]; norm_num
    simp only [mul_pow,hsign,one_mul] at hh
    nlinarith only [hh]
  have hs : (oscillatorRelativeNorm (u/v) z)^2 =
      ∑ p ∈ Finset.range (z+1), (oscillatorRelative (u/v) z p)^2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hn := oscillatorRelativeNorm_pos (u/v) z
  have hproduct : 0 < v^z*oscillatorRelativeNorm (u/v) z := mul_pos hvz hn
  rw [← hs] at he
  nlinarith only [he,hproduct]

theorem oscillatorHighest_from_relative (u v : ℝ) (hv : 0 < v) (huv : u^2+v^2=1)
    (z p : ℕ) (hp : p ≤ z) :
    (-1 : ℝ)^z * (oscillatorRelative (u/v) z p / oscillatorRelativeNorm (u/v) z) =
      oscillatorHighest u v z p := by
  have hs := oscillatorRelativeNorm_scale u v hv huv z
  have hn := ne_of_gt (oscillatorRelativeNorm_pos (u/v) z)
  have he := oscillatorHighest_relative u v (ne_of_gt hv) z p hp
  have hvz : v^z = 1 / oscillatorRelativeNorm (u/v) z := (eq_div_iff hn).mpr hs
  calc
    _ = (-1 : ℝ)^z * oscillatorRelative (u/v) z p * v^z := by rw [hvz]; ring
    _ = _ := he

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_ScaleLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem spin_fraction_sub_tendsto (B S : ℕ → ℕ) (b : ℝ)
    (hB : Tendsto B atTop atTop) (hS : Tendsto S atTop atTop)
    (hfrac : Tendsto (fun n => (B n : ℝ)/(S n : ℝ)) atTop (𝓝 b)) (k : ℕ) :
    Tendsto (fun n => ((B n-k : ℕ) : ℝ)/(S n : ℝ)) atTop (𝓝 b) := by
  have hi := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hS
  have ht := hfrac.sub (hi.const_mul (k : ℝ))
  have he : (fun n => (B n : ℝ)/(S n : ℝ)-(k : ℝ)*(S n : ℝ)⁻¹) =ᶠ[atTop]
      (fun n => ((B n-k : ℕ) : ℝ)/(S n : ℝ)) := by
    filter_upwards [hB.eventually (eventually_ge_atTop k)] with n hn
    rw [Nat.cast_sub hn]
    ring
  simpa using ht.congr' he

theorem first_spin_fraction_tendsto (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop)
    (hfrac : Tendsto (fun n => (B n : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 b)) :
    Tendsto (fun n => (A n : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 (1-b)) := by
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub hfrac
  apply ht.congr'
  filter_upwards [hA.eventually (eventually_ge_atTop 1)] with n hn
  have hp : (0 : ℝ) < (A n : ℝ)+B n := by
    have h : (0 : ℝ) < A n := by exact_mod_cast (show 0 < A n by omega)
    positivity
  field_simp
  ring

theorem ladder_ratio_tendsto (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    (hb : b < 1)
    (hfrac : Tendsto (fun n => (B n : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 b))
    (p k : ℕ) :
    Tendsto (fun n => ladder (B n) k / ladder (A n) p) atTop
      (𝓝 (Real.sqrt ((((k : ℝ)+1)*b)/(((p : ℝ)+1)*(1-b))))) := by
  have hS : Tendsto (fun n => A n+B n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right (A n) (B n)) hA
  have hb' : Tendsto (fun n => ((B n-k : ℕ) : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 b) := by
    simpa only [Nat.cast_add] using spin_fraction_sub_tendsto B (fun n => A n+B n) b hB hS
      (by simpa only [Nat.cast_add] using hfrac) k
  have ha' : Tendsto (fun n => ((A n-p : ℕ) : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 (1-b)) := by
    simpa only [Nat.cast_add] using spin_fraction_sub_tendsto A (fun n => A n+B n) (1-b) hA hS
      (by simpa only [Nat.cast_add] using first_spin_fraction_tendsto A B b hA hfrac) p
  have hnz : ((p : ℝ)+1)*(1-b) ≠ 0 := by positivity
  have ht := ((hb'.const_mul ((k : ℝ)+1)).div (ha'.const_mul ((p : ℝ)+1)) hnz).sqrt
  apply ht.congr'
  filter_upwards [hA.eventually (eventually_ge_atTop 1)] with n hn
  have hp : (0 : ℝ) < (A n : ℝ)+B n := by
    have h : (0 : ℝ) < A n := by exact_mod_cast (show 0 < A n by omega)
    positivity
  have he : (((k : ℝ)+1)*(((B n-k : ℕ) : ℝ)/((A n : ℝ)+B n))) /
      (((p : ℝ)+1)*(((A n-p : ℕ) : ℝ)/((A n : ℝ)+B n))) =
      (((k : ℝ)+1)*((B n-k : ℕ) : ℝ))/(((p : ℝ)+1)*((A n-p : ℕ) : ℝ)) := by
    field_simp
  simp only [Pi.div_apply]
  rw [he,Real.sqrt_div (by positivity)]
  rfl

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Asymptotics_HighestCouplingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Topology
open Filter

theorem relativeHighest_tendsto (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hfrac : Tendsto (fun n => (B n : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 b))
    (z p : ℕ) (hp : p ≤ z) :
    Tendsto (fun n => relativeHighest (A n) (B n) z p) atTop
      (𝓝 (oscillatorRelative (Real.sqrt (b/(1-b))) z p)) := by
  induction p with
  | zero =>
    rw [oscillatorRelative_zero]
    apply (tendsto_const_nhds (x := (1 : ℝ))).congr'
    filter_upwards [hB.eventually (eventually_ge_atTop z)] with n hn
    exact (relativeHighest_zero (A n) (B n) z hn).symm
  | succ p ih =>
    have hlt : p < z := by omega
    have hr := ladder_ratio_tendsto A B b hA hB hb1 hfrac p (z-p-1)
    have hk : ((z-p-1 : ℕ) : ℝ)+1 = (z-p : ℕ) := by
      exact_mod_cast (show z-p-1+1=z-p by omega)
    rw [hk] at hr
    have ht := hr.neg.mul (ih (by omega))
    rw [oscillatorRelative_succ b (le_of_lt hb0) z p hlt]
    apply ht.congr'
    filter_upwards [hA.eventually (eventually_ge_atTop z),hB.eventually (eventually_ge_atTop z)] with n hnA hnB
    exact (relativeHighest_succ (A n) (B n) z p hnA hnB hlt).symm

theorem relativeHighestNorm_tendsto (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hfrac : Tendsto (fun n => (B n : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 b)) (z : ℕ) :
    Tendsto (fun n => relativeHighestNorm (A n) (B n) z) atTop
      (𝓝 (oscillatorRelativeNorm (Real.sqrt (b/(1-b))) z)) := by
  apply Tendsto.sqrt
  apply tendsto_finsetSum
  intro p hp
  exact (relativeHighest_tendsto A B b hA hB hb0 hb1 hfrac z p
    (by have := Finset.mem_range.mp hp; omega)).pow 2

theorem source_highest_coupling_tendsto (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hfrac : Tendsto (fun n => (B n : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 b))
    (z p : ℕ) (hp : p ≤ z) :
    Tendsto (fun n => (-1 : ℝ)^z * highestUnit (A n) (B n) z p) atTop
      (𝓝 (oscillatorHighest (Real.sqrt b) (Real.sqrt (1-b)) z p)) := by
  have huvs : (Real.sqrt b)^2+(Real.sqrt (1-b))^2=1 := by
    rw [Real.sq_sqrt (le_of_lt hb0),Real.sq_sqrt (by linarith)]; ring
  have hv : 0 < Real.sqrt (1-b) := Real.sqrt_pos.mpr (by linarith)
  have ht := ((relativeHighest_tendsto A B b hA hB hb0 hb1 hfrac z p hp).div
    (relativeHighestNorm_tendsto A B b hA hB hb0 hb1 hfrac z)
    (ne_of_gt (oscillatorRelativeNorm_pos (Real.sqrt (b/(1-b))) z))).const_mul ((-1 : ℝ)^z)
  rw [Real.sqrt_div (le_of_lt hb0)] at ht
  rw [← oscillatorHighest_from_relative (Real.sqrt b) (Real.sqrt (1-b)) hv huvs z p hp]
  apply ht.congr'
  filter_upwards [hB.eventually (eventually_ge_atTop z)] with n hn
  simp only [Pi.div_apply]
  rw [highestUnit_eq_relative (A n) (B n) z p hn]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Polynomial_OscillatorPolynomial
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
-- module Solutions.OAIQ047_LA.Laughlin_Polynomial_OscillatorPolynomialLadder
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
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Array
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem couplingArray_physical (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hTA : z+n ≤ A) (hTB : z+n ≤ B) (i : SpinIndex A B) (hi : i.1.val+i.2.val=z+n) :
    (-1 : ℝ)^z * genericUnitDescendant A B z hA hB n i = couplingArray A B z n i.1.val := by
  induction n generalizing i with
  | zero =>
    rw [genericUnitDescendant_zero]
    let p : Fin (z+1) := ⟨i.1.val,by omega⟩
    have he : i = weightSliceIndex A B z hA hB p := by
      apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp [weightSliceIndex,p]; omega
    rw [he]
    change (-1 : ℝ)^z * extendWeightSlice A B z hA hB (fun q => highestUnit A B z q.val)
      (weightSliceIndex A B z hA hB p) = (-1 : ℝ)^z * highestUnit A B z p.val
    rw [extendWeightSlice_at]
  | succ n ih =>
    have hn : n < genericCoupledWeight A B z := by unfold genericCoupledWeight; omega
    have hnreal : (n : ℝ) < genericCoupledWeight A B z := by exact_mod_cast hn
    have hd : Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n)) ≠ 0 := by positivity
    have he := congrFun (genericUnitDescendant_lowering A B z n hA hB hn) i
    change (∑ j, totalRaise A B j i * genericUnitDescendant A B z hA hB n j) =
      Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n))*
        genericUnitDescendant A B z hA hB (n+1) i at he
    rw [totalRaise_transpose_apply,raiseMatrix_column,raiseMatrix_column] at he
    have h1 : (-1 : ℝ)^z *
        (if h : 0 < i.1.val then genericUnitDescendant A B z hA hB n (⟨i.1.val-1,by omega⟩,i.2) *
          ladder A (i.1.val-1) else 0) =
        (if i.1.val=0 then 0 else ladder A (i.1.val-1)*couplingArray A B z n (i.1.val-1)) := by
      by_cases hp : 0 < i.1.val
      · rw [dite_eq_left hp,ite_eq_right (by omega : i.1.val ≠ 0)]
        have hh := ih (by omega) (by omega) (⟨i.1.val-1,by omega⟩,i.2) (by dsimp; omega)
        dsimp at hh
        rw [← hh]; ring
      · rw [dite_eq_right hp,ite_eq_left (by omega : i.1.val=0),mul_zero]
    have h2 : (-1 : ℝ)^z *
        (if h : 0 < i.2.val then genericUnitDescendant A B z hA hB n (i.1,⟨i.2.val-1,by omega⟩) *
          ladder B (i.2.val-1) else 0) =
        (if i.1.val ≤ z+n then ladder B (z+n-i.1.val)*couplingArray A B z n i.1.val else 0) := by
      by_cases hp : 0 < i.2.val
      · rw [dite_eq_left hp,ite_eq_left (by omega : i.1.val ≤ z+n)]
        have hh := ih (by omega) (by omega) (i.1,⟨i.2.val-1,by omega⟩) (by dsimp; omega)
        dsimp at hh
        have hl : ladder B (i.2.val-1) = ladder B (z+n-i.1.val) := congrArg (ladder B) (by omega)
        rw [← hh,hl]; ring
      · rw [dite_eq_right hp,ite_eq_right (by omega : ¬ i.1.val ≤ z+n),mul_zero]
    change _ = (_ + _) / _
    apply (eq_div_iff hd).mpr
    linear_combination h1+h2-(-1 : ℝ)^z*he

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_LoweringLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem coupled_denominator_scale_tendsto (S : ℕ → ℕ) (hS : Tendsto S atTop atTop)
    (z n : ℕ) :
    Tendsto (fun j => ((((S j-2*z : ℕ) : ℝ)-(n : ℝ))/(S j : ℝ))) atTop (𝓝 1) := by
  have hself : Tendsto (fun j => (S j : ℝ)/(S j : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    apply (tendsto_const_nhds (x := (1 : ℝ))).congr'
    filter_upwards [hS.eventually (eventually_ge_atTop 1)] with j hj
    have hn : (S j : ℝ) ≠ 0 := by exact_mod_cast (show S j ≠ 0 by omega)
    rw [div_self hn]
  have ht := spin_fraction_sub_tendsto S S 1 hS hS hself (2*z+n)
  apply ht.congr'
  filter_upwards [hS.eventually (eventually_ge_atTop (2*z+n))] with j hj
  rw [Nat.cast_sub (by omega : 2*z+n ≤ S j),Nat.cast_sub (by omega : 2*z ≤ S j)]
  push_cast
  ring

theorem normalized_ladder_factor_tendsto (C S : ℕ → ℕ) (c : ℝ)
    (hC : Tendsto C atTop atTop) (hS : Tendsto S atTop atTop)
    (hc : Tendsto (fun j => (C j : ℝ)/(S j : ℝ)) atTop (𝓝 c)) (z n k : ℕ) :
    Tendsto (fun j => ladder (C j) k /
      Real.sqrt (((n : ℝ)+1)*(((S j-2*z : ℕ) : ℝ)-n))) atTop
      (𝓝 (Real.sqrt ((((k : ℝ)+1)*c)/((n : ℝ)+1)))) := by
  have hnum := (spin_fraction_sub_tendsto C S c hC hS hc k).const_mul ((k : ℝ)+1)
  have hden := (coupled_denominator_scale_tendsto S hS z n).const_mul ((n : ℝ)+1)
  have ht := (hnum.div hden (by positivity)).sqrt
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [hS.eventually (eventually_ge_atTop 1)] with j hj
  have hp : (S j : ℝ) ≠ 0 := by exact_mod_cast (show S j ≠ 0 by omega)
  simp only [Pi.div_apply]
  have he : (((k : ℝ)+1)*(((C j-k : ℕ) : ℝ)/(S j : ℝ))) /
      (((n : ℝ)+1)*((((S j-2*z : ℕ) : ℝ)-n)/(S j : ℝ))) =
      (((k : ℝ)+1)*((C j-k : ℕ) : ℝ)) /
        (((n : ℝ)+1)*(((S j-2*z : ℕ) : ℝ)-n)) := by field_simp
  rw [he,Real.sqrt_div (by positivity)]
  rfl

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_ArrayLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Topology
open Filter

theorem couplingArray_tendsto (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hfrac : Tendsto (fun j => (B j : ℝ)/((A j : ℝ)+B j)) atTop (𝓝 b))
    (z n p : ℕ) (hp : p ≤ z+n) :
    Tendsto (fun j => couplingArray (A j) (B j) z n p) atTop (𝓝 (oscillatorArray b z n p)) := by
  have hS : Tendsto (fun j => A j+B j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_add_right (A j) (B j)) hA
  induction n generalizing p with
  | zero =>
    exact source_highest_coupling_tendsto A B b hA hB hb0 hb1 hfrac z p (by omega)
  | succ n ih =>
    let d : ℕ → ℝ := fun j => Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight (A j) (B j) z : ℝ)-n))
    have hfirst : Tendsto (fun j => if p=0 then 0 else
        (ladder (A j) (p-1)/d j)*couplingArray (A j) (B j) z n (p-1)) atTop
        (𝓝 (if p=0 then 0 else Real.sqrt ((((p-1 : ℕ)+1 : ℝ)*(1-b))/((n : ℝ)+1))*
          oscillatorArray b z n (p-1))) := by
      by_cases hp0 : p=0
      · simp only [hp0,ite_true]; exact tendsto_const_nhds
      · simp only [hp0,ite_false]
        have hf := normalized_ladder_factor_tendsto A (fun j => A j+B j) (1-b) hA hS
          (by simpa only [Nat.cast_add] using first_spin_fraction_tendsto A B b hA hfrac) z n (p-1)
        exact hf.mul (ih (p-1) (by omega))
    have hsecond : Tendsto (fun j => if p ≤ z+n then
        (ladder (B j) (z+n-p)/d j)*couplingArray (A j) (B j) z n p else 0) atTop
        (𝓝 (if p ≤ z+n then Real.sqrt ((((z+n-p : ℕ)+1 : ℝ)*b)/((n : ℝ)+1))*
          oscillatorArray b z n p else 0)) := by
      by_cases hpn : p ≤ z+n
      · simp only [hpn,ite_true]
        have hf := normalized_ladder_factor_tendsto B (fun j => A j+B j) b hB hS
          (by simpa only [Nat.cast_add] using hfrac) z n (z+n-p)
        exact hf.mul (ih p hpn)
      · simp only [hpn,ite_false]; exact tendsto_const_nhds
    have ht := hfirst.add hsecond
    apply ht.congr'
    exact Filter.Eventually.of_forall (fun j => by
      change (if p=0 then 0 else (ladder (A j) (p-1)/d j)*couplingArray (A j) (B j) z n (p-1)) +
        (if p ≤ z+n then (ladder (B j) (z+n-p)/d j)*couplingArray (A j) (B j) z n p else 0) = _
      change _ = ((if p=0 then 0 else _) + (if p ≤ z+n then _ else 0))/d j
      split_ifs <;> ring)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem oscillatorArray_polynomial (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
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

theorem source_coupling_polynomial_tendsto (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hfrac : Tendsto (fun j => (B j : ℝ)/((A j : ℝ)+B j)) atTop (𝓝 b))
    (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    Tendsto (fun j => couplingArray (A j) (B j) z (T-z) p) atTop
      (𝓝 (couplingPolynomialCoefficient (Real.sqrt b) (Real.sqrt (1-b)) z (T-z) p)) := by
  rw [← oscillatorArray_polynomial b hb0 hb1 z (T-z) p (by omega)]
  exact couplingArray_tendsto A B b hA hB hb0 hb1 hfrac z (T-z) p (by omega)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_PhysicalCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem physicalCouplingCoefficient_eq_array (A B z T p : ℕ)
    (hz : z ≤ T) (hp : p ≤ T) (hA : T ≤ A) (hB : T ≤ B) :
    physicalCouplingCoefficient A B z T p = couplingArray A B z (T-z) p := by
  rw [physicalCouplingCoefficient,dite_eq_left ⟨hz,hp,hA,hB⟩]
  exact couplingArray_physical A B z (T-z) (by omega) (by omega) (by omega) (by omega)
    (⟨p,by omega⟩,⟨T-p,by omega⟩) (by dsimp; omega)

theorem source_physical_coupling_tendsto (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hfrac : Tendsto (fun j => (B j : ℝ)/((A j : ℝ)+B j)) atTop (𝓝 b))
    (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    Tendsto (fun j => physicalCouplingCoefficient (A j) (B j) z T p) atTop
      (𝓝 (couplingPolynomialCoefficient (Real.sqrt b) (Real.sqrt (1-b)) z (T-z) p)) := by
  apply (source_coupling_polynomial_tendsto A B b hA hB hb0 hb1 hfrac z T p hz hp).congr'
  filter_upwards [hA.eventually (eventually_ge_atTop T),hB.eventually (eventually_ge_atTop T)] with j hjA hjB
  exact (physicalCouplingCoefficient_eq_array (A j) (B j) z T p hz hp hjA hjB).symm

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_CAR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem annihilate_anticommute {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * annihilate j + annihilate j * annihilate i = 0 := by
  refine LinearMap.ext fun x => ?_
  change CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q))
      (CliffordAlgebra.contractLeft (LinearMap.proj j : Module.Dual ℂ (Orbital Q)) x) +
    CliffordAlgebra.contractLeft (LinearMap.proj j : Module.Dual ℂ (Orbital Q))
      (CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q)) x) = 0
  rw [CliffordAlgebra.contractLeft_comm]
  exact neg_add_cancel _

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Specializations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem affine_spin_tendsto (a c : ℕ) (ha : 0 < a) :
    Tendsto (fun Q : ℕ => a*Q-c) atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop (k+c)] with Q hQ
  have hm : Q ≤ a*Q := by
    simpa using Nat.mul_le_mul_right Q (show 1 ≤ a by omega)
  omega

theorem affine_spin_fraction_tendsto (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun Q : ℕ => ((b*Q-d : ℕ) : ℝ)/(((a*Q-c : ℕ) : ℝ)+((b*Q-d : ℕ) : ℝ)))
      atTop (𝓝 ((b : ℝ)/((a : ℝ)+b))) := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have ht : Tendsto (fun Q : ℕ => (-(d : ℝ)+(b : ℝ)*Q)/
      (-(c : ℝ)-(d : ℝ)+((a : ℝ)+b)*Q)) atTop (𝓝 ((b : ℝ)/((a : ℝ)+b))) :=
    tendsto_add_mul_div_add_mul_atTop_nhds (-(d : ℝ)) (-(c : ℝ)-(d : ℝ)) (b : ℝ) (by positivity)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (c+d)] with Q hQ
  have hmA : Q ≤ a*Q := by simpa using Nat.mul_le_mul_right Q (show 1 ≤ a by omega)
  have hmB : Q ≤ b*Q := by simpa using Nat.mul_le_mul_right Q (show 1 ≤ b by omega)
  rw [Nat.cast_sub (by omega : c ≤ a*Q),Nat.cast_sub (by omega : d ≤ b*Q)]
  push_cast
  congr 1 <;> ring

theorem source_fourBody_inner_coupling_tendsto (r T p : ℕ) (hr : r ≤ T) (hp : p ≤ T) :
    Tendsto (fun Q : ℕ => physicalCouplingCoefficient Q Q r T p) atTop
      (𝓝 (couplingPolynomialCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) r (T-r) p)) := by
  have hf : Tendsto (fun Q : ℕ => (Q : ℝ)/((Q : ℝ)+Q)) atTop (𝓝 (1/2 : ℝ)) := by
    have h := affine_spin_fraction_tendsto 1 1 0 0 (by omega) (by omega)
    norm_num at h ⊢
    exact h
  have hh := source_physical_coupling_tendsto (fun Q => Q) (fun Q => Q) (1/2) tendsto_id tendsto_id
    (by norm_num) (by norm_num) hf r T p hr hp
  norm_num at hh ⊢
  exact hh

theorem source_fourBody_outer_coupling_tendsto (r z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    Tendsto (fun Q : ℕ => physicalCouplingCoefficient (2*Q-2) (2*Q-2*r) z T p) atTop
      (𝓝 (couplingPolynomialCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) z (T-z) p)) := by
  have hf : Tendsto (fun Q : ℕ => ((2*Q-2*r : ℕ) : ℝ)/
      (((2*Q-2 : ℕ) : ℝ)+((2*Q-2*r : ℕ) : ℝ))) atTop (𝓝 (1/2 : ℝ)) := by
    have h := affine_spin_fraction_tendsto 2 2 2 (2*r) (by omega) (by omega)
    norm_num at h ⊢
    exact h
  have hh := source_physical_coupling_tendsto (fun Q => 2*Q-2) (fun Q => 2*Q-2*r) (1/2)
    (affine_spin_tendsto 2 2 (by omega)) (affine_spin_tendsto 2 (2*r) (by omega))
    (by norm_num) (by norm_num) hf z T p hz hp
  norm_num at hh ⊢
  exact hh

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_CoefficientLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem source_fourBody_coefficient_tendsto (r D T p j k : ℕ)
    (hrD : r ≤ D) (hDT : D ≤ T) (hT : p+j+k=T) :
    Tendsto (fun Q : ℕ => fourBodyCoefficient Q r D T p j k) atTop
      (𝓝 (fourBodyLimitCoefficient r D T p j k)) := by
  by_cases hr : r ≤ j+k
  · simp only [fourBodyCoefficient,fourBodyLimitCoefficient,ite_eq_left hr]
    have hI := source_fourBody_inner_coupling_tendsto r (j+k) j hr (by omega)
    have hO := source_fourBody_outer_coupling_tendsto r (D-r) (T-r) p (by omega) (by omega)
    have he : T-r-(D-r)=T-D := by omega
    rw [he] at hO
    exact (tendsto_const_nhds.mul hI).mul hO
  · simp only [fourBodyCoefficient,fourBodyLimitCoefficient,ite_eq_right hr]
    exact tendsto_const_nhds

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Parity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem physicalPairCoupling_antisymmetric (Q r j k : ℕ) (ho : Odd r) :
    physicalCouplingCoefficient Q Q r (j+k) k =
      -physicalCouplingCoefficient Q Q r (j+k) j := by
  by_cases h : r ≤ j+k ∧ j+k ≤ Q
  · have h1 : r ≤ j+k ∧ k ≤ j+k ∧ j+k ≤ Q ∧ j+k ≤ Q := by omega
    have h2 : r ≤ j+k ∧ j ≤ j+k ∧ j+k ≤ Q ∧ j+k ≤ Q := by omega
    rw [physicalCouplingCoefficient,dite_eq_left h1,physicalCouplingCoefficient,dite_eq_left h2]
    have hj : j+k-k=j := by omega
    have hk : j+k-j=k := by omega
    simp only [hj,hk]
    exact pairCoupledTensor_antisymmetric Q r (j+k-r) (by omega) ho
      ⟨j,by omega⟩ ⟨k,by omega⟩
  · have h1 : ¬(r ≤ j+k ∧ k ≤ j+k ∧ j+k ≤ Q ∧ j+k ≤ Q) := by omega
    have h2 : ¬(r ≤ j+k ∧ j ≤ j+k ∧ j+k ≤ Q ∧ j+k ≤ Q) := by omega
    simp only [physicalCouplingCoefficient,dite_eq_right h1,dite_eq_right h2,neg_zero]

theorem fourBodyCoefficient_antisymmetric (Q r D T p j k : ℕ) (ho : Odd r) :
    fourBodyCoefficient Q r D T p k j = -fourBodyCoefficient Q r D T p j k := by
  unfold fourBodyCoefficient
  rw [Nat.add_comm k j]
  by_cases hr : r ≤ j+k
  · rw [ite_eq_left hr,ite_eq_left hr,physicalPairCoupling_antisymmetric Q r j k ho]
    ring
  · rw [ite_eq_right hr,ite_eq_right hr,neg_zero]

theorem fourBodyLimitCoefficient_antisymmetric (r D T p j k : ℕ) (ho : Odd r)
    (hrD : r ≤ D) (hDT : D ≤ T) (hT : p+j+k=T) :
    fourBodyLimitCoefficient r D T p k j = -fourBodyLimitCoefficient r D T p j k := by
  apply tendsto_nhds_unique (source_fourBody_coefficient_tendsto r D T p k j hrD hDT (by omega))
  have h := (source_fourBody_coefficient_tendsto r D T p j k hrD hDT hT).neg
  apply h.congr
  intro Q
  exact (fourBodyCoefficient_antisymmetric Q r D T p j k ho).symm

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_SliceCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem limitSliceCoefficient_antisymmetric (r D p j k : ℕ) (hr : r ≤ D) (ho : Odd r) :
    limitSliceCoefficient r D p k j = -limitSliceCoefficient r D p j k := by
  unfold limitSliceCoefficient
  by_cases h : p+j+k=D
  · rw [ite_eq_left (by omega : p+k+j=D),ite_eq_left h,
      fourBodyLimitCoefficient_antisymmetric r D D p j k ho hr (le_refl _) h]
  · rw [ite_eq_right (by omega : p+k+j ≠ D),ite_eq_right h,neg_zero]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_LocalFourIndexEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem localFourIndex_sum {M : Type*} [AddCommMonoid M] (Q D : ℕ) (hDQ : D ≤ Q)
    (f : ℕ → Fin (Q+1) → Fin (Q+1) → M) :
    (∑ p : Fin (D+1), ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
      if p.val+j.val+k.val=D ∧ j<k then f p.val j k else 0) =
      ∑ b : LocalFourIndex D, f b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ := by
  classical
  let P := fun b : Fin (D+1) × Fin (Q+1) × Fin (Q+1) =>
    b.1.val+b.2.1.val+b.2.2.val=D ∧ b.2.1<b.2.2
  have he : (∑ b : Fin (D+1) × Fin (Q+1) × Fin (Q+1),
      if P b then f b.1.val b.2.1 b.2.2 else 0) =
      ∑ p : Fin (D+1), ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
        if p.val+j.val+k.val=D ∧ j<k then f p.val j k else 0 := by
    simp only [Fintype.sum_prod_type,P]
  rw [← he,← Finset.sum_filter,Finset.sum_subtype (p := P) _ (by simp)]
  exact (localFourIndexEquiv Q D hDQ).sum_comp
    (fun b => f b.val.1.val b.val.2.1 b.val.2.2) |>.symm

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_SymmetricPairSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

private theorem symmetric_pair_sum {I M : Type*} [Fintype I] [LinearOrder I]
    [AddCommGroup M] (F : I → I → M) (hF : ∀ i j, F j i=F i j) (h0 : ∀ i, F i i=0) :
    (∑ i, ∑ j, F i j) = (∑ i, ∑ j, if i < j then F i j else 0) +
      (∑ i, ∑ j, if i < j then F i j else 0) := by
  have he (i j : I) : F i j = (if i < j then F i j else 0) + (if j < i then F j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h,not_lt_of_gt h]
    · subst j; simp [h0]
    · simp [h,not_lt_of_gt h,hF]
  conv_lhs => arg 2; ext i; arg 2; ext j; rw [he i j]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : I => if j < i then F j i else 0)]

theorem limitFourEnd_swap (Q p : ℕ) (j k : Fin (Q+1)) (x : Space Q) :
    limitFourEnd Q p k j x = -limitFourEnd Q p j k x := by
  have h := LinearMap.congr_fun (annihilate_anticommute j k) (limitPairEnd Q p x)
  simpa only [limitFourEnd,Module.End.mul_apply,LinearMap.add_apply,LinearMap.zero_apply,
    add_eq_zero_iff_eq_neg] using h

theorem weightedFourEnd_ordered (Q p : ℕ) (S : ℕ → ℕ → ℝ)
    (hS : ∀ j k, S k j = -S j k) (x : Space Q) :
    weightedFourEnd Q p (fun j k => S j.val k.val) x = ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
      if j<k then (S j.val k.val : ℂ) • limitFourEnd Q p j k x else 0 := by
  let F := fun j k : Fin (Q+1) => ((S j.val k.val / 2 : ℝ) : ℂ) • limitFourEnd Q p j k x
  have hf : ∀ j k, F k j=F j k := by
    intro j k
    simp [F,hS j.val k.val,limitFourEnd_swap Q p j k x,neg_div]
  have h0 : ∀ j, F j j=0 := by
    intro j
    have hs := hS j.val j.val
    have hz : S j.val j.val=0 := by linarith
    simp [F,hz]
  have h := symmetric_pair_sum F hf h0
  simp only [weightedFourEnd,LinearMap.sum_apply,LinearMap.smul_apply]
  change (∑ j, ∑ k, F j k) = _
  rw [h,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j hj
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k hk
  split_ifs
  · simp only [F,← add_smul]
    congr 1
    push_cast
    ring
  · simp

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Asymptotics_LimitFourLocalSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem limitFourCopyEnd_local_sum_oai (Q r D : ℕ) (hDQ : D ≤ Q) (hr : r ≤ D) (hor : Odd r) (x : Space Q) :
    limitFourCopyEnd Q r D x = ∑ b : LocalFourIndex D,
      (fourBodyLimitCoefficient r D D b.val.1.val b.val.2.1.val b.val.2.2.val : ℂ) •
        limitFourEnd Q b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ x := by
  simp only [limitFourCopyEnd,LinearMap.sum_apply]
  simp_rw [weightedFourEnd_ordered Q _ _ (fun j k => limitSliceCoefficient_antisymmetric r D _ j k hr hor)]
  have he (p : ℕ) (j k : Fin (Q+1)) :
      (if j<k then (limitSliceCoefficient r D p j.val k.val : ℂ) • limitFourEnd Q p j k x else 0) =
      (if p+j.val+k.val=D ∧ j<k then
        (fourBodyLimitCoefficient r D D p j.val k.val : ℂ) • limitFourEnd Q p j k x else 0) := by
    by_cases hjk : j<k <;> by_cases ht : p+j.val+k.val=D <;> simp [limitSliceCoefficient,hjk,ht]
  simp_rw [he]
  rw [← Fin.sum_univ_eq_sum_range]
  exact localFourIndex_sum Q D hDQ
    (fun p j k => (fourBodyLimitCoefficient r D D p j.val k.val : ℂ) • limitFourEnd Q p j k x)

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.limitFourCopyEnd_local_sum_oai := @OAI.Laughlin.Fock.limitFourCopyEnd_local_sum_oai
