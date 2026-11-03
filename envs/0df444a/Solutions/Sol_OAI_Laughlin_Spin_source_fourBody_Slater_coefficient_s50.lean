-- Prove2me | solution 1 for OAI.Laughlin.Spin.source_fourBody_Slater_coefficient_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:09:04.384584+00:00
-- url     : https://prove2.me/submissions/1dd911fd-5b3c-44d5-bb19-ca390449fd85

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L014
import Theorems.Thm_OAI_Laughlin_Spin_source_fourBody_factorial_coefficient_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RadicalCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem fourBodyRadical_factorial (r D T p j k : ℕ) (hr : r ≤ T) :
    fourBodyRadical r D T p j k =
      Real.sqrt 2 * (Real.sqrt (1/2))^(j+k+(T-r)) *
      sqrtFactorial j * sqrtFactorial k * sqrtFactorial p /
        (sqrtFactorial r * sqrtFactorial (D-r) * sqrtFactorial (T-D)) := by
  let m := j+k+(T-r)
  have hm : (1 : ℤ)-(j : ℤ)-k-T+r = 1-(m : ℤ) := by
    dsimp [m]
    simp only [Nat.cast_sub hr]
    omega
  have hp : (2 : ℝ)^((1 : ℤ)-(j : ℤ)-k-T+r) = 2*(1/2 : ℝ)^m := by
    rw [hm,zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0),zpow_one,zpow_natCast]
    simp [div_eq_mul_inv]
  let a := Real.sqrt 2 * (Real.sqrt (1/2))^m *
    sqrtFactorial j * sqrtFactorial k * sqrtFactorial p /
      (sqrtFactorial r * sqrtFactorial (D-r) * sqrtFactorial (T-D))
  have ha : 0 ≤ a := by dsimp [a]; unfold sqrtFactorial; positivity
  have hs : a^2 = (2 : ℝ)^((1 : ℤ)-(j : ℤ)-k-T+r) *
    ((j.factorial : ℝ)*(k.factorial : ℝ)*(p.factorial : ℝ) /
      ((r.factorial : ℝ)*((D-r).factorial : ℝ)*((T-D).factorial : ℝ))) := by
    rw [hp]
    dsimp [a]
    simp only [div_pow,mul_pow,sqrtFactorial]
    rw [show ((Real.sqrt (1/2))^m)^2 = (1/2 : ℝ)^m by
      rw [← pow_mul,mul_comm m 2,pow_mul,Real.sq_sqrt (by norm_num)]]
    simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),Real.sq_sqrt (Nat.cast_nonneg _)]
    ring_nf
    norm_num
  change Real.sqrt _ = a
  rw [← hs,Real.sqrt_sq ha]

theorem source_fourBody_radical_coefficient (r D T p j k : ℕ)
    (hrD : r ≤ D) (hDT : D ≤ T) (hT : p+j+k=T) :
    fourBodyLimitCoefficient r D T p j k =
      (Certificate.V r D T p j k : ℝ) * fourBodyRadical r D T p j k := by
  by_cases hr : r ≤ j+k
  · rw [source_fourBody_factorial_coefficient_s50 r D T p j k hrD hDT hT hr,
      fourBodyRadical_factorial r D T p j k (by omega)]
    ring
  · simp [fourBodyLimitCoefficient,Certificate.V,hr]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_SlaterRadical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem source_L_radical_cancellation (D r p x y j k : ℕ) (hor : Odd r)
    (hT : p+j+k=D) :
    Real.sqrt ((p.factorial : ℝ)/((2 : ℝ)^p*x.factorial*y.factorial)) * fourBodyRadical r D D p j k =
      Real.sqrt (sourceCopyWeight D r / ((x.factorial : ℝ)*y.factorial*j.factorial*k.factorial)) *
        (2 : ℝ)^(((1 : ℤ)-2*D+r)/2) *
        ((p.factorial : ℝ)*j.factorial*k.factorial) := by
  let e : ℤ := ((1 : ℤ)-2*D+r)/2
  have he : e*2=(1 : ℤ)-2*D+r := by
    rcases hor with ⟨a,ha⟩
    dsimp [e]; omega
  have hTr : (p : ℤ)+j+k=D := by exact_mod_cast hT
  have hpow : (2 : ℝ)^((1 : ℤ)-j-k-D+r) / (2 : ℝ)^p = ((2 : ℝ)^e)^2 := by
    rw [← zpow_natCast,← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (1 : ℤ)-j-k-D+r-(p : ℤ)=e*2 by omega,zpow_mul]
    norm_num
  have hsq : (Real.sqrt ((p.factorial : ℝ)/((2 : ℝ)^p*x.factorial*y.factorial)) *
      fourBodyRadical r D D p j k)^2 =
      (Real.sqrt (sourceCopyWeight D r / ((x.factorial : ℝ)*y.factorial*j.factorial*k.factorial)) *
        (2 : ℝ)^e * ((p.factorial : ℝ)*j.factorial*k.factorial))^2 := by
    simp only [fourBodyRadical,mul_pow]
    rw [Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by unfold sourceCopyWeight; positivity)]
    simp only [Nat.sub_self,Nat.factorial_zero,Nat.cast_one,mul_one]
    calc
      _ = ((2 : ℝ)^((1 : ℤ)-j-k-D+r)/(2 : ℝ)^p) *
        (((p.factorial : ℝ)*j.factorial*k.factorial)^2 /
          ((r.factorial : ℝ)*(D-r).factorial*x.factorial*y.factorial*j.factorial*k.factorial)) := by
        field_simp
      _ = ((2 : ℝ)^e)^2 *
        (((p.factorial : ℝ)*j.factorial*k.factorial)^2 /
          ((r.factorial : ℝ)*(D-r).factorial*x.factorial*y.factorial*j.factorial*k.factorial)) := by rw [hpow]
      _ = _ := by unfold sourceCopyWeight; field_simp
  have hl : 0 ≤ Real.sqrt ((p.factorial : ℝ)/((2 : ℝ)^p*x.factorial*y.factorial)) *
      fourBodyRadical r D D p j k := by unfold fourBodyRadical; positivity
  have hr : 0 ≤ Real.sqrt (sourceCopyWeight D r / ((x.factorial : ℝ)*y.factorial*j.factorial*k.factorial)) *
      (2 : ℝ)^e * ((p.factorial : ℝ)*j.factorial*k.factorial) := by positivity
  nlinarith only [hsq,hl,hr]

theorem limitSlaterTerm_rational (D r x y j k : ℕ) (hr : r ≤ D) (hor : Odd r)
    (hxy : x < y) (hT : x+y+j+k=D+1) :
    limitSlaterTerm D r x y j k =
      Real.sqrt (sourceCopyWeight D r / ((x.factorial : ℝ)*y.factorial*j.factorial*k.factorial)) *
        (2 : ℝ)^(((1 : ℤ)-2*D+r)/2) *
        ((x : ℝ)-y) * ((x+y-1).factorial : ℝ)*j.factorial*k.factorial *
        (Certificate.V r D D (x+y-1) j k : ℝ) := by
  have hp : x+y-1+j+k=D := by omega
  rw [limitSlaterTerm,source_fourBody_radical_coefficient r D D (x+y-1) j k hr (le_refl _) hp]
  rw [pairLimitCoefficient,ite_eq_left (by omega : x+y=x+y-1+1)]
  have hc := source_L_radical_cancellation D r (x+y-1) x y j k hor hp
  calc
    _ = ((x : ℝ)-y)*(Certificate.V r D D (x+y-1) j k : ℝ) *
      (Real.sqrt (((x+y-1).factorial : ℝ)/((2 : ℝ)^(x+y-1)*x.factorial*y.factorial)) *
        fourBodyRadical r D D (x+y-1) j k) := by
      simp only [Nat.cast_ofNat]
      field_simp
    _ = _ := by rw [hc]; ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_SlaterCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem source_fourBody_Slater_coefficient_s50_oai (D r a b c d : ℕ) (hr : r ≤ D) (hor : Odd r)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hT : a+b+c+d=D+1) :
    limitSlaterCoefficient D r a b c d =
      Real.sqrt (sourceCopyWeight D r / ((a.factorial : ℝ)*b.factorial*c.factorial*d.factorial)) *
        (Certificate.L D r (a,b,c,d) : ℝ) := by
  unfold limitSlaterCoefficient
  rw [limitSlaterTerm_rational D r a b c d hr hor hab hT,
    limitSlaterTerm_rational D r a c b d hr hor (by omega) (by omega),
    limitSlaterTerm_rational D r a d b c hr hor (by omega) (by omega),
    limitSlaterTerm_rational D r b c a d hr hor hbc (by omega),
    limitSlaterTerm_rational D r b d a c hr hor (by omega) (by omega),
    limitSlaterTerm_rational D r c d a b hr hor hcd (by omega)]
  have h1 : (a.factorial : ℝ)*c.factorial*b.factorial*d.factorial =
      (a.factorial : ℝ)*b.factorial*c.factorial*d.factorial := by ring
  have h2 : (a.factorial : ℝ)*d.factorial*b.factorial*c.factorial =
      (a.factorial : ℝ)*b.factorial*c.factorial*d.factorial := by ring
  have h3 : (b.factorial : ℝ)*c.factorial*a.factorial*d.factorial =
      (a.factorial : ℝ)*b.factorial*c.factorial*d.factorial := by ring
  have h4 : (b.factorial : ℝ)*d.factorial*a.factorial*c.factorial =
      (a.factorial : ℝ)*b.factorial*c.factorial*d.factorial := by ring
  have h5 : (c.factorial : ℝ)*d.factorial*a.factorial*b.factorial =
      (a.factorial : ℝ)*b.factorial*c.factorial*d.factorial := by ring
  rw [h1,h2,h3,h4,h5]
  simp only [Certificate.L]
  push_cast
  ring

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.source_fourBody_Slater_coefficient_s50_oai := @OAI.Laughlin.Spin.source_fourBody_Slater_coefficient_s50_oai
