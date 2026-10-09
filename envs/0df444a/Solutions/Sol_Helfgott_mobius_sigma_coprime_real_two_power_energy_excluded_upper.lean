-- Prove2me | solution 1 for Helfgott.mobius_sigma_coprime_real_two_power_energy_excluded_upper
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T05:21:55.06823+00:00
-- url     : https://prove2.me/submissions/54c2df6a-5b94-4559-9355-b99714081a65

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Theorems.Thm_Helfgott_mobius_sigma_coprime_real_two_power_rankin_upper
import Theorems.Thm_Helfgott_rankin_sharp_coprime_coupled_weight_excluded_upper
import Mathlib.Algebra.Order.Floor.Semifield

section
set_option autoImplicit false
set_option Elab.async false
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott
noncomputable def excluded_energy_reuse_tp_rankinSingleZetaConstant (s : ℝ) : ℝ :=
  ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/
    (∑' n : ℕ,(n : ℝ)^(-3 : ℝ))

noncomputable def excluded_energy_reuse_tp_rankinCoupledZetaConstant (s t : ℝ) : ℝ :=
  ((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
    ((∑' n : ℕ,(n : ℝ)^(-3 : ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4 : ℝ)))

noncomputable def excluded_energy_reuse_tp_rankinSharpCoprimeFactor (q : ℕ) (s : ℝ) : ℝ :=
  ∏ p ∈ q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-s))

lemma excluded_energy_reuse_tp_rankin_single_zeta_constant_nonneg (s : ℝ) : 0 ≤ excluded_energy_reuse_tp_rankinSingleZetaConstant s := by
  unfold excluded_energy_reuse_tp_rankinSingleZetaConstant
  exact div_nonneg (mul_nonneg
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)))
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))

lemma excluded_energy_reuse_tp_rankin_sharp_factor_pos (q : ℕ) (s : ℝ) (hs : 0 < s) :
    0 < excluded_energy_reuse_tp_rankinSharpCoprimeFactor q s := by
  unfold excluded_energy_reuse_tp_rankinSharpCoprimeFactor
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have ht : (p : ℝ)^(-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hmul := mul_pos (by linarith : (0 : ℝ) < p) (by linarith : 0 < 1-(p : ℝ)^(-s))
  exact div_pos (by linarith) (by nlinarith)


noncomputable def excluded_energy_reuse_tp_rankinCoupledExcludedProduct (q : ℕ) (s t : ℝ) : ℝ :=
  ∏ p∈q.primeFactors, (1+(p : ℝ)^(-s-t)/
    ((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ))))

lemma excluded_energy_reuse_tp_rankin_coupled_excluded_product_pos (q : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    0 < excluded_energy_reuse_tp_rankinCoupledExcludedProduct q s t := by
  unfold excluded_energy_reuse_tp_rankinCoupledExcludedProduct
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hsp : (p : ℝ)^(-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have htp : (p : ℝ)^(-t) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hpInv : 0 < (p : ℝ)^(-1 : ℝ) := Real.rpow_pos_of_pos hp0 _
  have hden : 0 < (1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ)) :=
    mul_pos (by linarith) (by linarith)
  have hquo : 0 ≤ (p : ℝ)^(-s-t)/
    ((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ))) :=
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) hden.le
  linarith

noncomputable def excluded_energy_reuse_tp_rankinCoprimeCoupledZetaConstant (q : ℕ) (s t : ℝ) : ℝ :=
  excluded_energy_reuse_tp_rankinCoupledZetaConstant s t/excluded_energy_reuse_tp_rankinCoupledExcludedProduct q s t

noncomputable def excluded_energy_reuse_tp_rankinSharpCoupledOuter (q Y : ℕ) (s t : ℝ) : ℝ :=
  ∑ d∈Icc 1 Y, if Nat.Coprime d q then
    |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors, ((p : ℝ)+1))^2 *
      (d : ℝ)^(2-s-t)*excluded_energy_reuse_tp_rankinSharpCoprimeFactor (d*q) s*excluded_energy_reuse_tp_rankinSharpCoprimeFactor (d*q) t else 0

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott
lemma excluded_energy_reuse_tp_rankin_sharp_coupled_outer_excluded_upper (q Y : ℕ) (s t : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hst : 1 < s+t) :
    excluded_energy_reuse_tp_rankinSharpCoupledOuter q Y s t ≤
      excluded_energy_reuse_tp_rankinSharpCoprimeFactor q s*excluded_energy_reuse_tp_rankinSharpCoprimeFactor q t*excluded_energy_reuse_tp_rankinCoprimeCoupledZetaConstant q s t :=
  rankin_sharp_coprime_coupled_weight_excluded_upper q Y s t hs0 hs1 ht0 ht1 hst


theorem mobius_sigma_coprime_real_two_power_energy_excluded_upper_complete
    (q : ℕ) (X L T a b s t : ℝ)
    (hq : 1 ≤ q) (hX : 1 ≤ X) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs0 : 1/2 < s) (hs1 : s ≤ 1)
    (ht0 : 1/2 < t) (ht1 : t ≤ 1)
    (hM : ∀ z : ℝ, 1 ≤ z → z ≤ X →
      |∑ r∈Icc 1 ⌊z⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤
        a*(L/z)^(1-s)+b*(T/z)^(1-t)) :
    let R : ℝ → ℝ := fun u =>
      (((∑' n : ℕ,(n : ℝ)^(-u-1))*(∑' n : ℕ,(n : ℝ)^(-2*u-1)))/
        (∑' n : ℕ,(n : ℝ)^(-3 : ℝ))) *
        (∏ p∈q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-u)))
    let C : ℝ → ℝ → ℝ := fun u v =>
      ((∑' n : ℕ,(n : ℝ)^(-u-v))*(∑' n : ℕ,(n : ℝ)^(-u-2*v))*(∑' n : ℕ,(n : ℝ)^(-2*u-v)))/
        ((∑' n : ℕ,(n : ℝ)^(-3 : ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4 : ℝ))) /
          (∏ p∈q.primeFactors,(1+(p : ℝ)^(-u-v)/
            ((1-(p : ℝ)^(-u)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-v)+(p : ℝ)^(-1:ℝ)))))
    let P : ℝ := (L/X)^(1-s)
    let Z : ℝ := (T/X)^(1-t)
    (∑ d∈Icc 1 ⌊X⌋₊, if Nat.Coprime d q then
      |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors, ((p : ℝ)+1))^2 *
        (∑ r∈Icc 1 ⌊X/(d : ℝ)⌋₊, if Nat.Coprime r (d*q) then
          ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors, ((p : ℝ)+1)) else 0)^2 else 0) ≤
      a^2*P^2*(R s)^2*C s s + 2*a*b*P*Z*R s*R t*C s t + b^2*Z^2*(R t)^2*C t t := by
  let K := excluded_energy_reuse_tp_rankinSingleZetaConstant
  let J := excluded_energy_reuse_tp_rankinSharpCoprimeFactor
  let P := (L/X)^(1-s)
  let Z := (T/X)^(1-t)
  let Y := ⌊X⌋₊
  let w : ℕ → ℝ := fun d => |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2
  let f : ℕ → ℝ := fun d => ∑ r∈Icc 1 ⌊X/(d : ℝ)⌋₊, if Nat.Coprime r (d*q) then
    ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)) else 0
  let B : ℕ → ℝ := fun d => a*P*K s*(d : ℝ)^(1-s)*J (d*q) s +
    b*Z*K t*(d : ℝ)^(1-t)*J (d*q) t
  have hXp : 0 < X := by linarith
  have hs : 0 < s := by linarith
  have ht : 0 < t := by linarith
  have hKs : 0 ≤ K s := excluded_energy_reuse_tp_rankin_single_zeta_constant_nonneg s
  have hKt : 0 ≤ K t := excluded_energy_reuse_tp_rankin_single_zeta_constant_nonneg t
  have hP : 0 ≤ P := by positivity
  have hZ : 0 ≤ Z := by positivity
  have hw (d : ℕ) : 0 ≤ w d := by dsimp [w];positivity
  have hB (d : ℕ) : 0 ≤ B d := by
    have hJs := (excluded_energy_reuse_tp_rankin_sharp_factor_pos (d*q) s hs).le
    have hJt := (excluded_energy_reuse_tp_rankin_sharp_factor_pos (d*q) t ht).le
    dsimp only [B,J]
    positivity
  have hbound (d : ℕ) (hdI : d∈Icc 1 Y) : |f d| ≤ B d := by
    have hd : 1 ≤ d := (Finset.mem_Icc.mp hdI).1
    have hdp : (0 : ℝ) < d := by exact_mod_cast hd
    have hdX : (d : ℝ) ≤ X := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hdI).2)
      (Nat.floor_le hXp.le)
    have hin1 : 1 ≤ X/d := (le_div_iff₀ hdp).mpr (by simpa using hdX)
    have hinX : X/d ≤ X := (div_le_iff₀ hdp).mpr (by
      have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith)
    have hi := mobius_sigma_coprime_real_two_power_rankin_upper (d*q) (X/d) L T a b s t
      (by nlinarith) hin1 hL hT ha hb hs0.le hs1 ht0.le ht1
      (fun z hz hzx => hM z hz (hzx.trans hinX))
    change |f d| ≤ a*(L/(X/d))^(1-s)*(K s*J (d*q) s) +
      b*(T/(X/d))^(1-t)*(K t*J (d*q) t) at hi
    have hLP : (L/(X/d))^(1-s)=P*(d : ℝ)^(1-s) := by
      dsimp only [P]
      rw [show L/(X/d)=(L/X)*d by field_simp <;> ring, Real.mul_rpow (div_nonneg hL hXp.le) hdp.le]
    have hTZ : (T/(X/d))^(1-t)=Z*(d : ℝ)^(1-t) := by
      dsimp only [Z]
      rw [show T/(X/d)=(T/X)*d by field_simp <;> ring, Real.mul_rpow (div_nonneg hT hXp.le) hdp.le]
    apply hi.trans_eq
    rw [hLP,hTZ]
    dsimp only [B]
    ring
  dsimp only
  change (∑ d∈Icc 1 Y,if Nat.Coprime d q then w d*(f d)^2 else 0) ≤
    a^2*P^2*(K s*J q s)^2*excluded_energy_reuse_tp_rankinCoprimeCoupledZetaConstant q s s +
    2*a*b*P*Z*(K s*J q s)*(K t*J q t)*excluded_energy_reuse_tp_rankinCoprimeCoupledZetaConstant q s t +
    b^2*Z^2*(K t*J q t)^2*excluded_energy_reuse_tp_rankinCoprimeCoupledZetaConstant q t t
  have hsum : (∑ d∈Icc 1 Y,if Nat.Coprime d q then w d*(f d)^2 else 0) ≤
      ∑ d∈Icc 1 Y,if Nat.Coprime d q then w d*(B d)^2 else 0 := by
    apply Finset.sum_le_sum
    intro d hd
    by_cases hdq : Nat.Coprime d q
    · simp only [if_pos hdq]
      apply mul_le_mul_of_nonneg_left _ (hw d)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (f d)) (hB d)).mpr (hbound d hd)
    · simp only [if_neg hdq,le_refl]
  have hexpand : (∑ d∈Icc 1 Y,if Nat.Coprime d q then w d*(B d)^2 else 0) =
      a^2*P^2*(K s)^2*excluded_energy_reuse_tp_rankinSharpCoupledOuter q Y s s +
      2*a*b*P*Z*K s*K t*excluded_energy_reuse_tp_rankinSharpCoupledOuter q Y s t +
      b^2*Z^2*(K t)^2*excluded_energy_reuse_tp_rankinSharpCoupledOuter q Y t t := by
    unfold excluded_energy_reuse_tp_rankinSharpCoupledOuter
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdq : Nat.Coprime d q
    · simp only [if_pos hdq]
      have hdp : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      rw [show (2 : ℝ)-s-s=(1-s)*2 by ring,Real.rpow_mul hdp.le,Real.rpow_two,
        show (2 : ℝ)-s-t=(1-s)+(1-t) by ring,Real.rpow_add hdp,
        show (2 : ℝ)-t-t=(1-t)*2 by ring,Real.rpow_mul hdp.le,Real.rpow_two]
      dsimp [w,B,J]
      ring
    · simp only [if_neg hdq,mul_zero,add_zero]
  have hmss := excluded_energy_reuse_tp_rankin_sharp_coupled_outer_excluded_upper q Y s s hs0.le hs1 hs0.le hs1 (by linarith)
  have hmst := excluded_energy_reuse_tp_rankin_sharp_coupled_outer_excluded_upper q Y s t hs0.le hs1 ht0.le ht1 (by linarith)
  have hmtt := excluded_energy_reuse_tp_rankin_sharp_coupled_outer_excluded_upper q Y t t ht0.le ht1 ht0.le ht1 (by linarith)
  apply hsum.trans
  rw [hexpand]
  have hi := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hmss (by positivity : 0 ≤ a^2*P^2*(K s)^2))
    (mul_le_mul_of_nonneg_left hmst (by positivity : 0 ≤ 2*a*b*P*Z*K s*K t)))
    (mul_le_mul_of_nonneg_left hmtt (by positivity : 0 ≤ b^2*Z^2*(K t)^2))
  apply hi.trans_eq
  ring


end Helfgott
end

open Helfgott Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
theorem solution 
    (q : ℕ) (X L T a b s t : ℝ)
    (hq : 1 ≤ q) (hX : 1 ≤ X) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs0 : 1/2 < s) (hs1 : s ≤ 1)
    (ht0 : 1/2 < t) (ht1 : t ≤ 1)
    (hM : ∀ z : ℝ, 1 ≤ z → z ≤ X →
      |∑ r∈Icc 1 ⌊z⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤
        a*(L/z)^(1-s)+b*(T/z)^(1-t)) :
    let R : ℝ → ℝ := fun u =>
      (((∑' n : ℕ,(n : ℝ)^(-u-1))*(∑' n : ℕ,(n : ℝ)^(-2*u-1)))/
        (∑' n : ℕ,(n : ℝ)^(-3 : ℝ))) *
        (∏ p∈q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-u)))
    let C : ℝ → ℝ → ℝ := fun u v =>
      ((∑' n : ℕ,(n : ℝ)^(-u-v))*(∑' n : ℕ,(n : ℝ)^(-u-2*v))*(∑' n : ℕ,(n : ℝ)^(-2*u-v)))/
        ((∑' n : ℕ,(n : ℝ)^(-3 : ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4 : ℝ))) /
          (∏ p∈q.primeFactors,(1+(p : ℝ)^(-u-v)/
            ((1-(p : ℝ)^(-u)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-v)+(p : ℝ)^(-1:ℝ)))))
    let P : ℝ := (L/X)^(1-s)
    let Z : ℝ := (T/X)^(1-t)
    (∑ d∈Icc 1 ⌊X⌋₊, if Nat.Coprime d q then
      |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors, ((p : ℝ)+1))^2 *
        (∑ r∈Icc 1 ⌊X/(d : ℝ)⌋₊, if Nat.Coprime r (d*q) then
          ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors, ((p : ℝ)+1)) else 0)^2 else 0) ≤
      a^2*P^2*(R s)^2*C s s + 2*a*b*P*Z*R s*R t*C s t + b^2*Z^2*(R t)^2*C t t := Helfgott.mobius_sigma_coprime_real_two_power_energy_excluded_upper_complete q X L T a b s t hq hX hL hT ha hb hs0 hs1 ht0 ht1 hM
#print axioms solution
