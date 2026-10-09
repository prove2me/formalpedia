-- Prove2me | solution 1 for Helfgott.actual_vaughan_odd_mobius_two_power_analytic_upper
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T05:35:38.214115+00:00
-- url     : https://prove2.me/submissions/77b52af0-9b4b-49b5-8912-60f9e910876f

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Theorems.Thm_Helfgott_actual_vaughan_odd_mobius_two_power_energy_upper
import Theorems.Thm_Helfgott_odd_floor_two_power_sum_upper

section
set_option autoImplicit false
set_option Elab.async false
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott
noncomputable def vaughan_two_power_tp_rankinSingleZetaConstant (s : ℝ) : ℝ :=
  ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/
    (∑' n : ℕ,(n : ℝ)^(-3 : ℝ))

noncomputable def vaughan_two_power_tp_rankinCoupledZetaConstant (s t : ℝ) : ℝ :=
  ((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
    ((∑' n : ℕ,(n : ℝ)^(-3 : ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4 : ℝ)))

noncomputable def vaughan_two_power_tp_rankinSharpCoprimeFactor (q : ℕ) (s : ℝ) : ℝ :=
  ∏ p ∈ q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-s))

lemma vaughan_two_power_tp_rankin_single_zeta_constant_nonneg (s : ℝ) : 0 ≤ vaughan_two_power_tp_rankinSingleZetaConstant s := by
  unfold vaughan_two_power_tp_rankinSingleZetaConstant
  exact div_nonneg (mul_nonneg
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)))
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))

lemma vaughan_two_power_tp_rankin_sharp_factor_pos (q : ℕ) (s : ℝ) (hs : 0 < s) :
    0 < vaughan_two_power_tp_rankinSharpCoprimeFactor q s := by
  unfold vaughan_two_power_tp_rankinSharpCoprimeFactor
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have ht : (p : ℝ)^(-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hmul := mul_pos (by linarith : (0 : ℝ) < p) (by linarith : 0 < 1-(p : ℝ)^(-s))
  exact div_pos (by linarith) (by nlinarith)


noncomputable def vaughan_two_power_tp_rankinCoupledExcludedProduct (q : ℕ) (s t : ℝ) : ℝ :=
  ∏ p∈q.primeFactors, (1+(p : ℝ)^(-s-t)/
    ((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ))))

lemma vaughan_two_power_tp_rankin_coupled_excluded_product_pos (q : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    0 < vaughan_two_power_tp_rankinCoupledExcludedProduct q s t := by
  unfold vaughan_two_power_tp_rankinCoupledExcludedProduct
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

noncomputable def vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant (q : ℕ) (s t : ℝ) : ℝ :=
  vaughan_two_power_tp_rankinCoupledZetaConstant s t/vaughan_two_power_tp_rankinCoupledExcludedProduct q s t

noncomputable def vaughan_two_power_tp_rankinSharpCoupledOuter (q Y : ℕ) (s t : ℝ) : ℝ :=
  ∑ d∈Icc 1 Y, if Nat.Coprime d q then
    |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors, ((p : ℝ)+1))^2 *
      (d : ℝ)^(2-s-t)*vaughan_two_power_tp_rankinSharpCoprimeFactor (d*q) s*vaughan_two_power_tp_rankinSharpCoprimeFactor (d*q) t else 0

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
open Finset Nat Real ArithmeticFunction MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott
noncomputable def vaughan_two_power_eval_twoPowerCoprimeEnergyPolynomial (q : ℕ) (a b s t P Z : ℝ) : ℝ :=
  a^2*P^2*(vaughan_two_power_tp_rankinSingleZetaConstant s*vaughan_two_power_tp_rankinSharpCoprimeFactor q s)^2*vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant q s s +
    2*a*b*P*Z*(vaughan_two_power_tp_rankinSingleZetaConstant s*vaughan_two_power_tp_rankinSharpCoprimeFactor q s)*
      (vaughan_two_power_tp_rankinSingleZetaConstant t*vaughan_two_power_tp_rankinSharpCoprimeFactor q t)*vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant q s t +
    b^2*Z^2*(vaughan_two_power_tp_rankinSingleZetaConstant t*vaughan_two_power_tp_rankinSharpCoprimeFactor q t)^2*vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant q t t

lemma vaughan_two_power_eval_two_power_coprime_constant_nonneg (q : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    0 ≤ vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant q s t := by
  unfold vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant
  apply div_nonneg _ (vaughan_two_power_tp_rankin_coupled_excluded_product_pos q s t hs ht).le
  unfold vaughan_two_power_tp_rankinCoupledZetaConstant
  exact div_nonneg (mul_nonneg (mul_nonneg
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)))
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)))
    (mul_nonneg (sq_nonneg _) (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)))




noncomputable def vaughan_two_power_eval_oddRankinPowerIntegralBound (Y : ℕ) (gamma : ℝ) : ℝ :=
  1+((Y : ℝ)^gamma-1)/(2*gamma)

lemma vaughan_two_power_eval_nonnegative_rpow_double (v gamma : ℝ) (hv : 0 ≤ v) :
    v^(2*gamma)=(v^gamma)^2 := by
  rw [mul_comm (2 : ℝ) gamma,Real.rpow_mul hv,Real.rpow_two]

lemma vaughan_two_power_eval_odd_floor_power_square_sum_upper (U A Y : ℕ) (L gamma : ℝ)
    (hA : 1 ≤ A) (hY : 1 ≤ Y) (hL : 0 ≤ L) (hg0 : 0 < gamma) (hg1 : gamma ≤ 1/2) :
    (∑ k∈Icc 1 Y,if Nat.Coprime k 2 then
      ((L/(max 1 (A/((U+1)*k)) : ℕ))^gamma)^2/k else 0) ≤
      ((2*L*(U+1 : ℕ)/A)^gamma)^2*vaughan_two_power_eval_oddRankinPowerIntegralBound Y (2*gamma) := by
  have hi := odd_floor_two_power_sum_upper U A Y L 0 (2*gamma) 0 hA hY hL (by norm_num)
    (by positivity) (by norm_num) (by linarith) (by linarith)
  simp only [add_zero,Real.rpow_zero,mul_one] at hi
  have heq : (∑ k∈Icc 1 Y,if Nat.Coprime k 2 then
      (L/(max 1 (A/((U+1)*k)) : ℕ))^(2*gamma)/k else 0) =
      (∑ k∈Icc 1 Y,if Nat.Coprime k 2 then
      ((L/(max 1 (A/((U+1)*k)) : ℕ))^gamma)^2/k else 0) := by
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs
    · rw [vaughan_two_power_eval_nonnegative_rpow_double _ _ (by positivity)]
    · rfl
  rw [heq,vaughan_two_power_eval_nonnegative_rpow_double _ _ (by positivity)] at hi
  exact hi

lemma vaughan_two_power_eval_two_power_energy_odd_sum_upper (U A Y : ℕ) (L T a b s t : ℝ)
    (hA : 1 ≤ A) (hY : 1 ≤ Y) (hL : 0 ≤ L) (hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs0 : 1/2 < s) (hs1 : s < 1) (ht0 : 1/2 < t) (ht1 : t < 1) :
    (∑ k∈Icc 1 Y,if Nat.Coprime k 2 then
      vaughan_two_power_eval_twoPowerCoprimeEnergyPolynomial 2 a b s t
        ((L/(max 1 (A/((U+1)*k)) : ℕ))^(1-s))
        ((T/(max 1 (A/((U+1)*k)) : ℕ))^(1-t))/k else 0) ≤
      a^2*((2*L*(U+1 : ℕ)/A)^(1-s))^2*
        (vaughan_two_power_tp_rankinSingleZetaConstant s*vaughan_two_power_tp_rankinSharpCoprimeFactor 2 s)^2*
        vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant 2 s s*vaughan_two_power_eval_oddRankinPowerIntegralBound Y (2*(1-s)) +
      2*a*b*((2*L*(U+1 : ℕ)/A)^(1-s))*((2*T*(U+1 : ℕ)/A)^(1-t))*
        (vaughan_two_power_tp_rankinSingleZetaConstant s*vaughan_two_power_tp_rankinSharpCoprimeFactor 2 s)*
        (vaughan_two_power_tp_rankinSingleZetaConstant t*vaughan_two_power_tp_rankinSharpCoprimeFactor 2 t)*
        vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant 2 s t*vaughan_two_power_eval_oddRankinPowerIntegralBound Y (2-s-t) +
      b^2*((2*T*(U+1 : ℕ)/A)^(1-t))^2*
        (vaughan_two_power_tp_rankinSingleZetaConstant t*vaughan_two_power_tp_rankinSharpCoprimeFactor 2 t)^2*
        vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant 2 t t*vaughan_two_power_eval_oddRankinPowerIntegralBound Y (2*(1-t)) := by
  let Rs := vaughan_two_power_tp_rankinSingleZetaConstant s*vaughan_two_power_tp_rankinSharpCoprimeFactor 2 s
  let Rt := vaughan_two_power_tp_rankinSingleZetaConstant t*vaughan_two_power_tp_rankinSharpCoprimeFactor 2 t
  let Css := vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant 2 s s
  let Cst := vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant 2 s t
  let Ctt := vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant 2 t t
  let P : ℕ → ℝ := fun k => (L/(max 1 (A/((U+1)*k)) : ℕ))^(1-s)
  let Z : ℕ → ℝ := fun k => (T/(max 1 (A/((U+1)*k)) : ℕ))^(1-t)
  let P0 := (2*L*(U+1 : ℕ)/A)^(1-s)
  let Z0 := (2*T*(U+1 : ℕ)/A)^(1-t)
  have hss := vaughan_two_power_eval_odd_floor_power_square_sum_upper U A Y L (1-s) hA hY hL (by linarith) (by linarith)
  have htt := vaughan_two_power_eval_odd_floor_power_square_sum_upper U A Y T (1-t) hA hY hT (by linarith) (by linarith)
  have hst := odd_floor_two_power_sum_upper U A Y L T (1-s) (1-t) hA hY hL hT
    (by linarith) (by linarith) (by linarith) (by linarith)
  change (∑ k∈Icc 1 Y,if Nat.Coprime k 2 then P k*Z k/k else 0) ≤
    P0*Z0*vaughan_two_power_eval_oddRankinPowerIntegralBound Y ((1-s)+(1-t)) at hst
  rw [show (1-s)+(1-t)=(2 : ℝ)-s-t by ring] at hst
  change (∑ k∈Icc 1 Y,if Nat.Coprime k 2 then (P k)^2/k else 0) ≤
    P0^2*vaughan_two_power_eval_oddRankinPowerIntegralBound Y (2*(1-s)) at hss
  change (∑ k∈Icc 1 Y,if Nat.Coprime k 2 then (Z k)^2/k else 0) ≤
    Z0^2*vaughan_two_power_eval_oddRankinPowerIntegralBound Y (2*(1-t)) at htt
  have hCs := vaughan_two_power_eval_two_power_coprime_constant_nonneg 2 s s (by linarith) (by linarith)
  have hCt := vaughan_two_power_eval_two_power_coprime_constant_nonneg 2 t t (by linarith) (by linarith)
  have hCst := vaughan_two_power_eval_two_power_coprime_constant_nonneg 2 s t (by linarith) (by linarith)
  have hRs : 0 ≤ Rs := mul_nonneg (vaughan_two_power_tp_rankin_single_zeta_constant_nonneg s)
    (vaughan_two_power_tp_rankin_sharp_factor_pos 2 s (by linarith)).le
  have hRt : 0 ≤ Rt := mul_nonneg (vaughan_two_power_tp_rankin_single_zeta_constant_nonneg t)
    (vaughan_two_power_tp_rankin_sharp_factor_pos 2 t (by linarith)).le
  have hCss : 0 ≤ Css := hCs
  have hCtt : 0 ≤ Ctt := hCt
  have hcst : 0 ≤ Cst := hCst
  have heq : (∑ k∈Icc 1 Y,if Nat.Coprime k 2 then
      vaughan_two_power_eval_twoPowerCoprimeEnergyPolynomial 2 a b s t (P k) (Z k)/k else 0)=
      a^2*Rs^2*Css*(∑ k∈Icc 1 Y,if Nat.Coprime k 2 then (P k)^2/k else 0)+
      2*a*b*Rs*Rt*Cst*(∑ k∈Icc 1 Y,if Nat.Coprime k 2 then P k*Z k/k else 0)+
      b^2*Rt^2*Ctt*(∑ k∈Icc 1 Y,if Nat.Coprime k 2 then (Z k)^2/k else 0) := by
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs
    · dsimp [vaughan_two_power_eval_twoPowerCoprimeEnergyPolynomial,Rs,Rt,Css,Cst,Ctt]
      ring
    · ring
  change (∑ k∈Icc 1 Y,if Nat.Coprime k 2 then vaughan_two_power_eval_twoPowerCoprimeEnergyPolynomial 2 a b s t (P k) (Z k)/k else 0) ≤ _
  rw [heq]
  have hi := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hss (by positivity : 0 ≤ a^2*Rs^2*Css))
    (mul_le_mul_of_nonneg_left hst (by positivity : 0 ≤ 2*a*b*Rs*Rt*Cst)))
    (mul_le_mul_of_nonneg_left htt (by positivity : 0 ≤ b^2*Rt^2*Ctt))
  apply hi.trans_eq
  dsimp [vaughan_two_power_eval_twoPowerCoprimeEnergyPolynomial,Rs,Rt,Css,Cst,Ctt,P0,Z0]
  ring

theorem actual_vaughan_odd_mobius_two_power_analytic_upper_complete
    (U A B : ℕ) (X L T a b s t : ℝ)
    (hA : 1 ≤ A) (hY : 1 ≤ B/(U+1)) (hAB : A ≤ B) (hhalf : B ≤ 2*A) (hU : 1 ≤ U) (hYX : (B/(U+1) : ℕ) ≤ X)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs0 : 1/2 < s) (hs1 : s < 1) (ht0 : 1/2 < t) (ht1 : t < 1)
    (hM : ∀ v : ℝ, 1 ≤ v → v ≤ X →
      |∑ r∈Icc 1 ⌊v⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤
        a*(L/v)^(1-s)+b*(T/v)^(1-t)) :
    let R : ℝ → ℝ := fun u =>
      (((∑' n : ℕ,(n : ℝ)^(-u-1))*(∑' n : ℕ,(n : ℝ)^(-2*u-1)))/
        (∑' n : ℕ,(n : ℝ)^(-3 : ℝ))) *
        (∏ p∈(2 : ℕ).primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-u)))
    let C : ℝ → ℝ → ℝ := fun u v =>
      ((∑' n : ℕ,(n : ℝ)^(-u-v))*(∑' n : ℕ,(n : ℝ)^(-u-2*v))*(∑' n : ℕ,(n : ℝ)^(-2*u-v)))/
        ((∑' n : ℕ,(n : ℝ)^(-3 : ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4 : ℝ))) /
          (∏ p∈(2 : ℕ).primeFactors,(1+(p : ℝ)^(-u-v)/
            ((1-(p : ℝ)^(-u)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-v)+(p : ℝ)^(-1:ℝ)))))
    let Y : ℕ := B/(U+1)
    let Psi : ℝ → ℝ := fun gamma => 1+((Y : ℝ)^gamma-1)/(2*gamma)
    let P : ℝ := (2*L*(U+1 : ℕ)/A)^(1-s)
    let Z : ℝ := (2*T*(U+1 : ℕ)/A)^(1-t)
    (∑ m∈Ioc A B,if Nat.Coprime m 2 then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0) ≤
      (4/Real.pi^2)*((B : ℝ)-A)*
        (a^2*P^2*(R s)^2*C s s*Psi (2*(1-s)) +
          2*a*b*P*Z*R s*R t*C s t*Psi (2-s-t) +
          b^2*Z^2*(R t)^2*C t t*Psi (2*(1-t))) +
        (107/10 : ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := by
  have hbase := actual_vaughan_odd_mobius_two_power_energy_upper U A B X L T a b s t
    hAB hhalf hU hYX hL hT ha hb hs0 hs1.le ht0 ht1.le hM
  have hsum := vaughan_two_power_eval_two_power_energy_odd_sum_upper U A (B/(U+1)) L T a b s t
    hA hY hL hT ha hb hs0 hs1 ht0 ht1
  have hABr : (0 : ℝ) ≤ (B : ℝ)-A := by
    have hh : (A : ℝ) ≤ B := by exact_mod_cast hAB
    linarith
  have hi := mul_le_mul_of_nonneg_left hsum
    (show (0 : ℝ) ≤ (4/Real.pi^2)*((B : ℝ)-A) by positivity)
  apply hbase.trans ((add_le_add hi (le_refl ((107/10 : ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ))))).trans_eq ?_)
  dsimp [vaughan_two_power_tp_rankinSingleZetaConstant,vaughan_two_power_tp_rankinSharpCoprimeFactor,vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant,
    vaughan_two_power_tp_rankinCoupledZetaConstant,vaughan_two_power_tp_rankinCoupledExcludedProduct,vaughan_two_power_eval_oddRankinPowerIntegralBound]


end Helfgott
end

open Helfgott Finset Nat Real ArithmeticFunction MeasureTheory
open scoped BigOperators Classical Interval
theorem solution 
    (U A B : ℕ) (X L T a b s t : ℝ)
    (hA : 1 ≤ A) (hY : 1 ≤ B/(U+1)) (hAB : A ≤ B) (hhalf : B ≤ 2*A) (hU : 1 ≤ U) (hYX : (B/(U+1) : ℕ) ≤ X)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs0 : 1/2 < s) (hs1 : s < 1) (ht0 : 1/2 < t) (ht1 : t < 1)
    (hM : ∀ v : ℝ, 1 ≤ v → v ≤ X →
      |∑ r∈Icc 1 ⌊v⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤
        a*(L/v)^(1-s)+b*(T/v)^(1-t)) :
    let R : ℝ → ℝ := fun u =>
      (((∑' n : ℕ,(n : ℝ)^(-u-1))*(∑' n : ℕ,(n : ℝ)^(-2*u-1)))/
        (∑' n : ℕ,(n : ℝ)^(-3 : ℝ))) *
        (∏ p∈(2 : ℕ).primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-u)))
    let C : ℝ → ℝ → ℝ := fun u v =>
      ((∑' n : ℕ,(n : ℝ)^(-u-v))*(∑' n : ℕ,(n : ℝ)^(-u-2*v))*(∑' n : ℕ,(n : ℝ)^(-2*u-v)))/
        ((∑' n : ℕ,(n : ℝ)^(-3 : ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4 : ℝ))) /
          (∏ p∈(2 : ℕ).primeFactors,(1+(p : ℝ)^(-u-v)/
            ((1-(p : ℝ)^(-u)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-v)+(p : ℝ)^(-1:ℝ)))))
    let Y : ℕ := B/(U+1)
    let Psi : ℝ → ℝ := fun gamma => 1+((Y : ℝ)^gamma-1)/(2*gamma)
    let P : ℝ := (2*L*(U+1 : ℕ)/A)^(1-s)
    let Z : ℝ := (2*T*(U+1 : ℕ)/A)^(1-t)
    (∑ m∈Ioc A B,if Nat.Coprime m 2 then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0) ≤
      (4/Real.pi^2)*((B : ℝ)-A)*
        (a^2*P^2*(R s)^2*C s s*Psi (2*(1-s)) +
          2*a*b*P*Z*R s*R t*C s t*Psi (2-s-t) +
          b^2*Z^2*(R t)^2*C t t*Psi (2*(1-t))) +
        (107/10 : ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := Helfgott.actual_vaughan_odd_mobius_two_power_analytic_upper_complete U A B X L T a b s t hA hY hAB hhalf hU hYX hL hT ha hb hs0 hs1 ht0 ht1 hM
#print axioms solution
