-- Prove2me | solution 1 for Helfgott.actual_vaughan_odd_mobius_two_power_energy_upper
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T05:27:17.321364+00:00
-- url     : https://prove2.me/submissions/180f8108-2b6f-4d9d-b1c1-a7e7f1e8342c

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Theorems.Thm_Helfgott_mobius_sigma_coprime_real_two_power_energy_excluded_upper
import Mathlib.Algebra.Order.Floor.Semiring
import Theorems.Thm_Helfgott_actual_vaughan_odd_mobius_quadratic_integral_upper
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

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
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

noncomputable def vaughan_two_power_compact_strictMobiusCutoffLength (Y : ℕ) (U z : ℝ) : ℕ :=
  min Y (⌈z/U⌉₊-1)

lemma vaughan_two_power_compact_strict_mobius_cutoff_divisor_iff (Y d a : ℕ) (U z : ℝ)
    (hd : 1 ≤ d) (ha : 1 ≤ a) (hU : 0 < U) :
    (a ≤ Y/d ∧ U*(d*a : ℕ)<z) ↔ a ≤ vaughan_two_power_compact_strictMobiusCutoffLength Y U z/d := by
  have hceil : d*a<⌈z/U⌉₊ ↔ U*(d*a : ℕ)<z := by
    rw [Nat.lt_ceil, lt_div_iff₀ hU]
    rw [mul_comm]
  have hcut : U*(d*a : ℕ)<z ↔ d*a ≤ ⌈z/U⌉₊-1 := by
    have hda : 1 ≤ d*a := Nat.mul_le_mul hd ha
    rw [← hceil]
    omega
  rw [hcut, Nat.le_div_iff_mul_le (by omega), Nat.le_div_iff_mul_le (by omega)]
  unfold vaughan_two_power_compact_strictMobiusCutoffLength
  rw [le_min_iff]
  simp only [Nat.mul_comm]

lemma vaughan_two_power_compact_strict_mobius_cutoff_partial_sum_eq (f : ℕ → ℝ) (q Y d : ℕ) (U z : ℝ)
    (hd : 1 ≤ d) (hU : 0 < U) :
    (∑ a∈Icc 1 (Y/d), if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then f a else 0) =
      ∑ a∈Icc 1 (vaughan_two_power_compact_strictMobiusCutoffLength Y U z/d), if Nat.Coprime a (d*q) then f a else 0 := by
  have hfilter : (Icc 1 (Y/d)).filter (fun a => U*(d*a : ℕ)<z) =
      Icc 1 (vaughan_two_power_compact_strictMobiusCutoffLength Y U z/d) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro h
      exact ⟨h.1.1,(vaughan_two_power_compact_strict_mobius_cutoff_divisor_iff Y d a U z hd h.1.1 hU).mp ⟨h.1.2,h.2⟩⟩
    · intro h
      have hi := (vaughan_two_power_compact_strict_mobius_cutoff_divisor_iff Y d a U z hd h.1 hU).mpr h.2
      exact ⟨⟨h.1,hi.1⟩,hi.2⟩
  calc
    _ = ∑ a∈Icc 1 (Y/d), if U*(d*a : ℕ)<z then
        (if Nat.Coprime a (d*q) then f a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hc : Nat.Coprime a (d*q) <;> by_cases ht : U*(d*a : ℕ)<z <;>
        simp only [hc,ht,and_true,and_false,true_and,false_and,ite_true,ite_false]
    _ = ∑ a∈(Icc 1 (Y/d)).filter (fun a => U*(d*a : ℕ)<z),
        if Nat.Coprime a (d*q) then f a else 0 := (Finset.sum_filter _ _).symm
    _ = _ := by rw [hfilter]

theorem vaughan_two_power_compact_mobius_sigma_coprime_strict_cutoff_energy_eq (q Y : ℕ) (U z : ℝ) (hU : 0 < U) :
    let X : ℕ := min Y (⌈z/U⌉₊-1)
    let sigma : ℕ → ℝ := fun n => ∏ p∈n.primeFactors, ((p : ℝ)+1)
    (∑ d∈Icc 1 Y, if Nat.Coprime d q then |((moebius d : ℤ) : ℝ)|/(sigma d)^2 *
      (∑ a∈Icc 1 (Y/d), if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then
        ((moebius a : ℤ) : ℝ)/sigma a else 0)^2 else 0) =
    (∑ d∈Icc 1 X, if Nat.Coprime d q then |((moebius d : ℤ) : ℝ)|/(sigma d)^2 *
      (∑ a∈Icc 1 (X/d), if Nat.Coprime a (d*q) then
        ((moebius a : ℤ) : ℝ)/sigma a else 0)^2 else 0) := by
  let X := vaughan_two_power_compact_strictMobiusCutoffLength Y U z
  let sigma : ℕ → ℝ := fun n => ∏ p∈n.primeFactors, ((p : ℝ)+1)
  let f : ℕ → ℝ := fun a => ((moebius a : ℤ) : ℝ)/sigma a
  let g : ℕ → ℝ := fun d => if Nat.Coprime d q then |((moebius d : ℤ) : ℝ)|/(sigma d)^2 *
    (∑ a∈Icc 1 (X/d), if Nat.Coprime a (d*q) then f a else 0)^2 else 0
  change (∑ d∈Icc 1 Y, if Nat.Coprime d q then |((moebius d : ℤ) : ℝ)|/(sigma d)^2 *
      (∑ a∈Icc 1 (Y/d), if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then f a else 0)^2 else 0) =
    ∑ d∈Icc 1 X, g d
  have hinner : (∑ d∈Icc 1 Y, if Nat.Coprime d q then |((moebius d : ℤ) : ℝ)|/(sigma d)^2 *
      (∑ a∈Icc 1 (Y/d), if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then f a else 0)^2 else 0) =
    ∑ d∈Icc 1 Y, g d := by
    apply Finset.sum_congr rfl
    intro d hd
    dsimp only [g]
    rw [vaughan_two_power_compact_strict_mobius_cutoff_partial_sum_eq f q Y d U z (Finset.mem_Icc.mp hd).1 hU]
  rw [hinner]
  have hXY : X ≤ Y := min_le_left _ _
  have hsub : Icc 1 X ⊆ Icc 1 Y := fun d hd =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans hXY⟩
  exact (Finset.sum_subset hsub (fun d hdY hdX => by
    have hd : 1 ≤ d := (Finset.mem_Icc.mp hdY).1
    have hXd : X < d := by
      have hn : ¬d≤X := fun h => hdX (Finset.mem_Icc.mpr ⟨hd,h⟩)
      omega
    have hdiv : X/d = 0 := Nat.div_eq_of_lt hXd
    simp [g,hdiv])).symm

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

noncomputable def vaughan_two_power_tp_twoPowerCoprimeEnergyPolynomial (q : ℕ) (a b s t P Z : ℝ) : ℝ :=
  a^2*P^2*(vaughan_two_power_tp_rankinSingleZetaConstant s*vaughan_two_power_tp_rankinSharpCoprimeFactor q s)^2*vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant q s s +
    2*a*b*P*Z*(vaughan_two_power_tp_rankinSingleZetaConstant s*vaughan_two_power_tp_rankinSharpCoprimeFactor q s)*
      (vaughan_two_power_tp_rankinSingleZetaConstant t*vaughan_two_power_tp_rankinSharpCoprimeFactor q t)*vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant q s t +
    b^2*Z^2*(vaughan_two_power_tp_rankinSingleZetaConstant t*vaughan_two_power_tp_rankinSharpCoprimeFactor q t)^2*vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant q t t

lemma vaughan_two_power_tp_two_power_coprime_constant_nonneg (q : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    0 ≤ vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant q s t := by
  unfold vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant
  apply div_nonneg _ (vaughan_two_power_tp_rankin_coupled_excluded_product_pos q s t hs ht).le
  unfold vaughan_two_power_tp_rankinCoupledZetaConstant
  exact div_nonneg (mul_nonneg (mul_nonneg
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)))
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)))
    (mul_nonneg (sq_nonneg _) (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)))

lemma vaughan_two_power_tp_two_power_coprime_energy_polynomial_nonneg (q : ℕ) (a b s t P Z : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 < s) (ht : 0 < t) (hP : 0 ≤ P) (hZ : 0 ≤ Z) :
    0 ≤ vaughan_two_power_tp_twoPowerCoprimeEnergyPolynomial q a b s t P Z := by
  have hKs := vaughan_two_power_tp_rankin_single_zeta_constant_nonneg s
  have hKt := vaughan_two_power_tp_rankin_single_zeta_constant_nonneg t
  have hJs := (vaughan_two_power_tp_rankin_sharp_factor_pos q s hs).le
  have hJt := (vaughan_two_power_tp_rankin_sharp_factor_pos q t ht).le
  have hCss := vaughan_two_power_tp_two_power_coprime_constant_nonneg q s s hs hs
  have hCst := vaughan_two_power_tp_two_power_coprime_constant_nonneg q s t hs ht
  have hCtt := vaughan_two_power_tp_two_power_coprime_constant_nonneg q t t ht ht
  unfold vaughan_two_power_tp_twoPowerCoprimeEnergyPolynomial
  positivity

lemma vaughan_two_power_tp_two_power_coprime_energy_polynomial_mono (q : ℕ) (a b s t P Z P' Z' : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 < s) (ht : 0 < t)
    (hP : 0 ≤ P) (hZ : 0 ≤ Z) (hPP : P ≤ P') (hZZ : Z ≤ Z') :
    vaughan_two_power_tp_twoPowerCoprimeEnergyPolynomial q a b s t P Z ≤
      vaughan_two_power_tp_twoPowerCoprimeEnergyPolynomial q a b s t P' Z' := by
  have hKs := vaughan_two_power_tp_rankin_single_zeta_constant_nonneg s
  have hKt := vaughan_two_power_tp_rankin_single_zeta_constant_nonneg t
  have hJs := (vaughan_two_power_tp_rankin_sharp_factor_pos q s hs).le
  have hJt := (vaughan_two_power_tp_rankin_sharp_factor_pos q t ht).le
  have hCss := vaughan_two_power_tp_two_power_coprime_constant_nonneg q s s hs hs
  have hCst := vaughan_two_power_tp_two_power_coprime_constant_nonneg q s t hs ht
  have hCtt := vaughan_two_power_tp_two_power_coprime_constant_nonneg q t t ht ht
  have hsqP : P^2 ≤ P'^2 := (sq_le_sq₀ hP (hP.trans hPP)).mpr hPP
  have hsqZ : Z^2 ≤ Z'^2 := (sq_le_sq₀ hZ (hZ.trans hZZ)).mpr hZZ
  have hcross : P*Z ≤ P'*Z' := mul_le_mul hPP hZZ hZ (hP.trans hPP)
  have hpterm := mul_le_mul_of_nonneg_right hsqP
    (show 0 ≤ a^2*(vaughan_two_power_tp_rankinSingleZetaConstant s*vaughan_two_power_tp_rankinSharpCoprimeFactor q s)^2*vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant q s s by positivity)
  have hcterm := mul_le_mul_of_nonneg_right hcross
    (show 0 ≤ 2*a*b*(vaughan_two_power_tp_rankinSingleZetaConstant s*vaughan_two_power_tp_rankinSharpCoprimeFactor q s)*
      (vaughan_two_power_tp_rankinSingleZetaConstant t*vaughan_two_power_tp_rankinSharpCoprimeFactor q t)*vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant q s t by positivity)
  have hzterm := mul_le_mul_of_nonneg_right hsqZ
    (show 0 ≤ b^2*(vaughan_two_power_tp_rankinSingleZetaConstant t*vaughan_two_power_tp_rankinSharpCoprimeFactor q t)^2*vaughan_two_power_tp_rankinCoprimeCoupledZetaConstant q t t by positivity)
  unfold vaughan_two_power_tp_twoPowerCoprimeEnergyPolynomial
  nlinarith

noncomputable def vaughan_two_power_tp_twoPowerStrictMobiusEnergy (q Y : ℕ) (U z : ℝ) : ℝ :=
  ∑ d∈Icc 1 Y,if Nat.Coprime d q then
    |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2*
      (∑ r∈Icc 1 (Y/d),if Nat.Coprime r (d*q) ∧ U*(d*r : ℕ)<z then
        ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)) else 0)^2 else 0

lemma vaughan_two_power_tp_strict_mobius_two_power_energy_upper_of_lower
    (q Y N : ℕ) (X L T a b s t U z : ℝ)
    (hq : 1 ≤ q) (hN : 1 ≤ N) (hYX : (Y : ℝ) ≤ X)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs0 : 1/2 < s) (hs1 : s ≤ 1) (ht0 : 1/2 < t) (ht1 : t ≤ 1) (hU : 0 < U)
    (hlower : N ≤ vaughan_two_power_compact_strictMobiusCutoffLength Y U z ∨ vaughan_two_power_compact_strictMobiusCutoffLength Y U z = 0)
    (hM : ∀ v : ℝ, 1 ≤ v → v ≤ X →
      |∑ r∈Icc 1 ⌊v⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤
        a*(L/v)^(1-s)+b*(T/v)^(1-t)) :
    vaughan_two_power_tp_twoPowerStrictMobiusEnergy q Y U z ≤
      vaughan_two_power_tp_twoPowerCoprimeEnergyPolynomial q a b s t ((L/N)^(1-s)) ((T/N)^(1-t)) := by
  let K := vaughan_two_power_compact_strictMobiusCutoffLength Y U z
  have hKeq := vaughan_two_power_compact_mobius_sigma_coprime_strict_cutoff_energy_eq q Y U z hU
  change vaughan_two_power_tp_twoPowerStrictMobiusEnergy q Y U z =
    (∑ d∈Icc 1 K,if Nat.Coprime d q then
      |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2*
        (∑ r∈Icc 1 (K/d),if Nat.Coprime r (d*q) then
          ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)) else 0)^2 else 0) at hKeq
  rw [hKeq]
  rcases hlower with hlo | hz0
  · have hK1 : 1 ≤ K := hN.trans hlo
    have hKr1 : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have hKr : (0 : ℝ) < K := by linarith
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hNK : (N : ℝ) ≤ K := by exact_mod_cast hlo
    have hKX : (K : ℝ) ≤ X := le_trans (by exact_mod_cast (min_le_left Y (⌈z/U⌉₊-1))) hYX
    have hi := mobius_sigma_coprime_real_two_power_energy_excluded_upper q K L T a b s t
      hq hKr1 hL hT ha hb hs0 hs1 ht0 ht1 (fun v hv hvK => hM v hv (hvK.trans hKX))
    simp only [Nat.floor_natCast,Nat.floor_div_natCast] at hi
    change (∑ d∈Icc 1 K,if Nat.Coprime d q then
      |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2*
        (∑ r∈Icc 1 (K/d),if Nat.Coprime r (d*q) then
          ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)) else 0)^2 else 0) ≤
      vaughan_two_power_tp_twoPowerCoprimeEnergyPolynomial q a b s t ((L/K)^(1-s)) ((T/K)^(1-t)) at hi
    have hp := Real.rpow_le_rpow (div_nonneg hL hKr.le)
      (div_le_div_of_nonneg_left hL hNr hNK) (by linarith : 0 ≤ 1-s)
    have ht := Real.rpow_le_rpow (div_nonneg hT hKr.le)
      (div_le_div_of_nonneg_left hT hNr hNK) (by linarith : 0 ≤ 1-t)
    exact hi.trans (vaughan_two_power_tp_two_power_coprime_energy_polynomial_mono q a b s t _ _ _ _ ha hb
      (by linarith) (by linarith) (by positivity) (by positivity) hp ht)
  · have hn := vaughan_two_power_tp_two_power_coprime_energy_polynomial_nonneg q a b s t ((L/N)^(1-s)) ((T/N)^(1-t))
      ha hb (by linarith) (by linarith) (by positivity) (by positivity)
    simpa [K,hz0] using hn
end Helfgott
end

section
set_option autoImplicit false
open Finset
open scoped BigOperators Classical
namespace Helfgott

theorem vaughan_two_power_finite_positive_divisor_reindex (B : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ q ∈ Icc 1 B, ∑ d ∈ q.divisors, F d (q/d)) =
      ∑ d ∈ Icc 1 B, ∑ r ∈ Icc 1 (B/d), F d r := by
  classical
  rw [← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.2 (i.1/i.2)),
    ← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.1 i.2)]
  refine sum_bij (fun i _ => (⟨i.2, i.1/i.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    rcases mem_sigma.mp hi with ⟨hq, hd⟩
    have hdq := (Nat.mem_divisors.mp hd).1
    have hqpos : 0 < i.1 := (mem_Icc.mp hq).1
    have hdpos := Nat.pos_of_dvd_of_pos hdq hqpos
    apply mem_sigma.mpr
    constructor
    · exact mem_Icc.mpr ⟨hdpos, (Nat.le_of_dvd hqpos hdq).trans (mem_Icc.mp hq).2⟩
    · apply mem_Icc.mpr
      exact ⟨Nat.div_pos (Nat.le_of_dvd hqpos hdq) hdpos,
        Nat.div_le_div_right (mem_Icc.mp hq).2⟩
  · intro i hi j hj he
    rcases mem_sigma.mp hi with ⟨_, hdi⟩
    rcases mem_sigma.mp hj with ⟨_, hdj⟩
    have hd : i.2 = j.2 := congrArg Sigma.fst he
    have hr : i.1/i.2 = j.1/j.2 := congrArg (fun k : Σ _ : ℕ, ℕ => k.2) he
    have hq : i.1 = j.1 := by
      calc
        i.1 = i.2*(i.1/i.2) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hdi).1).symm
        _ = j.2*(j.1/j.2) := by rw [hr, hd]
        _ = j.1 := Nat.mul_div_cancel' (Nat.mem_divisors.mp hdj).1
    exact Sigma.ext hq (by simpa using hd)
  · intro j hj
    rcases mem_sigma.mp hj with ⟨hd, hr⟩
    have hdpos : 0 < j.1 := (mem_Icc.mp hd).1
    have hrpos : 0 < j.2 := (mem_Icc.mp hr).1
    have hprod : j.1*j.2 ≤ B := by
      calc
        _ ≤ j.1*(B/j.1) := Nat.mul_le_mul_left j.1 (mem_Icc.mp hr).2
        _ ≤ B := by simpa only [mul_comm] using Nat.div_mul_le_self B j.1
    refine ⟨⟨j.1*j.2, j.1⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hdpos hrpos, hprod⟩,
      Nat.mem_divisors.mpr ⟨Nat.dvd_mul_right j.1 j.2, (Nat.mul_pos hdpos hrpos).ne'⟩⟩, ?_⟩
    change (⟨j.1, (j.1*j.2)/j.1⟩ : Σ _ : ℕ, ℕ) = j
    rw [Nat.mul_div_right j.2 hdpos]
  · intro _ _
    rfl

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat
open scoped BigOperators Classical
namespace Helfgott

lemma vaughan_two_power_finite_positive_multiples_reindex (Y d : ℕ) (hd : 1 ≤ d) (F : ℕ→ℝ) :
    (∑ r∈Finset.Icc 1 Y,if d∣r then F r else 0)=∑ a∈Finset.Icc 1 (Y/d),F (d*a) := by
  rw [←Finset.sum_filter]
  apply Finset.sum_bij (fun r hr => r/d)
  · intro r hr
    obtain ⟨hrI,hrd⟩ := Finset.mem_filter.mp hr
    have hrpos := (Finset.mem_Icc.mp hrI).1
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hrpos hrd) hd,
      Nat.div_le_div_right (Finset.mem_Icc.mp hrI).2⟩
  · intro r hr t ht he
    have hrdiv := (Finset.mem_filter.mp hr).2
    have htdiv := (Finset.mem_filter.mp ht).2
    calc r=d*(r/d) := (Nat.mul_div_cancel' hrdiv).symm
         _=d*(t/d) := by rw [he]
         _=t := Nat.mul_div_cancel' htdiv
  · intro a ha
    have hp : 1 ≤ d*a := Nat.mul_pos hd (Finset.mem_Icc.mp ha).1
    have hb : d*a ≤ Y := by
      simpa only [mul_comm] using (Nat.le_div_iff_mul_le hd).mp (Finset.mem_Icc.mp ha).2
    exact ⟨d*a,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp,hb⟩,dvd_mul_right d a⟩,Nat.mul_div_right a hd⟩
  · intro r hr
    rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hr).2]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma vaughan_two_power_floorRoot_two_eq_one_iff_squarefree (n : ℕ) (hn : n ≠ 0) :
    Nat.floorRoot 2 n = 1 ↔ Squarefree n := by
  constructor
  · intro hroot
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hdvd
    have h : p ∣ Nat.floorRoot 2 n := Nat.pow_dvd_iff_dvd_floorRoot.mp (by simpa [pow_two] using hdvd)
    rw [hroot] at h
    exact hp.ne_one (Nat.dvd_one.mp h)
  · intro hsf
    have h := hsf (Nat.floorRoot 2 n) (by simpa [pow_two] using Nat.floorRoot_pow_dvd (n:=2) (a:=n))
    exact Nat.isUnit_iff.mp h

lemma vaughan_two_power_moebius_divisor_sum (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors,moebius d) = if n=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa [ArithmeticFunction.one_apply,hn] using h

theorem vaughan_two_power_moebius_square_divisor_expansion (n : ℕ) (hn : n ≠ 0) :
    (moebius n)^2 = ∑ d ∈ n.divisors,if d^2 ∣ n then moebius d else 0 := by
  have hroot0 : Nat.floorRoot 2 n ≠ 0 := Nat.floorRoot_ne_zero.mpr ⟨by norm_num,hn⟩
  have he : n.divisors.filter (fun d => d^2 ∣ n) = (Nat.floorRoot 2 n).divisors := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd,hn0⟩,hsq⟩
      exact ⟨Nat.pow_dvd_iff_dvd_floorRoot.mp hsq,hroot0⟩
    · rintro ⟨hd,hr0⟩
      have hsq := Nat.pow_dvd_iff_dvd_floorRoot.mpr hd
      exact ⟨⟨dvd_trans (dvd_pow_self d (by norm_num : 2 ≠ 0)) hsq,hn⟩,hsq⟩
  rw [←Finset.sum_filter,he,vaughan_two_power_moebius_divisor_sum _ hroot0,moebius_sq]
  simp only [vaughan_two_power_floorRoot_two_eq_one_iff_squarefree n hn]

lemma vaughan_two_power_coprime_moebius_divisor_expansion (q n : ℕ) (hq : q ≠ 0) :
    (∑ e ∈ q.divisors,if e ∣ n then moebius e else 0) =
      if Nat.Coprime n q then 1 else 0 := by
  have he : q.divisors.filter (fun e => e ∣ n) = (Nat.gcd n q).divisors := by
    ext e
    simp only [Finset.mem_filter,Nat.mem_divisors]
    have hg : Nat.gcd n q ≠ 0 := Nat.gcd_ne_zero_right hq
    constructor
    · rintro ⟨⟨heq,hq0⟩,hen⟩
      exact ⟨Nat.dvd_gcd hen heq,hg⟩
    · rintro ⟨heg,hg0⟩
      exact ⟨⟨dvd_trans heg (Nat.gcd_dvd_right n q),hq⟩,dvd_trans heg (Nat.gcd_dvd_left n q)⟩
  rw [←Finset.sum_filter,he,vaughan_two_power_moebius_divisor_sum _ (Nat.gcd_ne_zero_right hq)]

theorem vaughan_two_power_squarefree_coprime_pointwise_expansion (q n : ℕ) (hq : q ≠ 0) (hn : n ≠ 0) :
    (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0)*
      (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) := by
  have hcop : (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) =
      if Nat.Coprime n q then 1 else 0 := by
    exact_mod_cast vaughan_two_power_coprime_moebius_divisor_expansion q n hq
  rw [hcop]
  by_cases h : Nat.Coprime n q
  · simp only [if_pos h,mul_one]
    have he : (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0) =
        ∑ d ∈ n.divisors,if d^2 ∣ n then ((moebius d : ℤ) : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdc : Nat.Coprime d q := h.of_dvd_left (Nat.dvd_of_mem_divisors hd)
      by_cases hs : d^2 ∣ n <;> simp [hs,hdc]
    rw [he]
    exact_mod_cast vaughan_two_power_moebius_square_divisor_expansion n hn
  · simp [h]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

lemma vaughan_two_power_finite_coprime_pair_mobius_reindex (Y : ℕ) (F : ℕ→ℕ→ℝ) :
    (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,if Nat.Coprime r t then F r t else 0)=
      ∑ d∈Finset.Icc 1 Y,((moebius d : ℤ) : ℝ)*
        (∑ a∈Finset.Icc 1 (Y/d),∑ b∈Finset.Icc 1 (Y/d),F (d*a) (d*b)) := by
  have hpoint (r t : ℕ) (hr : 1 ≤ r) :
      (if Nat.Coprime r t then F r t else 0)=
        ∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ)*F r t else 0 := by
    have hc : (∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ) else 0)=
        if Nat.Coprime r t then (1:ℝ) else 0 := by
      have h := vaughan_two_power_coprime_moebius_divisor_expansion r t (by omega)
      have hR : (∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ) else 0)=
          if Nat.Coprime t r then (1:ℝ) else 0 := by exact_mod_cast h
      simpa only [Nat.coprime_comm] using hR
    calc
      _=(if Nat.Coprime r t then (1:ℝ) else 0)*F r t := by split_ifs <;> simp
      _=(∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ) else 0)*F r t := by rw [hc]
      _=_ := by rw [Finset.sum_mul];apply Finset.sum_congr rfl;intro d hd;split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl (fun t ht => hpoint r t (Finset.mem_Icc.mp hr).1)),Finset.sum_comm]
  have hdiv (t : ℕ) : (∑ r∈Finset.Icc 1 Y,∑ d∈r.divisors,
      if d∣t then ((moebius d : ℤ) : ℝ)*F r t else 0)=
      ∑ d∈Finset.Icc 1 Y,∑ a∈Finset.Icc 1 (Y/d),
        if d∣t then ((moebius d : ℤ) : ℝ)*F (d*a) t else 0 := by
    have hr (r : ℕ) (hr : r∈Finset.Icc 1 Y) :
        (∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ)*F r t else 0)=
        ∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ)*F (d*(r/d)) t else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
    rw [Finset.sum_congr rfl hr,vaughan_two_power_finite_positive_divisor_reindex Y
      (fun d a => if d∣t then ((moebius d : ℤ) : ℝ)*F (d*a) t else 0)]
  rw [Finset.sum_congr rfl (fun t ht => hdiv t),Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [vaughan_two_power_finite_positive_multiples_reindex Y d (Finset.mem_Icc.mp hd).1
    (fun t => ((moebius d : ℤ) : ℝ)*F (d*a) t),Finset.mul_sum]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

noncomputable def vaughan_two_power_mobiusSigmaWeight (n : ℕ) : ℝ :=
  ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))

lemma vaughan_two_power_mobiusSigmaWeight_mul (d a : ℕ) :
    vaughan_two_power_mobiusSigmaWeight (d*a)=if Nat.Coprime d a then vaughan_two_power_mobiusSigmaWeight d*vaughan_two_power_mobiusSigmaWeight a else 0 := by
  by_cases hc : Nat.Coprime d a
  · rw [if_pos hc]
    have hS : (∏ p∈(d*a).primeFactors,((p : ℝ)+1))=
        (∏ p∈d.primeFactors,((p : ℝ)+1))*(∏ p∈a.primeFactors,((p : ℝ)+1)) := by
      rw [hc.primeFactors_mul,Finset.prod_union hc.disjoint_primeFactors]
    dsimp [vaughan_two_power_mobiusSigmaWeight]
    rw [isMultiplicative_moebius.map_mul_of_coprime hc,Int.cast_mul,hS]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · rw [if_neg hc]
    have hsf : ¬Squarefree (d*a) := fun h => hc (Nat.coprime_of_squarefree_mul h)
    simp [vaughan_two_power_mobiusSigmaWeight,moebius_eq_zero_of_not_squarefree hsf]

lemma vaughan_two_power_moebius_real_cube_eq_self (d : ℕ) : ((moebius d : ℤ) : ℝ)^3=((moebius d : ℤ) : ℝ) := by
  by_cases hd : moebius d=0
  · rw [hd];norm_num
  · obtain h | h := moebius_ne_zero_iff_eq_or.mp hd <;> rw [h] <;> norm_num

lemma vaughan_two_power_mobiusSigmaWeight_moebius_square (d : ℕ) :
    ((moebius d : ℤ) : ℝ)*(vaughan_two_power_mobiusSigmaWeight d)^2=
      ((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2 := by
  dsimp [vaughan_two_power_mobiusSigmaWeight]
  rw [div_pow]
  calc
    _=((moebius d : ℤ) : ℝ)^3/(∏ p∈d.primeFactors,((p : ℝ)+1))^2 := by ring
    _=_ := by rw [vaughan_two_power_moebius_real_cube_eq_self]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma vaughan_two_power_mobius_sigma_pair_common_divisor (d a b q : ℕ) :
    ((moebius d : ℤ) : ℝ)*
      (if Nat.Coprime (d*a) q ∧ Nat.Coprime (d*b) q then
        vaughan_two_power_mobiusSigmaWeight (d*a)*vaughan_two_power_mobiusSigmaWeight (d*b) else 0)=
      if Nat.Coprime d q then
        (((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (if Nat.Coprime a (d*q) then vaughan_two_power_mobiusSigmaWeight a else 0)*
          (if Nat.Coprime b (d*q) then vaughan_two_power_mobiusSigmaWeight b else 0) else 0 := by
  have hfactor := vaughan_two_power_mobiusSigmaWeight_moebius_square d
  rw [vaughan_two_power_mobiusSigmaWeight_mul,vaughan_two_power_mobiusSigmaWeight_mul]
  simp only [Nat.coprime_mul_iff_left,Nat.coprime_mul_iff_right]
  have hca : Nat.Coprime a d ↔ Nat.Coprime d a := Nat.coprime_comm
  have hcb : Nat.Coprime b d ↔ Nat.Coprime d b := Nat.coprime_comm
  split_ifs <;> simp_all only [hca,hcb,mul_zero,zero_mul] <;> try aesop
  linear_combination (vaughan_two_power_mobiusSigmaWeight a*vaughan_two_power_mobiusSigmaWeight b)*hfactor

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma vaughan_two_power_mobius_sigma_weighted_pair_common_divisor (d a b q : ℕ) (h : ℕ→ℝ) :
    ((moebius d : ℤ) : ℝ)*
      (if Nat.Coprime (d*a) q ∧ Nat.Coprime (d*b) q then
        (vaughan_two_power_mobiusSigmaWeight (d*a)*h (d*a))*(vaughan_two_power_mobiusSigmaWeight (d*b)*h (d*b)) else 0)=
      if Nat.Coprime d q then
        (((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (if Nat.Coprime a (d*q) then vaughan_two_power_mobiusSigmaWeight a*h (d*a) else 0)*
          (if Nat.Coprime b (d*q) then vaughan_two_power_mobiusSigmaWeight b*h (d*b) else 0) else 0 := by
  have hp := vaughan_two_power_mobius_sigma_pair_common_divisor d a b q
  have he := congrArg (fun x : ℝ => x*h (d*a)*h (d*b)) hp
  convert he using 1 <;> split_ifs <;> ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem vaughan_two_power_mobius_sigma_weighted_coprime_pair_square_decomposition (q Y : ℕ) (h : ℕ→ℝ) :
    let f : ℕ→ℝ := fun n => ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))
    (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then (f r*h r)*(f t*h t) else 0)=
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then f a*h (d*a) else 0)^2 else 0 := by
  change (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then (vaughan_two_power_mobiusSigmaWeight r*h r)*(vaughan_two_power_mobiusSigmaWeight t*h t) else 0)=_
  have hleft : (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then (vaughan_two_power_mobiusSigmaWeight r*h r)*(vaughan_two_power_mobiusSigmaWeight t*h t) else 0)=
      ∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,if Nat.Coprime r t then
        (if Nat.Coprime r q ∧ Nat.Coprime t q then (vaughan_two_power_mobiusSigmaWeight r*h r)*(vaughan_two_power_mobiusSigmaWeight t*h t) else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t ht
    split_ifs <;> aesop
  rw [hleft,vaughan_two_power_finite_coprime_pair_mobius_reindex]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  have he : (∑ a∈Finset.Icc 1 (Y/d),∑ b∈Finset.Icc 1 (Y/d),
      ((moebius d : ℤ) : ℝ)*(if Nat.Coprime (d*a) q ∧ Nat.Coprime (d*b) q then
        (vaughan_two_power_mobiusSigmaWeight (d*a)*h (d*a))*(vaughan_two_power_mobiusSigmaWeight (d*b)*h (d*b)) else 0))=
      ∑ a∈Finset.Icc 1 (Y/d),∑ b∈Finset.Icc 1 (Y/d),
        if Nat.Coprime d q then (((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (if Nat.Coprime a (d*q) then vaughan_two_power_mobiusSigmaWeight a*h (d*a) else 0)*
          (if Nat.Coprime b (d*q) then vaughan_two_power_mobiusSigmaWeight b*h (d*b) else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    exact Finset.sum_congr rfl (fun b hb => vaughan_two_power_mobius_sigma_weighted_pair_common_divisor d a b q h)
  rw [he]
  by_cases hc : Nat.Coprime d q
  · rw [if_pos hc]
    simp only [if_pos hc]
    simp_rw [←Finset.mul_sum]
    rw [←Finset.sum_mul,←Finset.mul_sum]
    change _=(((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
      (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then vaughan_two_power_mobiusSigmaWeight a*h (d*a) else 0)^2
    ring
  · simp only [if_neg hc,Finset.sum_const_zero]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem vaughan_two_power_mobius_sigma_weighted_coprime_pair_quadratic_bound (q Y : ℕ) (h : ℕ→ℝ) :
    let f : ℕ→ℝ := fun n => ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))
    |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then (f r*h r)*(f t*h t) else 0| ≤
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then f a*h (d*a) else 0)^2 else 0 := by
  dsimp only
  rw [vaughan_two_power_mobius_sigma_weighted_coprime_pair_square_decomposition]
  apply (abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hc : Nat.Coprime d q
  · rw [if_pos hc,if_pos hc,abs_mul,abs_div,
      abs_of_nonneg (sq_nonneg (∏ p∈d.primeFactors,((p : ℝ)+1))),abs_of_nonneg (sq_nonneg (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then (((moebius a : ℤ) : ℝ)/(∏ p∈a.primeFactors,((p : ℝ)+1)))*h (d*a) else 0))]
  · rw [if_neg hc,if_neg hc,abs_zero]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem vaughan_two_power_mobius_sigma_cutoff_coprime_pair_quadratic_bound (q Y : ℕ) (U z : ℝ) :
    let f : ℕ→ℝ := fun n => ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))
    |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q ∧ U*r<z ∧ U*t<z then f r*f t else 0| ≤
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then f a else 0)^2 else 0 := by
  let h : ℕ→ℝ := fun n => if U*n<z then 1 else 0
  have hb := vaughan_two_power_mobius_sigma_weighted_coprime_pair_quadratic_bound q Y h
  dsimp only at hb ⊢
  have hleft : (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then
        (vaughan_two_power_mobiusSigmaWeight r*h r)*(vaughan_two_power_mobiusSigmaWeight t*h t) else 0)=
      ∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
        if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q ∧ U*r<z ∧ U*t<z then
          vaughan_two_power_mobiusSigmaWeight r*vaughan_two_power_mobiusSigmaWeight t else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t ht
    dsimp [h]
    split_ifs <;> simp_all <;> try linarith <;> aesop
  have hright (d : ℕ) : (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then
        vaughan_two_power_mobiusSigmaWeight a*h (d*a) else 0)=
      ∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then vaughan_two_power_mobiusSigmaWeight a else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [h]
    split_ifs <;> simp_all <;> try linarith <;> aesop
  change |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
    if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then
      (vaughan_two_power_mobiusSigmaWeight r*h r)*(vaughan_two_power_mobiusSigmaWeight t*h t) else 0|≤_ at hb
  rw [hleft] at hb
  change |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
    if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q ∧ U*r<z ∧ U*t<z then
      vaughan_two_power_mobiusSigmaWeight r*vaughan_two_power_mobiusSigmaWeight t else 0|≤_
  exact hb.trans_eq (Finset.sum_congr rfl (fun d hd => by
    by_cases hc : Nat.Coprime d q
    · rw [if_pos hc,if_pos hc]
      congr 1
      exact congrArg (fun x : ℝ => x^2) (hright d)
    · rw [if_neg hc,if_neg hc]))

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma vaughan_two_power_cutoff_indicator_interval_integrable (c a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => if c<x then (1:ℝ) else 0) volume a b := by
  have hm : Measurable (fun x : ℝ => if c<x then (1:ℝ) else 0) :=
    Measurable.ite measurableSet_Ioi measurable_const measurable_const
  apply (intervalIntegrable_const (c:=(1:ℝ))).mono_fun' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by dsimp only;split_ifs <;> norm_num)

lemma vaughan_two_power_cutoff_indicator_interval_integral (a b c : ℝ) (hab : a ≤ b) (hcb : c ≤ b) :
    (∫ x in a..b,if c<x then (1:ℝ) else 0)=b-max a c := by
  by_cases hca : c ≤ a
  · rw [max_eq_left hca]
    have he : (∫ x in a..b,if c<x then (1:ℝ) else 0)=∫ x in a..b,(1:ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hab
      intro x hx
      exact if_pos (hca.trans_lt hx.1)
    rw [he,intervalIntegral.integral_const]
    simp
  · have hac : a ≤ c := le_of_not_ge hca
    rw [max_eq_right hac]
    have hleft : (∫ x in a..c,if c<x then (1:ℝ) else 0)=0 := by
      calc
        _=∫ x in a..c,(0:ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hac
          intro x hx
          exact if_neg (by linarith [hx.2])
        _=0 := by simp
    have hright : (∫ x in c..b,if c<x then (1:ℝ) else 0)=b-c := by
      calc
        _=∫ x in c..b,(1:ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hcb
          intro x hx
          exact if_pos hx.1
        _=b-c := by simp
    have h := intervalIntegral.integral_add_adjacent_intervals
      (vaughan_two_power_cutoff_indicator_interval_integrable c a c) (vaughan_two_power_cutoff_indicator_interval_integrable c c b)
    rw [hleft,hright,zero_add] at h
    exact h.symm

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma vaughan_two_power_finite_coprime_cutoff_sum_measurable (S : Finset ℕ) (q : ℕ) (w c : ℕ→ℝ) :
    Measurable (fun z : ℝ => ∑ a∈S,if Nat.Coprime a q ∧ c a<z then w a else 0) := by
  apply Finset.measurable_sum
  intro a ha
  by_cases hc : Nat.Coprime a q
  · have he : (fun z : ℝ => if Nat.Coprime a q ∧ c a<z then w a else 0)=
        (fun z : ℝ => if c a<z then w a else 0) := by
      funext z
      by_cases hz : c a<z
      · rw [if_pos ⟨hc,hz⟩,if_pos hz]
      · rw [if_neg (show ¬(Nat.Coprime a q ∧ c a<z) from by aesop),if_neg hz]
    rw [he]
    exact Measurable.ite measurableSet_Ioi measurable_const measurable_const
  · have he : (fun z : ℝ => if Nat.Coprime a q ∧ c a<z then w a else 0)=(fun _ : ℝ => (0:ℝ)) := by
      funext z;simp only [hc,false_and,if_false]
    rw [he]
    exact measurable_const

lemma vaughan_two_power_finite_coprime_cutoff_sum_abs_bound (S : Finset ℕ) (q : ℕ) (w c : ℕ→ℝ) (z : ℝ) :
    |∑ a∈S,if Nat.Coprime a q ∧ c a<z then w a else 0|≤∑ a∈S,|w a| := by
  apply (abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a ha
  split_ifs
  · exact le_rfl
  · simp only [abs_zero]
    exact abs_nonneg _

lemma vaughan_two_power_finite_coprime_cutoff_square_interval_integrable (S : Finset ℕ) (q : ℕ) (w c : ℕ→ℝ) (l r : ℝ) :
    IntervalIntegrable (fun z : ℝ => (∑ a∈S,if Nat.Coprime a q ∧ c a<z then w a else 0)^2) volume l r := by
  have hm := (vaughan_two_power_finite_coprime_cutoff_sum_measurable S q w c).pow_const 2
  apply (intervalIntegrable_const (c:=(∑ a∈S,|w a|)^2)).mono_fun' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hb := vaughan_two_power_finite_coprime_cutoff_sum_abs_bound S q w c z
  have hs : 0≤∑ a∈S,|w a| := Finset.sum_nonneg (fun a ha => abs_nonneg _)
  exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hs] using hb)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma vaughan_two_power_finite_interval_integrable_sum {ι : Type} (S : Finset ι) (f : ι→ℝ→ℝ) (l r : ℝ)
    (hf : ∀ i∈S,IntervalIntegrable (f i) volume l r) :
    IntervalIntegrable (fun z => ∑ i∈S,f i z) volume l r := by
  have he : (∑ i∈S,f i)=(fun z => ∑ i∈S,f i z) := by funext z;simp
  rw [←he]
  exact IntervalIntegrable.sum S hf

lemma vaughan_two_power_finite_filtered_cutoff_pair_interval_integrable (S T : Finset ℕ)
    (P : ℕ→ℕ→Prop) [∀ a b,Decidable (P a b)] (w c : ℕ→ℕ→ℝ) (l r : ℝ) :
    IntervalIntegrable (fun z => ∑ a∈S,∑ b∈T,if P a b ∧ c a b<z then w a b else 0) volume l r := by
  apply vaughan_two_power_finite_interval_integrable_sum
  intro a ha
  apply vaughan_two_power_finite_interval_integrable_sum
  intro b hb
  by_cases hP : P a b
  · have hi := (vaughan_two_power_cutoff_indicator_interval_integrable (c a b) l r).const_mul (w a b)
    apply hi.congr
    intro z hz
    dsimp only
    by_cases hc : c a b<z
    · rw [if_pos hc,if_pos ⟨hP,hc⟩,mul_one]
    · rw [if_neg hc,if_neg (show ¬(P a b ∧ c a b<z) from by aesop),mul_zero]
  · have he : (fun z : ℝ => if P a b ∧ c a b<z then w a b else 0)=(fun _ => (0:ℝ)) := by
      funext z
      exact if_neg (by aesop)
    rw [he]
    exact intervalIntegrable_const

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma vaughan_two_power_mobius_sigma_cutoff_pair_interval_integrable (q Y : ℕ) (U l r : ℝ) :
    IntervalIntegrable (fun z => ∑ a∈Finset.Icc 1 Y,∑ b∈Finset.Icc 1 Y,
      if Nat.Coprime a b ∧ Nat.Coprime a q ∧ Nat.Coprime b q ∧ U*a<z ∧ U*b<z then
        vaughan_two_power_mobiusSigmaWeight a*vaughan_two_power_mobiusSigmaWeight b else 0) volume l r := by
  have hi := vaughan_two_power_finite_filtered_cutoff_pair_interval_integrable (Finset.Icc 1 Y) (Finset.Icc 1 Y)
    (fun a b => Nat.Coprime a b ∧ Nat.Coprime a q ∧ Nat.Coprime b q)
    (fun a b => vaughan_two_power_mobiusSigmaWeight a*vaughan_two_power_mobiusSigmaWeight b) (fun a b => max (U*a) (U*b)) l r
  apply hi.congr
  intro z hz
  dsimp only
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp_all only [max_lt_iff] <;> aesop

lemma vaughan_two_power_mobius_sigma_cutoff_quadratic_interval_integrable (q Y : ℕ) (U l r : ℝ) :
    IntervalIntegrable (fun z => ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
      (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
        (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then vaughan_two_power_mobiusSigmaWeight a else 0)^2 else 0) volume l r := by
  apply vaughan_two_power_finite_interval_integrable_sum
  intro d hd
  by_cases hc : Nat.Coprime d q
  · have hi := (vaughan_two_power_finite_coprime_cutoff_square_interval_integrable (Finset.Icc 1 (Y/d)) (d*q)
        vaughan_two_power_mobiusSigmaWeight (fun a => U*(d*a : ℕ)) l r).const_mul
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)
    simpa only [if_pos hc] using hi
  · simpa only [if_neg hc] using (intervalIntegrable_const (c:=(0:ℝ)) : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume l r)

theorem vaughan_two_power_mobius_sigma_cutoff_integral_quadratic_upper (q Y : ℕ) (U l r : ℝ) (hlr : l≤r) :
    (∫ z in l..r,∑ a∈Finset.Icc 1 Y,∑ b∈Finset.Icc 1 Y,
      if Nat.Coprime a b ∧ Nat.Coprime a q ∧ Nat.Coprime b q ∧ U*a<z ∧ U*b<z then
        vaughan_two_power_mobiusSigmaWeight a*vaughan_two_power_mobiusSigmaWeight b else 0)≤
      ∫ z in l..r,∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then vaughan_two_power_mobiusSigmaWeight a else 0)^2 else 0 := by
  apply intervalIntegral.integral_mono hlr
    (vaughan_two_power_mobius_sigma_cutoff_pair_interval_integrable q Y U l r)
    (vaughan_two_power_mobius_sigma_cutoff_quadratic_interval_integrable q Y U l r)
  intro z
  exact (le_abs_self _).trans (vaughan_two_power_mobius_sigma_cutoff_coprime_pair_quadratic_bound q Y U z)

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
open Finset Nat Real ArithmeticFunction MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma vaughan_two_power_tp_two_power_strict_cutoff_length_lower_on_vaughan_interval (U A B k : ℕ) (z : ℝ)
    (hAB : A ≤ B) (hU : 1 ≤ U) (hk : 1 ≤ k) (hz : (A : ℝ)/k ≤ z) :
    max 1 (A/((U+1)*k)) ≤ vaughan_two_power_compact_strictMobiusCutoffLength (B/((U+1)*k)) U z ∨
      vaughan_two_power_compact_strictMobiusCutoffLength (B/((U+1)*k)) U z = 0 := by
  let N : ℕ := A/((U+1)*k)
  let Y : ℕ := B/((U+1)*k)
  let X : ℕ := vaughan_two_power_compact_strictMobiusCutoffLength Y U z
  change max 1 N ≤ X ∨ X=0
  by_cases hX : X=0
  · exact Or.inr hX
  · left
    have hXp : 1 ≤ X := by omega
    by_cases hN : 1 ≤ N
    · rw [max_eq_right hN]
      have hNY : N ≤ Y := Nat.div_le_div_right hAB
      have hkp : (0 : ℝ) < k := by exact_mod_cast hk
      have hUp : (0 : ℝ) < U := by exact_mod_cast hU
      have hNp : (0 : ℝ) < N := by exact_mod_cast hN
      have hNnat : N*((U+1)*k) ≤ A := Nat.div_mul_le_self A ((U+1)*k)
      have hNr : (N : ℝ)*(((U : ℝ)+1)*k) ≤ A := by exact_mod_cast hNnat
      have hAz : (A : ℝ) ≤ z*k := (div_le_iff₀ hkp).mp hz
      have hpos := mul_pos hNp hkp
      have hNcut : (N : ℝ)*U < z := by nlinarith
      have hceil : N < ⌈z/(U : ℝ)⌉₊ := Nat.lt_ceil.mpr ((lt_div_iff₀ hUp).mpr hNcut)
      have hNpred : N ≤ ⌈z/(U : ℝ)⌉₊-1 := by omega
      exact le_min hNY hNpred
    · have hNnonneg : 0 ≤ N := Nat.zero_le N
      have hNzero : N=0 := by omega
      simpa [hNzero] using hXp

lemma vaughan_two_power_tp_vaughan_odd_mobius_two_power_integral_upper (U A B k : ℕ) (X L T a b s t : ℝ)
    (hAB : A ≤ B) (hU : 1 ≤ U) (hk : 1 ≤ k) (hYX : (B/(U+1) : ℕ) ≤ X)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs0 : 1/2 < s) (hs1 : s ≤ 1) (ht0 : 1/2 < t) (ht1 : t ≤ 1)
    (hM : ∀ v : ℝ, 1 ≤ v → v ≤ X →
      |∑ r∈Icc 1 ⌊v⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤
        a*(L/v)^(1-s)+b*(T/v)^(1-t)) :
    (∫ z in ((A : ℝ)/k)..((B : ℝ)/k),
      vaughan_two_power_tp_twoPowerStrictMobiusEnergy 2 (B/((U+1)*k)) U z) ≤
      (((B : ℝ)-A)/k)*vaughan_two_power_tp_twoPowerCoprimeEnergyPolynomial 2 a b s t
        ((L/(max 1 (A/((U+1)*k)) : ℕ))^(1-s))
        ((T/(max 1 (A/((U+1)*k)) : ℕ))^(1-t)) := by
  let F : ℝ := vaughan_two_power_tp_twoPowerCoprimeEnergyPolynomial 2 a b s t
    ((L/(max 1 (A/((U+1)*k)) : ℕ))^(1-s))
    ((T/(max 1 (A/((U+1)*k)) : ℕ))^(1-t))
  have hlr : (A : ℝ)/k ≤ (B : ℝ)/k :=
    div_le_div_of_nonneg_right (by exact_mod_cast hAB) (Nat.cast_nonneg k)
  have hi := vaughan_two_power_mobius_sigma_cutoff_quadratic_interval_integrable 2 (B/((U+1)*k))
    (U : ℝ) ((A : ℝ)/k) ((B : ℝ)/k)
  change IntervalIntegrable (fun z => vaughan_two_power_tp_twoPowerStrictMobiusEnergy 2 (B/((U+1)*k)) U z)
    volume ((A : ℝ)/k) ((B : ℝ)/k) at hi
  have hY : B/((U+1)*k) ≤ B/(U+1) := by
    rw [← Nat.div_div_eq_div_mul]
    exact Nat.div_le_self _ _
  have hYr : (B/((U+1)*k) : ℕ) ≤ X := le_trans (by exact_mod_cast hY) hYX
  have hbound := intervalIntegral.integral_mono_on hlr hi
    (intervalIntegrable_const (c := F)) (fun z hz =>
      vaughan_two_power_tp_strict_mobius_two_power_energy_upper_of_lower 2 (B/((U+1)*k))
        (max 1 (A/((U+1)*k))) X L T a b s t U z (by norm_num) (le_max_left _ _) hYr
        hL hT ha hb hs0 hs1 ht0 ht1 (by exact_mod_cast hU)
        (vaughan_two_power_tp_two_power_strict_cutoff_length_lower_on_vaughan_interval U A B k z hAB hU hk hz.1) hM)
  apply hbound.trans_eq
  rw [intervalIntegral.integral_const]
  dsimp [F]
  ring

theorem vaughan_two_power_tp_actual_vaughan_odd_mobius_two_power_energy_polynomial_upper
    (U A B : ℕ) (X L T a b s t : ℝ)
    (hAB : A ≤ B) (hhalf : B ≤ 2*A) (hU : 1 ≤ U) (hYX : (B/(U+1) : ℕ) ≤ X)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs0 : 1/2 < s) (hs1 : s ≤ 1) (ht0 : 1/2 < t) (ht1 : t ≤ 1)
    (hM : ∀ v : ℝ, 1 ≤ v → v ≤ X →
      |∑ r∈Icc 1 ⌊v⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤
        a*(L/v)^(1-s)+b*(T/v)^(1-t)) :
    (∑ m∈Ioc A B, if Nat.Coprime m 2 then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0) ≤
      (4/Real.pi^2)*((B : ℝ)-A)*
        (∑ k∈Icc 1 (B/(U+1)), if Nat.Coprime k 2 then
          vaughan_two_power_tp_twoPowerCoprimeEnergyPolynomial 2 a b s t
            ((L/(max 1 (A/((U+1)*k)) : ℕ))^(1-s))
            ((T/(max 1 (A/((U+1)*k)) : ℕ))^(1-t))/k else 0) +
      (107/10 : ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := by
  let F : ℕ → ℝ := fun k => vaughan_two_power_tp_twoPowerCoprimeEnergyPolynomial 2 a b s t
    ((L/(max 1 (A/((U+1)*k)) : ℕ))^(1-s))
    ((T/(max 1 (A/((U+1)*k)) : ℕ))^(1-t))
  let I : ℕ → ℝ := fun k => ∫ z in ((A : ℝ)/k)..((B : ℝ)/k),
    vaughan_two_power_tp_twoPowerStrictMobiusEnergy 2 (B/((U+1)*k)) U z
  let eps : ℝ := (107/10 : ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ))
  have hbase := actual_vaughan_odd_mobius_quadratic_integral_upper U A B hAB hhalf
  change (∑ m∈Ioc A B, if Nat.Coprime m 2 then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0) ≤
    (4/Real.pi^2)*(∑ k∈Icc 1 (B/(U+1)), if Nat.Coprime k 2 then I k else 0)+eps at hbase
  have hsum : (∑ k∈Icc 1 (B/(U+1)), if Nat.Coprime k 2 then I k else 0) ≤
      ((B : ℝ)-A)*(∑ k∈Icc 1 (B/(U+1)), if Nat.Coprime k 2 then F k/k else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hkI
    by_cases hk2 : Nat.Coprime k 2
    · rw [if_pos hk2,if_pos hk2]
      have hi := vaughan_two_power_tp_vaughan_odd_mobius_two_power_integral_upper U A B k X L T a b s t hAB hU
        (Finset.mem_Icc.mp hkI).1 hYX hL hT ha hb hs0 hs1 ht0 ht1 hM
      exact hi.trans_eq (by dsimp only [F]; ring)
    · simp only [if_neg hk2,mul_zero,le_refl]
  have hmain := mul_le_mul_of_nonneg_left hsum (show 0 ≤ (4 : ℝ)/Real.pi^2 by positivity)
  apply hbase.trans ((add_le_add hmain (le_refl eps)).trans_eq ?_)
  dsimp only [F,eps]
  ring
theorem actual_vaughan_odd_mobius_two_power_energy_upper_complete
    (U A B : ℕ) (X L T a b s t : ℝ)
    (hAB : A ≤ B) (hhalf : B ≤ 2*A) (hU : 1 ≤ U) (hYX : (B/(U+1) : ℕ) ≤ X)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs0 : 1/2 < s) (hs1 : s ≤ 1) (ht0 : 1/2 < t) (ht1 : t ≤ 1)
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
    let P : ℕ → ℝ := fun k => (L/(max 1 (A/((U+1)*k)) : ℕ))^(1-s)
    let Z : ℕ → ℝ := fun k => (T/(max 1 (A/((U+1)*k)) : ℕ))^(1-t)
    (∑ m∈Ioc A B, if Nat.Coprime m 2 then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0) ≤
      (4/Real.pi^2)*((B : ℝ)-A)*
        (∑ k∈Icc 1 (B/(U+1)), if Nat.Coprime k 2 then
          (a^2*(P k)^2*(R s)^2*C s s + 2*a*b*(P k)*(Z k)*R s*R t*C s t +
            b^2*(Z k)^2*(R t)^2*C t t)/k else 0) +
      (107/10 : ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := by
  exact vaughan_two_power_tp_actual_vaughan_odd_mobius_two_power_energy_polynomial_upper U A B X L T a b s t
    hAB hhalf hU hYX hL hT ha hb hs0 hs1 ht0 ht1 hM

end Helfgott
end

open Helfgott Finset Nat Real ArithmeticFunction MeasureTheory
open scoped BigOperators Classical Interval
theorem solution 
    (U A B : ℕ) (X L T a b s t : ℝ)
    (hAB : A ≤ B) (hhalf : B ≤ 2*A) (hU : 1 ≤ U) (hYX : (B/(U+1) : ℕ) ≤ X)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs0 : 1/2 < s) (hs1 : s ≤ 1) (ht0 : 1/2 < t) (ht1 : t ≤ 1)
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
    let P : ℕ → ℝ := fun k => (L/(max 1 (A/((U+1)*k)) : ℕ))^(1-s)
    let Z : ℕ → ℝ := fun k => (T/(max 1 (A/((U+1)*k)) : ℕ))^(1-t)
    (∑ m∈Ioc A B, if Nat.Coprime m 2 then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0) ≤
      (4/Real.pi^2)*((B : ℝ)-A)*
        (∑ k∈Icc 1 (B/(U+1)), if Nat.Coprime k 2 then
          (a^2*(P k)^2*(R s)^2*C s s + 2*a*b*(P k)*(Z k)*R s*R t*C s t +
            b^2*(Z k)^2*(R t)^2*C t t)/k else 0) +
      (107/10 : ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := Helfgott.actual_vaughan_odd_mobius_two_power_energy_upper_complete U A B X L T a b s t hAB hhalf hU hYX hL hT ha hb hs0 hs1 ht0 ht1 hM
#print axioms solution
