-- Prove2me | solution 1 for Helfgott.actual_vaughan_odd_mobius_rankin_energy_log_decay_upper
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T04:26:08.678302+00:00
-- url     : https://prove2.me/submissions/bbafd979-8d78-4e5c-9214-44b0a6fb4342

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Mathlib.Algebra.Order.Floor.Semiring
import Theorems.Thm_Helfgott_mobius_sigma_coprime_divisor_energy_log_decay_upper
import Theorems.Thm_Helfgott_actual_vaughan_odd_mobius_quadratic_integral_upper
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

noncomputable def vaughan_odd_mobius_rankin_energy_compact_strictMobiusCutoffLength (Y : ℕ) (U z : ℝ) : ℕ :=
  min Y (⌈z/U⌉₊-1)

lemma vaughan_odd_mobius_rankin_energy_compact_strict_mobius_cutoff_divisor_iff (Y d a : ℕ) (U z : ℝ)
    (hd : 1 ≤ d) (ha : 1 ≤ a) (hU : 0 < U) :
    (a ≤ Y/d ∧ U*(d*a : ℕ)<z) ↔ a ≤ vaughan_odd_mobius_rankin_energy_compact_strictMobiusCutoffLength Y U z/d := by
  have hceil : d*a<⌈z/U⌉₊ ↔ U*(d*a : ℕ)<z := by
    rw [Nat.lt_ceil, lt_div_iff₀ hU]
    rw [mul_comm]
  have hcut : U*(d*a : ℕ)<z ↔ d*a ≤ ⌈z/U⌉₊-1 := by
    have hda : 1 ≤ d*a := Nat.mul_le_mul hd ha
    rw [← hceil]
    omega
  rw [hcut, Nat.le_div_iff_mul_le (by omega), Nat.le_div_iff_mul_le (by omega)]
  unfold vaughan_odd_mobius_rankin_energy_compact_strictMobiusCutoffLength
  rw [le_min_iff]
  simp only [Nat.mul_comm]

lemma vaughan_odd_mobius_rankin_energy_compact_strict_mobius_cutoff_partial_sum_eq (f : ℕ → ℝ) (q Y d : ℕ) (U z : ℝ)
    (hd : 1 ≤ d) (hU : 0 < U) :
    (∑ a∈Icc 1 (Y/d), if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then f a else 0) =
      ∑ a∈Icc 1 (vaughan_odd_mobius_rankin_energy_compact_strictMobiusCutoffLength Y U z/d), if Nat.Coprime a (d*q) then f a else 0 := by
  have hfilter : (Icc 1 (Y/d)).filter (fun a => U*(d*a : ℕ)<z) =
      Icc 1 (vaughan_odd_mobius_rankin_energy_compact_strictMobiusCutoffLength Y U z/d) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro h
      exact ⟨h.1.1,(vaughan_odd_mobius_rankin_energy_compact_strict_mobius_cutoff_divisor_iff Y d a U z hd h.1.1 hU).mp ⟨h.1.2,h.2⟩⟩
    · intro h
      have hi := (vaughan_odd_mobius_rankin_energy_compact_strict_mobius_cutoff_divisor_iff Y d a U z hd h.1 hU).mpr h.2
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

theorem vaughan_odd_mobius_rankin_energy_compact_mobius_sigma_coprime_strict_cutoff_energy_eq (q Y : ℕ) (U z : ℝ) (hU : 0 < U) :
    let X : ℕ := min Y (⌈z/U⌉₊-1)
    let sigma : ℕ → ℝ := fun n => ∏ p∈n.primeFactors, ((p : ℝ)+1)
    (∑ d∈Icc 1 Y, if Nat.Coprime d q then |((moebius d : ℤ) : ℝ)|/(sigma d)^2 *
      (∑ a∈Icc 1 (Y/d), if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then
        ((moebius a : ℤ) : ℝ)/sigma a else 0)^2 else 0) =
    (∑ d∈Icc 1 X, if Nat.Coprime d q then |((moebius d : ℤ) : ℝ)|/(sigma d)^2 *
      (∑ a∈Icc 1 (X/d), if Nat.Coprime a (d*q) then
        ((moebius a : ℤ) : ℝ)/sigma a else 0)^2 else 0) := by
  let X := vaughan_odd_mobius_rankin_energy_compact_strictMobiusCutoffLength Y U z
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
    rw [vaughan_odd_mobius_rankin_energy_compact_strict_mobius_cutoff_partial_sum_eq f q Y d U z (Finset.mem_Icc.mp hd).1 hU]
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

noncomputable def vaughan_odd_mobius_rankin_energy_compact_rankinSingleZetaConstant (s : ℝ) : ℝ :=
  ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/
    (∑' n : ℕ,(n : ℝ)^(-3 : ℝ))

noncomputable def vaughan_odd_mobius_rankin_energy_compact_rankinCoupledZetaConstant (s t : ℝ) : ℝ :=
  ((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
    ((∑' n : ℕ,(n : ℝ)^(-3 : ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4 : ℝ)))

noncomputable def vaughan_odd_mobius_rankin_energy_compact_rankinSharpCoprimeFactor (q : ℕ) (s : ℝ) : ℝ :=
  ∏ p ∈ q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-s))

lemma vaughan_odd_mobius_rankin_energy_compact_rankin_single_zeta_constant_nonneg (s : ℝ) : 0 ≤ vaughan_odd_mobius_rankin_energy_compact_rankinSingleZetaConstant s := by
  unfold vaughan_odd_mobius_rankin_energy_compact_rankinSingleZetaConstant
  exact div_nonneg (mul_nonneg
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)))
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))

lemma vaughan_odd_mobius_rankin_energy_compact_rankin_sharp_factor_pos (q : ℕ) (s : ℝ) (hs : 0 < s) :
    0 < vaughan_odd_mobius_rankin_energy_compact_rankinSharpCoprimeFactor q s := by
  unfold vaughan_odd_mobius_rankin_energy_compact_rankinSharpCoprimeFactor
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have ht : (p : ℝ)^(-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hmul := mul_pos (by linarith : (0 : ℝ) < p) (by linarith : 0 < 1-(p : ℝ)^(-s))
  exact div_pos (by linarith) (by nlinarith)


noncomputable def vaughan_odd_mobius_rankin_energy_compact_mobiusSigmaDivisorEnergy (q Y : ℕ) : ℝ :=
  ∑ d∈Icc 1 Y, if Nat.Coprime d q then
    |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors, ((p : ℝ)+1))^2 *
      (∑ a∈Icc 1 (Y/d), if Nat.Coprime a (d*q) then
        ((moebius a : ℤ) : ℝ)/(∏ p∈a.primeFactors, ((p : ℝ)+1)) else 0)^2 else 0

noncomputable def vaughan_odd_mobius_rankin_energy_compact_mobiusSigmaStrictEnergy (q Y : ℕ) (U z : ℝ) : ℝ :=
  ∑ d∈Icc 1 Y, if Nat.Coprime d q then
    |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors, ((p : ℝ)+1))^2 *
      (∑ a∈Icc 1 (Y/d), if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then
        ((moebius a : ℤ) : ℝ)/(∏ p∈a.primeFactors, ((p : ℝ)+1)) else 0)^2 else 0

noncomputable def vaughan_odd_mobius_rankin_energy_compact_rankinEnergyPolynomial (q : ℕ) (c s P : ℝ) : ℝ :=
  c^2*(vaughan_odd_mobius_rankin_energy_compact_rankinSingleZetaConstant 1*vaughan_odd_mobius_rankin_energy_compact_rankinSharpCoprimeFactor q 1)^2*vaughan_odd_mobius_rankin_energy_compact_rankinCoupledZetaConstant 1 1 +
    2*c*P*(vaughan_odd_mobius_rankin_energy_compact_rankinSingleZetaConstant 1*vaughan_odd_mobius_rankin_energy_compact_rankinSharpCoprimeFactor q 1)*
      (vaughan_odd_mobius_rankin_energy_compact_rankinSingleZetaConstant s*vaughan_odd_mobius_rankin_energy_compact_rankinSharpCoprimeFactor q s)*vaughan_odd_mobius_rankin_energy_compact_rankinCoupledZetaConstant 1 s +
    P^2*(vaughan_odd_mobius_rankin_energy_compact_rankinSingleZetaConstant s*vaughan_odd_mobius_rankin_energy_compact_rankinSharpCoprimeFactor q s)^2*vaughan_odd_mobius_rankin_energy_compact_rankinCoupledZetaConstant s s

lemma vaughan_odd_mobius_rankin_energy_compact_rankin_coupled_zeta_constant_nonneg (s t : ℝ) : 0 ≤ vaughan_odd_mobius_rankin_energy_compact_rankinCoupledZetaConstant s t := by
  unfold vaughan_odd_mobius_rankin_energy_compact_rankinCoupledZetaConstant
  exact div_nonneg (mul_nonneg (mul_nonneg
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)))
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)))
    (mul_nonneg (sq_nonneg _) (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)))

lemma vaughan_odd_mobius_rankin_energy_compact_rankin_energy_polynomial_nonneg (q : ℕ) (c s P : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hP : 0 ≤ P) :
    0 ≤ vaughan_odd_mobius_rankin_energy_compact_rankinEnergyPolynomial q c s P := by
  have hK1 := vaughan_odd_mobius_rankin_energy_compact_rankin_single_zeta_constant_nonneg 1
  have hKs := vaughan_odd_mobius_rankin_energy_compact_rankin_single_zeta_constant_nonneg s
  have hJ1 := (vaughan_odd_mobius_rankin_energy_compact_rankin_sharp_factor_pos q 1 (by norm_num)).le
  have hJs := (vaughan_odd_mobius_rankin_energy_compact_rankin_sharp_factor_pos q s hs).le
  have hC11 := vaughan_odd_mobius_rankin_energy_compact_rankin_coupled_zeta_constant_nonneg 1 1
  have hC1s := vaughan_odd_mobius_rankin_energy_compact_rankin_coupled_zeta_constant_nonneg 1 s
  have hCss := vaughan_odd_mobius_rankin_energy_compact_rankin_coupled_zeta_constant_nonneg s s
  unfold vaughan_odd_mobius_rankin_energy_compact_rankinEnergyPolynomial
  positivity

lemma vaughan_odd_mobius_rankin_energy_compact_rankin_energy_polynomial_mono (q : ℕ) (c s P T : ℝ)
    (hc : 0 ≤ c) (hs : 0 < s) (hP : 0 ≤ P) (hPT : P ≤ T) :
    vaughan_odd_mobius_rankin_energy_compact_rankinEnergyPolynomial q c s P ≤ vaughan_odd_mobius_rankin_energy_compact_rankinEnergyPolynomial q c s T := by
  have hK1 := vaughan_odd_mobius_rankin_energy_compact_rankin_single_zeta_constant_nonneg 1
  have hKs := vaughan_odd_mobius_rankin_energy_compact_rankin_single_zeta_constant_nonneg s
  have hJ1 := (vaughan_odd_mobius_rankin_energy_compact_rankin_sharp_factor_pos q 1 (by norm_num)).le
  have hJs := (vaughan_odd_mobius_rankin_energy_compact_rankin_sharp_factor_pos q s hs).le
  have hC11 := vaughan_odd_mobius_rankin_energy_compact_rankin_coupled_zeta_constant_nonneg 1 1
  have hC1s := vaughan_odd_mobius_rankin_energy_compact_rankin_coupled_zeta_constant_nonneg 1 s
  have hCss := vaughan_odd_mobius_rankin_energy_compact_rankin_coupled_zeta_constant_nonneg s s
  have hsquare : P^2 ≤ T^2 := (sq_le_sq₀ hP (hP.trans hPT)).mpr hPT
  unfold vaughan_odd_mobius_rankin_energy_compact_rankinEnergyPolynomial
  have hcross := mul_le_mul_of_nonneg_right hPT
    (show 0 ≤ 2*c*(vaughan_odd_mobius_rankin_energy_compact_rankinSingleZetaConstant 1*vaughan_odd_mobius_rankin_energy_compact_rankinSharpCoprimeFactor q 1)*
      (vaughan_odd_mobius_rankin_energy_compact_rankinSingleZetaConstant s*vaughan_odd_mobius_rankin_energy_compact_rankinSharpCoprimeFactor q s)*vaughan_odd_mobius_rankin_energy_compact_rankinCoupledZetaConstant 1 s by positivity)
  have htail := mul_le_mul_of_nonneg_right hsquare
    (show 0 ≤ (vaughan_odd_mobius_rankin_energy_compact_rankinSingleZetaConstant s*vaughan_odd_mobius_rankin_energy_compact_rankinSharpCoprimeFactor q s)^2*vaughan_odd_mobius_rankin_energy_compact_rankinCoupledZetaConstant s s by positivity)
  nlinarith

lemma vaughan_odd_mobius_rankin_energy_compact_mobius_sigma_strict_energy_eq_divisor_energy (q Y : ℕ) (U z : ℝ) (hU : 0 < U) :
    vaughan_odd_mobius_rankin_energy_compact_mobiusSigmaStrictEnergy q Y U z =
      vaughan_odd_mobius_rankin_energy_compact_mobiusSigmaDivisorEnergy q (vaughan_odd_mobius_rankin_energy_compact_strictMobiusCutoffLength Y U z) :=
  vaughan_odd_mobius_rankin_energy_compact_mobius_sigma_coprime_strict_cutoff_energy_eq q Y U z hU

lemma vaughan_odd_mobius_rankin_energy_compact_mobius_sigma_strict_energy_rankin_upper_of_lower
    (hdecay : ∀ x : ℝ, 11815 ≤ x →
      |∑ a∈Icc 1 ⌊x⌋₊, ((moebius a : ℤ) : ℝ)/(a : ℝ)| ≤ (3/100)/Real.log x)
    (q Y Z L : ℕ) (s U z : ℝ) (hq : 1 ≤ q) (hZ : 1 ≤ Z) (hL : 11815 ≤ L)
    (hs0 : 1/2 < s) (hs1 : s ≤ 1) (hU : 0 < U)
    (hlower : Z ≤ vaughan_odd_mobius_rankin_energy_compact_strictMobiusCutoffLength Y U z ∨ vaughan_odd_mobius_rankin_energy_compact_strictMobiusCutoffLength Y U z = 0) :
    vaughan_odd_mobius_rankin_energy_compact_mobiusSigmaStrictEnergy q Y U z ≤
      vaughan_odd_mobius_rankin_energy_compact_rankinEnergyPolynomial q ((3/100)/Real.log (L : ℝ)) s (((2*(L : ℝ))/Z)^(1-s)) := by
  have hLp : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hlog : 0 < Real.log (L : ℝ) := Real.log_pos hLp
  have hc : 0 ≤ (3/100 : ℝ)/Real.log (L : ℝ) := by positivity
  rw [vaughan_odd_mobius_rankin_energy_compact_mobius_sigma_strict_energy_eq_divisor_energy q Y U z hU]
  rcases hlower with hlower | hzero
  · have hX : 1 ≤ vaughan_odd_mobius_rankin_energy_compact_strictMobiusCutoffLength Y U z := hZ.trans hlower
    have hZp : (0 : ℝ) < Z := by exact_mod_cast hZ
    have hZX : (Z : ℝ) ≤ vaughan_odd_mobius_rankin_energy_compact_strictMobiusCutoffLength Y U z := by exact_mod_cast hlower
    have hdiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2*(L : ℝ)) hZp hZX
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (2*(L : ℝ))/vaughan_odd_mobius_rankin_energy_compact_strictMobiusCutoffLength Y U z)
      hdiv (by linarith : 0 ≤ 1-s)
    have henergy := mobius_sigma_coprime_divisor_energy_log_decay_upper hdecay
      q (vaughan_odd_mobius_rankin_energy_compact_strictMobiusCutoffLength Y U z) L s hq hX hL hs0 hs1
    change vaughan_odd_mobius_rankin_energy_compact_mobiusSigmaDivisorEnergy q (vaughan_odd_mobius_rankin_energy_compact_strictMobiusCutoffLength Y U z) ≤
      vaughan_odd_mobius_rankin_energy_compact_rankinEnergyPolynomial q ((3/100)/Real.log (L : ℝ)) s
        (((2*(L : ℝ))/vaughan_odd_mobius_rankin_energy_compact_strictMobiusCutoffLength Y U z)^(1-s)) at henergy
    exact henergy.trans (vaughan_odd_mobius_rankin_energy_compact_rankin_energy_polynomial_mono q _ s _ _ hc (by linarith) (by positivity) hpow)
  · rw [hzero]
    have hn := vaughan_odd_mobius_rankin_energy_compact_rankin_energy_polynomial_nonneg q ((3/100)/Real.log (L : ℝ)) s
      (((2*(L : ℝ))/Z)^(1-s)) hc (by linarith) (by positivity)
    simpa [vaughan_odd_mobius_rankin_energy_compact_mobiusSigmaDivisorEnergy] using hn
end Helfgott
end

section
set_option autoImplicit false
open Finset
open scoped BigOperators Classical
namespace Helfgott

theorem vaughan_odd_mobius_rankin_energy_finite_positive_divisor_reindex (B : ℕ) (F : ℕ → ℕ → ℝ) :
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

lemma vaughan_odd_mobius_rankin_energy_finite_positive_multiples_reindex (Y d : ℕ) (hd : 1 ≤ d) (F : ℕ→ℝ) :
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

lemma vaughan_odd_mobius_rankin_energy_floorRoot_two_eq_one_iff_squarefree (n : ℕ) (hn : n ≠ 0) :
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

lemma vaughan_odd_mobius_rankin_energy_moebius_divisor_sum (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors,moebius d) = if n=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa [ArithmeticFunction.one_apply,hn] using h

theorem vaughan_odd_mobius_rankin_energy_moebius_square_divisor_expansion (n : ℕ) (hn : n ≠ 0) :
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
  rw [←Finset.sum_filter,he,vaughan_odd_mobius_rankin_energy_moebius_divisor_sum _ hroot0,moebius_sq]
  simp only [vaughan_odd_mobius_rankin_energy_floorRoot_two_eq_one_iff_squarefree n hn]

lemma vaughan_odd_mobius_rankin_energy_coprime_moebius_divisor_expansion (q n : ℕ) (hq : q ≠ 0) :
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
  rw [←Finset.sum_filter,he,vaughan_odd_mobius_rankin_energy_moebius_divisor_sum _ (Nat.gcd_ne_zero_right hq)]

theorem vaughan_odd_mobius_rankin_energy_squarefree_coprime_pointwise_expansion (q n : ℕ) (hq : q ≠ 0) (hn : n ≠ 0) :
    (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0)*
      (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) := by
  have hcop : (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) =
      if Nat.Coprime n q then 1 else 0 := by
    exact_mod_cast vaughan_odd_mobius_rankin_energy_coprime_moebius_divisor_expansion q n hq
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
    exact_mod_cast vaughan_odd_mobius_rankin_energy_moebius_square_divisor_expansion n hn
  · simp [h]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

lemma vaughan_odd_mobius_rankin_energy_finite_coprime_pair_mobius_reindex (Y : ℕ) (F : ℕ→ℕ→ℝ) :
    (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,if Nat.Coprime r t then F r t else 0)=
      ∑ d∈Finset.Icc 1 Y,((moebius d : ℤ) : ℝ)*
        (∑ a∈Finset.Icc 1 (Y/d),∑ b∈Finset.Icc 1 (Y/d),F (d*a) (d*b)) := by
  have hpoint (r t : ℕ) (hr : 1 ≤ r) :
      (if Nat.Coprime r t then F r t else 0)=
        ∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ)*F r t else 0 := by
    have hc : (∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ) else 0)=
        if Nat.Coprime r t then (1:ℝ) else 0 := by
      have h := vaughan_odd_mobius_rankin_energy_coprime_moebius_divisor_expansion r t (by omega)
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
    rw [Finset.sum_congr rfl hr,vaughan_odd_mobius_rankin_energy_finite_positive_divisor_reindex Y
      (fun d a => if d∣t then ((moebius d : ℤ) : ℝ)*F (d*a) t else 0)]
  rw [Finset.sum_congr rfl (fun t ht => hdiv t),Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [vaughan_odd_mobius_rankin_energy_finite_positive_multiples_reindex Y d (Finset.mem_Icc.mp hd).1
    (fun t => ((moebius d : ℤ) : ℝ)*F (d*a) t),Finset.mul_sum]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

noncomputable def vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight (n : ℕ) : ℝ :=
  ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))

lemma vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight_mul (d a : ℕ) :
    vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight (d*a)=if Nat.Coprime d a then vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight d*vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight a else 0 := by
  by_cases hc : Nat.Coprime d a
  · rw [if_pos hc]
    have hS : (∏ p∈(d*a).primeFactors,((p : ℝ)+1))=
        (∏ p∈d.primeFactors,((p : ℝ)+1))*(∏ p∈a.primeFactors,((p : ℝ)+1)) := by
      rw [hc.primeFactors_mul,Finset.prod_union hc.disjoint_primeFactors]
    dsimp [vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight]
    rw [isMultiplicative_moebius.map_mul_of_coprime hc,Int.cast_mul,hS]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · rw [if_neg hc]
    have hsf : ¬Squarefree (d*a) := fun h => hc (Nat.coprime_of_squarefree_mul h)
    simp [vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight,moebius_eq_zero_of_not_squarefree hsf]

lemma vaughan_odd_mobius_rankin_energy_moebius_real_cube_eq_self (d : ℕ) : ((moebius d : ℤ) : ℝ)^3=((moebius d : ℤ) : ℝ) := by
  by_cases hd : moebius d=0
  · rw [hd];norm_num
  · obtain h | h := moebius_ne_zero_iff_eq_or.mp hd <;> rw [h] <;> norm_num

lemma vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight_moebius_square (d : ℕ) :
    ((moebius d : ℤ) : ℝ)*(vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight d)^2=
      ((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2 := by
  dsimp [vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight]
  rw [div_pow]
  calc
    _=((moebius d : ℤ) : ℝ)^3/(∏ p∈d.primeFactors,((p : ℝ)+1))^2 := by ring
    _=_ := by rw [vaughan_odd_mobius_rankin_energy_moebius_real_cube_eq_self]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma vaughan_odd_mobius_rankin_energy_mobius_sigma_pair_common_divisor (d a b q : ℕ) :
    ((moebius d : ℤ) : ℝ)*
      (if Nat.Coprime (d*a) q ∧ Nat.Coprime (d*b) q then
        vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight (d*a)*vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight (d*b) else 0)=
      if Nat.Coprime d q then
        (((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (if Nat.Coprime a (d*q) then vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight a else 0)*
          (if Nat.Coprime b (d*q) then vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight b else 0) else 0 := by
  have hfactor := vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight_moebius_square d
  rw [vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight_mul,vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight_mul]
  simp only [Nat.coprime_mul_iff_left,Nat.coprime_mul_iff_right]
  have hca : Nat.Coprime a d ↔ Nat.Coprime d a := Nat.coprime_comm
  have hcb : Nat.Coprime b d ↔ Nat.Coprime d b := Nat.coprime_comm
  split_ifs <;> simp_all only [hca,hcb,mul_zero,zero_mul] <;> try aesop
  linear_combination (vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight a*vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight b)*hfactor

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma vaughan_odd_mobius_rankin_energy_mobius_sigma_weighted_pair_common_divisor (d a b q : ℕ) (h : ℕ→ℝ) :
    ((moebius d : ℤ) : ℝ)*
      (if Nat.Coprime (d*a) q ∧ Nat.Coprime (d*b) q then
        (vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight (d*a)*h (d*a))*(vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight (d*b)*h (d*b)) else 0)=
      if Nat.Coprime d q then
        (((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (if Nat.Coprime a (d*q) then vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight a*h (d*a) else 0)*
          (if Nat.Coprime b (d*q) then vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight b*h (d*b) else 0) else 0 := by
  have hp := vaughan_odd_mobius_rankin_energy_mobius_sigma_pair_common_divisor d a b q
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

theorem vaughan_odd_mobius_rankin_energy_mobius_sigma_weighted_coprime_pair_square_decomposition (q Y : ℕ) (h : ℕ→ℝ) :
    let f : ℕ→ℝ := fun n => ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))
    (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then (f r*h r)*(f t*h t) else 0)=
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then f a*h (d*a) else 0)^2 else 0 := by
  change (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then (vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight r*h r)*(vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight t*h t) else 0)=_
  have hleft : (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then (vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight r*h r)*(vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight t*h t) else 0)=
      ∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,if Nat.Coprime r t then
        (if Nat.Coprime r q ∧ Nat.Coprime t q then (vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight r*h r)*(vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight t*h t) else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t ht
    split_ifs <;> aesop
  rw [hleft,vaughan_odd_mobius_rankin_energy_finite_coprime_pair_mobius_reindex]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  have he : (∑ a∈Finset.Icc 1 (Y/d),∑ b∈Finset.Icc 1 (Y/d),
      ((moebius d : ℤ) : ℝ)*(if Nat.Coprime (d*a) q ∧ Nat.Coprime (d*b) q then
        (vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight (d*a)*h (d*a))*(vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight (d*b)*h (d*b)) else 0))=
      ∑ a∈Finset.Icc 1 (Y/d),∑ b∈Finset.Icc 1 (Y/d),
        if Nat.Coprime d q then (((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (if Nat.Coprime a (d*q) then vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight a*h (d*a) else 0)*
          (if Nat.Coprime b (d*q) then vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight b*h (d*b) else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    exact Finset.sum_congr rfl (fun b hb => vaughan_odd_mobius_rankin_energy_mobius_sigma_weighted_pair_common_divisor d a b q h)
  rw [he]
  by_cases hc : Nat.Coprime d q
  · rw [if_pos hc]
    simp only [if_pos hc]
    simp_rw [←Finset.mul_sum]
    rw [←Finset.sum_mul,←Finset.mul_sum]
    change _=(((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
      (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight a*h (d*a) else 0)^2
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

theorem vaughan_odd_mobius_rankin_energy_mobius_sigma_weighted_coprime_pair_quadratic_bound (q Y : ℕ) (h : ℕ→ℝ) :
    let f : ℕ→ℝ := fun n => ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))
    |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then (f r*h r)*(f t*h t) else 0| ≤
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then f a*h (d*a) else 0)^2 else 0 := by
  dsimp only
  rw [vaughan_odd_mobius_rankin_energy_mobius_sigma_weighted_coprime_pair_square_decomposition]
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

theorem vaughan_odd_mobius_rankin_energy_mobius_sigma_cutoff_coprime_pair_quadratic_bound (q Y : ℕ) (U z : ℝ) :
    let f : ℕ→ℝ := fun n => ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))
    |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q ∧ U*r<z ∧ U*t<z then f r*f t else 0| ≤
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then f a else 0)^2 else 0 := by
  let h : ℕ→ℝ := fun n => if U*n<z then 1 else 0
  have hb := vaughan_odd_mobius_rankin_energy_mobius_sigma_weighted_coprime_pair_quadratic_bound q Y h
  dsimp only at hb ⊢
  have hleft : (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then
        (vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight r*h r)*(vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight t*h t) else 0)=
      ∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
        if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q ∧ U*r<z ∧ U*t<z then
          vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight r*vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight t else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t ht
    dsimp [h]
    split_ifs <;> simp_all <;> try linarith <;> aesop
  have hright (d : ℕ) : (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then
        vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight a*h (d*a) else 0)=
      ∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight a else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [h]
    split_ifs <;> simp_all <;> try linarith <;> aesop
  change |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
    if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then
      (vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight r*h r)*(vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight t*h t) else 0|≤_ at hb
  rw [hleft] at hb
  change |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
    if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q ∧ U*r<z ∧ U*t<z then
      vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight r*vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight t else 0|≤_
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

lemma vaughan_odd_mobius_rankin_energy_cutoff_indicator_interval_integrable (c a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => if c<x then (1:ℝ) else 0) volume a b := by
  have hm : Measurable (fun x : ℝ => if c<x then (1:ℝ) else 0) :=
    Measurable.ite measurableSet_Ioi measurable_const measurable_const
  apply (intervalIntegrable_const (c:=(1:ℝ))).mono_fun' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by dsimp only;split_ifs <;> norm_num)

lemma vaughan_odd_mobius_rankin_energy_cutoff_indicator_interval_integral (a b c : ℝ) (hab : a ≤ b) (hcb : c ≤ b) :
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
      (vaughan_odd_mobius_rankin_energy_cutoff_indicator_interval_integrable c a c) (vaughan_odd_mobius_rankin_energy_cutoff_indicator_interval_integrable c c b)
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

lemma vaughan_odd_mobius_rankin_energy_finite_coprime_cutoff_sum_measurable (S : Finset ℕ) (q : ℕ) (w c : ℕ→ℝ) :
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

lemma vaughan_odd_mobius_rankin_energy_finite_coprime_cutoff_sum_abs_bound (S : Finset ℕ) (q : ℕ) (w c : ℕ→ℝ) (z : ℝ) :
    |∑ a∈S,if Nat.Coprime a q ∧ c a<z then w a else 0|≤∑ a∈S,|w a| := by
  apply (abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a ha
  split_ifs
  · exact le_rfl
  · simp only [abs_zero]
    exact abs_nonneg _

lemma vaughan_odd_mobius_rankin_energy_finite_coprime_cutoff_square_interval_integrable (S : Finset ℕ) (q : ℕ) (w c : ℕ→ℝ) (l r : ℝ) :
    IntervalIntegrable (fun z : ℝ => (∑ a∈S,if Nat.Coprime a q ∧ c a<z then w a else 0)^2) volume l r := by
  have hm := (vaughan_odd_mobius_rankin_energy_finite_coprime_cutoff_sum_measurable S q w c).pow_const 2
  apply (intervalIntegrable_const (c:=(∑ a∈S,|w a|)^2)).mono_fun' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hb := vaughan_odd_mobius_rankin_energy_finite_coprime_cutoff_sum_abs_bound S q w c z
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

lemma vaughan_odd_mobius_rankin_energy_finite_interval_integrable_sum {ι : Type} (S : Finset ι) (f : ι→ℝ→ℝ) (l r : ℝ)
    (hf : ∀ i∈S,IntervalIntegrable (f i) volume l r) :
    IntervalIntegrable (fun z => ∑ i∈S,f i z) volume l r := by
  have he : (∑ i∈S,f i)=(fun z => ∑ i∈S,f i z) := by funext z;simp
  rw [←he]
  exact IntervalIntegrable.sum S hf

lemma vaughan_odd_mobius_rankin_energy_finite_filtered_cutoff_pair_interval_integrable (S T : Finset ℕ)
    (P : ℕ→ℕ→Prop) [∀ a b,Decidable (P a b)] (w c : ℕ→ℕ→ℝ) (l r : ℝ) :
    IntervalIntegrable (fun z => ∑ a∈S,∑ b∈T,if P a b ∧ c a b<z then w a b else 0) volume l r := by
  apply vaughan_odd_mobius_rankin_energy_finite_interval_integrable_sum
  intro a ha
  apply vaughan_odd_mobius_rankin_energy_finite_interval_integrable_sum
  intro b hb
  by_cases hP : P a b
  · have hi := (vaughan_odd_mobius_rankin_energy_cutoff_indicator_interval_integrable (c a b) l r).const_mul (w a b)
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

lemma vaughan_odd_mobius_rankin_energy_mobius_sigma_cutoff_pair_interval_integrable (q Y : ℕ) (U l r : ℝ) :
    IntervalIntegrable (fun z => ∑ a∈Finset.Icc 1 Y,∑ b∈Finset.Icc 1 Y,
      if Nat.Coprime a b ∧ Nat.Coprime a q ∧ Nat.Coprime b q ∧ U*a<z ∧ U*b<z then
        vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight a*vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight b else 0) volume l r := by
  have hi := vaughan_odd_mobius_rankin_energy_finite_filtered_cutoff_pair_interval_integrable (Finset.Icc 1 Y) (Finset.Icc 1 Y)
    (fun a b => Nat.Coprime a b ∧ Nat.Coprime a q ∧ Nat.Coprime b q)
    (fun a b => vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight a*vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight b) (fun a b => max (U*a) (U*b)) l r
  apply hi.congr
  intro z hz
  dsimp only
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp_all only [max_lt_iff] <;> aesop

lemma vaughan_odd_mobius_rankin_energy_mobius_sigma_cutoff_quadratic_interval_integrable (q Y : ℕ) (U l r : ℝ) :
    IntervalIntegrable (fun z => ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
      (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
        (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight a else 0)^2 else 0) volume l r := by
  apply vaughan_odd_mobius_rankin_energy_finite_interval_integrable_sum
  intro d hd
  by_cases hc : Nat.Coprime d q
  · have hi := (vaughan_odd_mobius_rankin_energy_finite_coprime_cutoff_square_interval_integrable (Finset.Icc 1 (Y/d)) (d*q)
        vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight (fun a => U*(d*a : ℕ)) l r).const_mul
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)
    simpa only [if_pos hc] using hi
  · simpa only [if_neg hc] using (intervalIntegrable_const (c:=(0:ℝ)) : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume l r)

theorem vaughan_odd_mobius_rankin_energy_mobius_sigma_cutoff_integral_quadratic_upper (q Y : ℕ) (U l r : ℝ) (hlr : l≤r) :
    (∫ z in l..r,∑ a∈Finset.Icc 1 Y,∑ b∈Finset.Icc 1 Y,
      if Nat.Coprime a b ∧ Nat.Coprime a q ∧ Nat.Coprime b q ∧ U*a<z ∧ U*b<z then
        vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight a*vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight b else 0)≤
      ∫ z in l..r,∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then vaughan_odd_mobius_rankin_energy_mobiusSigmaWeight a else 0)^2 else 0 := by
  apply intervalIntegral.integral_mono hlr
    (vaughan_odd_mobius_rankin_energy_mobius_sigma_cutoff_pair_interval_integrable q Y U l r)
    (vaughan_odd_mobius_rankin_energy_mobius_sigma_cutoff_quadratic_interval_integrable q Y U l r)
  intro z
  exact (le_abs_self _).trans (vaughan_odd_mobius_rankin_energy_mobius_sigma_cutoff_coprime_pair_quadratic_bound q Y U z)

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
open Finset Nat Real ArithmeticFunction MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma vaughan_odd_mobius_rankin_energy_strict_cutoff_length_lower_on_vaughan_interval (U A B k : ℕ) (z : ℝ)
    (hAB : A ≤ B) (hU : 1 ≤ U) (hk : 1 ≤ k) (hz : (A : ℝ)/k ≤ z) :
    max 1 (A/((U+1)*k)) ≤ vaughan_odd_mobius_rankin_energy_compact_strictMobiusCutoffLength (B/((U+1)*k)) U z ∨
      vaughan_odd_mobius_rankin_energy_compact_strictMobiusCutoffLength (B/((U+1)*k)) U z = 0 := by
  let N : ℕ := A/((U+1)*k)
  let Y : ℕ := B/((U+1)*k)
  let X : ℕ := vaughan_odd_mobius_rankin_energy_compact_strictMobiusCutoffLength Y U z
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

lemma vaughan_odd_mobius_rankin_energy_vaughan_odd_mobius_rankin_integral_upper (hdecay : ∀ x : ℝ, 11815 ≤ x →
      |∑ a∈Icc 1 ⌊x⌋₊, ((moebius a : ℤ) : ℝ)/(a : ℝ)| ≤ (3/100)/Real.log x) (U A B k L : ℕ) (s : ℝ)
    (hAB : A ≤ B) (hU : 1 ≤ U) (hk : 1 ≤ k) (hL : 11815 ≤ L)
    (hs0 : 1/2 < s) (hs1 : s ≤ 1)
 :
    (∫ z in ((A : ℝ)/k)..((B : ℝ)/k),
      vaughan_odd_mobius_rankin_energy_compact_mobiusSigmaStrictEnergy 2 (B/((U+1)*k)) U z) ≤
      (((B : ℝ)-A)/k)*vaughan_odd_mobius_rankin_energy_compact_rankinEnergyPolynomial 2 ((3/100)/Real.log (L : ℝ)) s
        (((2*(L : ℝ))/(max 1 (A/((U+1)*k)) : ℕ))^(1-s)) := by
  let T : ℝ := vaughan_odd_mobius_rankin_energy_compact_rankinEnergyPolynomial 2 ((3/100)/Real.log (L : ℝ)) s
    (((2*(L : ℝ))/(max 1 (A/((U+1)*k)) : ℕ))^(1-s))
  have hlr : (A : ℝ)/k ≤ (B : ℝ)/k :=
    div_le_div_of_nonneg_right (by exact_mod_cast hAB) (Nat.cast_nonneg k)
  have hi := vaughan_odd_mobius_rankin_energy_mobius_sigma_cutoff_quadratic_interval_integrable 2 (B/((U+1)*k))
    (U : ℝ) ((A : ℝ)/k) ((B : ℝ)/k)
  change IntervalIntegrable (fun z => vaughan_odd_mobius_rankin_energy_compact_mobiusSigmaStrictEnergy 2 (B/((U+1)*k)) U z)
    volume ((A : ℝ)/k) ((B : ℝ)/k) at hi
  have hbound := intervalIntegral.integral_mono_on hlr hi
    (intervalIntegrable_const (c := T)) (fun z hz =>
      vaughan_odd_mobius_rankin_energy_compact_mobius_sigma_strict_energy_rankin_upper_of_lower hdecay 2 (B/((U+1)*k))
        (max 1 (A/((U+1)*k))) L s U z (by norm_num) (le_max_left _ _) hL hs0 hs1
        (by exact_mod_cast hU)
        (vaughan_odd_mobius_rankin_energy_strict_cutoff_length_lower_on_vaughan_interval U A B k z hAB hU hk hz.1))
  apply hbound.trans_eq
  rw [intervalIntegral.integral_const]
  dsimp [T]
  ring

theorem actual_vaughan_odd_mobius_rankin_energy_log_decay_upper_complete
    (hdecay : ∀ x : ℝ, 11815 ≤ x →
      |∑ a∈Icc 1 ⌊x⌋₊, ((moebius a : ℤ) : ℝ)/(a : ℝ)| ≤ (3/100)/Real.log x)
    (U A B L : ℕ) (s : ℝ) (hAB : A ≤ B) (hhalf : B ≤ 2*A) (hU : 1 ≤ U)
    (hL : 11815 ≤ L) (hs0 : 1/2 < s) (hs1 : s ≤ 1) :
    let R : ℝ → ℝ := fun t =>
      (((∑' n : ℕ,(n : ℝ)^(-t-1))*(∑' n : ℕ,(n : ℝ)^(-2*t-1)))/
        (∑' n : ℕ,(n : ℝ)^(-3 : ℝ))) *
        (∏ p∈(2 : ℕ).primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-t)))
    let C : ℝ → ℝ → ℝ := fun u v =>
      ((∑' n : ℕ,(n : ℝ)^(-u-v))*(∑' n : ℕ,(n : ℝ)^(-u-2*v))*(∑' n : ℕ,(n : ℝ)^(-2*u-v)))/
        ((∑' n : ℕ,(n : ℝ)^(-3 : ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4 : ℝ)))
    let P : ℕ → ℝ := fun k => (((2*(L : ℝ))/(max 1 (A/((U+1)*k)) : ℕ))^(1-s))
    (∑ m∈Ioc A B, if Nat.Coprime m 2 then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0) ≤
      (4/Real.pi^2)*((B : ℝ)-A)*
        (∑ k∈Icc 1 (B/(U+1)), if Nat.Coprime k 2 then
          (((3/100)/Real.log (L : ℝ))^2*(R 1)^2*C 1 1 + 2*((3/100)/Real.log (L : ℝ))*P k*R 1*R s*C 1 s + (P k)^2*(R s)^2*C s s)/k else 0) +
      (107/10 : ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := by
  let T : ℕ → ℝ := fun k => vaughan_odd_mobius_rankin_energy_compact_rankinEnergyPolynomial 2 ((3/100)/Real.log (L : ℝ)) s
    (((2*(L : ℝ))/(max 1 (A/((U+1)*k)) : ℕ))^(1-s))
  let I : ℕ → ℝ := fun k => ∫ z in ((A : ℝ)/k)..((B : ℝ)/k),
    vaughan_odd_mobius_rankin_energy_compact_mobiusSigmaStrictEnergy 2 (B/((U+1)*k)) U z
  let eps : ℝ := (107/10 : ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ))
  have hbase := actual_vaughan_odd_mobius_quadratic_integral_upper U A B hAB hhalf
  change (∑ m∈Ioc A B, if Nat.Coprime m 2 then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0) ≤
    (4/Real.pi^2)*(∑ k∈Icc 1 (B/(U+1)), if Nat.Coprime k 2 then I k else 0)+eps at hbase
  have hsum : (∑ k∈Icc 1 (B/(U+1)), if Nat.Coprime k 2 then I k else 0) ≤
      ((B : ℝ)-A)*(∑ k∈Icc 1 (B/(U+1)), if Nat.Coprime k 2 then T k/k else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hkI
    by_cases hk2 : Nat.Coprime k 2
    · rw [if_pos hk2,if_pos hk2]
      have hi := vaughan_odd_mobius_rankin_energy_vaughan_odd_mobius_rankin_integral_upper hdecay U A B k L s hAB hU
        (Finset.mem_Icc.mp hkI).1 hL hs0 hs1
      exact hi.trans_eq (by dsimp only [T]; ring)
    · simp only [if_neg hk2,mul_zero,le_refl]
  have hmain := mul_le_mul_of_nonneg_left hsum (show 0 ≤ (4 : ℝ)/Real.pi^2 by positivity)
  apply hbase.trans ((add_le_add hmain (le_refl eps)).trans_eq ?_)
  dsimp [T,eps,vaughan_odd_mobius_rankin_energy_compact_rankinEnergyPolynomial,vaughan_odd_mobius_rankin_energy_compact_rankinSingleZetaConstant,vaughan_odd_mobius_rankin_energy_compact_rankinCoupledZetaConstant,vaughan_odd_mobius_rankin_energy_compact_rankinSharpCoprimeFactor]
  ring

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

theorem solution 
    (hdecay : ∀ x : ℝ, 11815 ≤ x →
      |∑ a∈Icc 1 ⌊x⌋₊, ((moebius a : ℤ) : ℝ)/(a : ℝ)| ≤ (3/100)/Real.log x)
    (U A B L : ℕ) (s : ℝ) (hAB : A ≤ B) (hhalf : B ≤ 2*A) (hU : 1 ≤ U)
    (hL : 11815 ≤ L) (hs0 : 1/2 < s) (hs1 : s ≤ 1) :
    let R : ℝ → ℝ := fun t =>
      (((∑' n : ℕ,(n : ℝ)^(-t-1))*(∑' n : ℕ,(n : ℝ)^(-2*t-1)))/
        (∑' n : ℕ,(n : ℝ)^(-3 : ℝ))) *
        (∏ p∈(2 : ℕ).primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-t)))
    let C : ℝ → ℝ → ℝ := fun u v =>
      ((∑' n : ℕ,(n : ℝ)^(-u-v))*(∑' n : ℕ,(n : ℝ)^(-u-2*v))*(∑' n : ℕ,(n : ℝ)^(-2*u-v)))/
        ((∑' n : ℕ,(n : ℝ)^(-3 : ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4 : ℝ)))
    let P : ℕ → ℝ := fun k => (((2*(L : ℝ))/(max 1 (A/((U+1)*k)) : ℕ))^(1-s))
    (∑ m∈Ioc A B, if Nat.Coprime m 2 then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0) ≤
      (4/Real.pi^2)*((B : ℝ)-A)*
        (∑ k∈Icc 1 (B/(U+1)), if Nat.Coprime k 2 then
          (((3/100)/Real.log (L : ℝ))^2*(R 1)^2*C 1 1 + 2*((3/100)/Real.log (L : ℝ))*P k*R 1*R s*C 1 s + (P k)^2*(R s)^2*C s s)/k else 0) +
      (107/10 : ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := Helfgott.actual_vaughan_odd_mobius_rankin_energy_log_decay_upper_complete hdecay U A B L s hAB hhalf hU hL hs0 hs1
#print axioms solution
