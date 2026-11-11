-- Prove2me | solution 1 for Helfgott.actual_vaughan_odd_mobius_constant_log_energy_upper
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-11T01:16:52.362329+00:00
-- url     : https://prove2.me/submissions/104c1c88-4a95-4644-8e15-48b8f490fcfb

import Theorems.Thm_Helfgott_actual_vaughan_odd_mobius_power_constant_analytic_upper
import Theorems.Thm_Helfgott_moebius_reciprocal_sqrt_constant_envelope

open Helfgott Finset Nat Real ArithmeticFunction MeasureTheory
open scoped BigOperators Classical Interval

theorem solution
    (hdecay : ∀ v : ℝ, 11815 ≤ v →
      |∑ r∈Icc 1 ⌊v⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤ (3/100)/Real.log v)
    (U A B : ℕ) (beta : ℝ)
    (hA : 1 ≤ A) (hY : 1 ≤ B/(U+1)) (hAB : A ≤ B) (hhalf : B ≤ 2*A) (hU : 1 ≤ U)
    (hb0 : 0 < beta) (hb1 : beta < 1/2) :
    let s : ℝ := 1-beta
    let a : ℝ := 1
    let b : ℝ := (3/100)/Real.log (1200001 : ℝ)
    let L : ℝ := 2
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
    (∑ m∈Ioc A B,if Nat.Coprime m 2 then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0) ≤
      (4/Real.pi^2)*((B : ℝ)-A)*
        (a^2*P^2*(R s)^2*C s s*Psi (2*(1-s)) +
          2*a*b*P*R s*R 1*C s 1*Psi (1-s) +
          b^2*(R 1)^2*C 1 1*(1+Real.log (Y : ℝ)/2)) +
        (107/10 : ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := by
  have hb : 0 ≤ (3 / 100 : ℝ) / Real.log (1200001 : ℝ) := by
    exact div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le
  have hM : ∀ v : ℝ, 1 ≤ v → v ≤ (B / (U + 1) : ℕ) →
      |∑ r ∈ Icc 1 ⌊v⌋₊, ((moebius r : ℤ) : ℝ) / (r : ℝ)| ≤
        1 * (2 / v) ^ (1 - (1 - beta)) + (3 / 100) / Real.log (1200001 : ℝ) := by
    intro v hv _
    simpa only [sub_sub_cancel, one_mul] using
      Helfgott.moebius_reciprocal_sqrt_constant_envelope hdecay beta hb0.le hb1.le v hv
  exact Helfgott.actual_vaughan_odd_mobius_power_constant_analytic_upper
    U A B (B / (U + 1) : ℕ) 2 1 ((3 / 100) / Real.log (1200001 : ℝ)) (1 - beta)
    hA hY hAB hhalf hU le_rfl (by norm_num) (by norm_num) hb
    (by linarith) (by linarith) hM
