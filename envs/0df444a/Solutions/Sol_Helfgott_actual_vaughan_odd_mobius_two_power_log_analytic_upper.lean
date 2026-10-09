-- Prove2me | solution 1 for Helfgott.actual_vaughan_odd_mobius_two_power_log_analytic_upper
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T05:57:17.721321+00:00
-- url     : https://prove2.me/submissions/59c3d452-2224-468c-aa10-2efa5d8439e1

import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Tactic
import Theorems.Thm_Helfgott_actual_vaughan_odd_mobius_two_power_analytic_upper
import Theorems.Thm_Helfgott_moebius_reciprocal_two_power_envelope
import Theorems.Thm_Helfgott_moebius_reciprocal_sqrt_two_finite

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
open Finset Nat Real ArithmeticFunction MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott
theorem actual_vaughan_odd_mobius_two_power_log_analytic_upper_complete
    (hdecay : ∀ v : ℝ, 11815 ≤ v →
      |∑ r∈Icc 1 ⌊v⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤ (3/100)/Real.log v)
    (U A B : ℕ) (beta delta : ℝ)
    (hAB : A ≤ B) (hhalf : B ≤ 2*A) (hU : 1 ≤ U)
    (hX : 1200001 ≤ B/(U+1))
    (hb0 : 0 < beta) (hb1 : beta < 1/2) (hd1 : delta < 1/2)
    (hd : 1/Real.log (1200001 : ℝ) ≤ delta) :
    let X : ℝ := (B/(U+1) : ℕ)
    let a : ℝ := 1
    let b : ℝ := (3/100)/Real.log X
    let L : ℝ := 2
    let T : ℝ := X
    let s : ℝ := 1-beta
    let t : ℝ := 1-delta
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
  let X : ℝ := (B/(U+1) : ℕ)
  have hXr : (1200001 : ℝ) ≤ X := by
    dsimp only [X]
    exact_mod_cast hX
  have hlog : 0 < Real.log (1200001 : ℝ) := Real.log_pos (by norm_num)
  have hd0 : 0 < delta := lt_of_lt_of_le (by positivity) hd
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hM := moebius_reciprocal_two_power_envelope 1200001 X beta delta (by norm_num) hXr
    hb0.le hb1.le hd moebius_reciprocal_sqrt_two_finite hdecay
  have hA : 1 ≤ A := by
    have hB := Nat.div_le_self B (U+1)
    omega
  have hY : 1 ≤ B/(U+1) := by omega
  exact actual_vaughan_odd_mobius_two_power_analytic_upper U A B X 2 X 1
    ((3/100)/Real.log X) (1-beta) (1-delta)
    hA hY hAB hhalf hU le_rfl (by norm_num) (by linarith) (by norm_num)
    (by positivity) (by linarith) (by linarith) (by linarith) (by linarith)
    (by simpa only [show (1 : ℝ)-(1-beta)=beta by ring,
      show (1 : ℝ)-(1-delta)=delta by ring,one_mul] using hM)


end Helfgott
end

open Helfgott Finset Nat Real ArithmeticFunction MeasureTheory
open scoped BigOperators Classical Interval
theorem solution 
    (hdecay : ∀ v : ℝ, 11815 ≤ v →
      |∑ r∈Icc 1 ⌊v⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤ (3/100)/Real.log v)
    (U A B : ℕ) (beta delta : ℝ)
    (hAB : A ≤ B) (hhalf : B ≤ 2*A) (hU : 1 ≤ U)
    (hX : 1200001 ≤ B/(U+1))
    (hb0 : 0 < beta) (hb1 : beta < 1/2) (hd1 : delta < 1/2)
    (hd : 1/Real.log (1200001 : ℝ) ≤ delta) :
    let X : ℝ := (B/(U+1) : ℕ)
    let a : ℝ := 1
    let b : ℝ := (3/100)/Real.log X
    let L : ℝ := 2
    let T : ℝ := X
    let s : ℝ := 1-beta
    let t : ℝ := 1-delta
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
        (107/10 : ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := Helfgott.actual_vaughan_odd_mobius_two_power_log_analytic_upper_complete hdecay U A B beta delta hAB hhalf hU hX hb0 hb1 hd1 hd
#print axioms solution
