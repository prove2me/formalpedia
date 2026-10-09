-- Prove2me | solution 1 for Helfgott.actual_vaughan_odd_mobius_two_power_log_decay_upper
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T05:57:02.510088+00:00
-- url     : https://prove2.me/submissions/c653850b-1e08-4120-b038-54ecbf04d0a3

import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Tactic
import Theorems.Thm_Helfgott_actual_vaughan_odd_mobius_two_power_energy_upper
import Theorems.Thm_Helfgott_moebius_reciprocal_two_power_envelope
import Theorems.Thm_Helfgott_moebius_reciprocal_sqrt_two_finite

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
open Finset Nat Real ArithmeticFunction MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott
theorem actual_vaughan_odd_mobius_two_power_log_decay_upper_complete
    (hdecay : ∀ v : ℝ, 11815 ≤ v →
      |∑ r∈Icc 1 ⌊v⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤ (3/100)/Real.log v)
    (U A B : ℕ) (beta delta : ℝ)
    (hAB : A ≤ B) (hhalf : B ≤ 2*A) (hU : 1 ≤ U)
    (hX : 1200001 ≤ B/(U+1))
    (hb0 : 0 ≤ beta) (hb1 : beta < 1/2) (hd1 : delta < 1/2)
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
    let P : ℕ → ℝ := fun k => (L/(max 1 (A/((U+1)*k)) : ℕ))^(1-s)
    let Z : ℕ → ℝ := fun k => (T/(max 1 (A/((U+1)*k)) : ℕ))^(1-t)
    (∑ m∈Ioc A B, if Nat.Coprime m 2 then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0) ≤
      (4/Real.pi^2)*((B : ℝ)-A)*
        (∑ k∈Icc 1 (B/(U+1)), if Nat.Coprime k 2 then
          (a^2*(P k)^2*(R s)^2*C s s + 2*a*b*(P k)*(Z k)*R s*R t*C s t +
            b^2*(Z k)^2*(R t)^2*C t t)/k else 0) +
      (107/10 : ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := by
  let X : ℝ := (B/(U+1) : ℕ)
  have hXr : (1200001 : ℝ) ≤ X := by
    dsimp only [X]
    exact_mod_cast hX
  have hlog : 0 < Real.log (1200001 : ℝ) := Real.log_pos (by norm_num)
  have hd0 : 0 ≤ delta := le_trans (by positivity) hd
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hM := moebius_reciprocal_two_power_envelope 1200001 X beta delta (by norm_num) hXr
    hb0 hb1.le hd moebius_reciprocal_sqrt_two_finite hdecay
  exact actual_vaughan_odd_mobius_two_power_energy_upper U A B X 2 X 1
    ((3/100)/Real.log X) (1-beta) (1-delta)
    hAB hhalf hU le_rfl (by norm_num) (by linarith) (by norm_num)
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
    (hb0 : 0 ≤ beta) (hb1 : beta < 1/2) (hd1 : delta < 1/2)
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
    let P : ℕ → ℝ := fun k => (L/(max 1 (A/((U+1)*k)) : ℕ))^(1-s)
    let Z : ℕ → ℝ := fun k => (T/(max 1 (A/((U+1)*k)) : ℕ))^(1-t)
    (∑ m∈Ioc A B, if Nat.Coprime m 2 then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0) ≤
      (4/Real.pi^2)*((B : ℝ)-A)*
        (∑ k∈Icc 1 (B/(U+1)), if Nat.Coprime k 2 then
          (a^2*(P k)^2*(R s)^2*C s s + 2*a*b*(P k)*(Z k)*R s*R t*C s t +
            b^2*(Z k)^2*(R t)^2*C t t)/k else 0) +
      (107/10 : ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := Helfgott.actual_vaughan_odd_mobius_two_power_log_decay_upper_complete hdecay U A B beta delta hAB hhalf hU hX hb0 hb1 hd1 hd
#print axioms solution
