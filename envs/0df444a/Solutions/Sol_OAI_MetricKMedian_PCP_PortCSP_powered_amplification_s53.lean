-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.PortCSP.powered_amplification_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:19:11.577184+00:00
-- url     : https://prove2.me/submissions/49bea004-5965-46ea-8ee2-7b7b7305102f

import Mathlib
import Definitions.Def_OAIQ053K035
import Definitions.Def_OAIQ053K036
import Theorems.Thm_OAI_MetricKMedian_PCP_PortCSP_powered_sound_s53

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_FiniteTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteTest

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section Rates
variable {S T : Type} [Fintype S] [Fintype T]

theorem testRate_nonneg (p : S → Prop) : 0 ≤ testRate p := by
  classical
  exact expect_nonneg (by intro s _; split_ifs <;> norm_num)

end Rates

end MetricKMedian.PCP

end Inline_PCPFiniteTest

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_Stopped
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPStopped

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace Stopped
variable (t : ℕ)

theorem survival_nonneg : 0 ≤ survival t := div_nonneg (Nat.cast_nonneg _) (by positivity)
theorem stopping_nonneg : 0 ≤ stopping t := by unfold stopping; positivity
theorem survival_add_stopping : survival t + stopping t = 1 := by
  unfold survival stopping
  have hn : (t:ℝ)+1 ≠ 0 := by positivity
  field_simp

theorem coin_expect (a b : ℝ) :
    (𝔼 d : Fin (t+1), if d=0 then a else b) = stopping t * a + survival t * b := by
  classical
  rw [Fintype.expect_eq_sum_div_card, Fin.sum_univ_succ]
  simp only [ite_true, Fin.succ_ne_zero, ite_false, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold survival stopping
  push_cast
  ring

theorem expectation (n : ℕ) (H : ℕ → ℝ) :
    (𝔼 c : Fin n → Fin (t+1), H (length t n c)) =
      (∑ k ∈ range n, stopping t * survival t ^ k * H k) + survival t ^ n * H n := by
  induction n generalizing H with
  | zero => simp [length]
  | succ n ih =>
    rw [expect_word_succ]
    simp_rw [length_cons]
    have he (d : Fin (t+1)) :
        (𝔼 c : Fin n → Fin (t+1), H (if d=0 then 0 else 1+length t n c)) =
        if d=0 then H 0 else 𝔼 c : Fin n → Fin (t+1), H (1+length t n c) := by
      by_cases hd : d=0 <;> simp [hd]
    simp_rw [he]
    rw [coin_expect,ih (fun k => H (1+k)),sum_range_succ']
    simp only [pow_zero,mul_one,pow_succ]
    rw [mul_add, mul_sum]
    have hs : (∑ k ∈ range n, survival t * (stopping t * survival t ^ k * H (1+k))) =
        ∑ k ∈ range n, stopping t * (survival t ^ k * survival t) * H (k+1) := by
      apply sum_congr rfl
      intro k _
      rw [Nat.add_comm 1 k]
      ring
    rw [hs,Nat.add_comm 1 n]
    ring

theorem weights_sum (n : ℕ) :
    (∑ k ∈ range n, stopping t * survival t ^ k) + survival t ^ n = 1 := by
  simpa only [mul_one,Fintype.expect_const] using (expectation t n (fun _ => 1)).symm

end Stopped

end MetricKMedian.PCP

end Inline_PCPStopped

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_Majority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPMajority

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D A : Type} [Fintype D] [Nonempty D] [Fintype A] [Inhabited A]
variable (G : PortGraph V D) {cap : ℕ} (a : V → Advice D A cap)

lemma totalMass_eq (t L : ℕ) : totalMass t L = 1 - Stopped.survival t ^ (L+1) := by
  have h := Stopped.weights_sum t (L+1)
  unfold totalMass
  linarith

end PortGraph

end MetricKMedian.PCP

end Inline_PCPMajority

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PoweringBound
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPoweringBound

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

lemma geometric_tail_bound (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (h : p+q=1) (n : ℕ) :
    (1+(n:ℝ)*p)*q^n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    have hqp := pow_nonneg hq n
    have hs : (1+((n:ℝ)+1)*p)*q ≤ 1+(n:ℝ)*p := by
      rw [show q=1-p by linarith]
      nlinarith [mul_nonneg (add_nonneg hn zero_le_one) (mul_nonneg hp hp)]
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    calc
      _ = ((1+((n:ℝ)+1)*p)*q)*q^n := by ring
      _ ≤ (1+(n:ℝ)*p)*q^n := mul_le_mul_of_nonneg_right hs hqp
      _ ≤ 1 := ih

namespace PortGraph
lemma totalMass_half (t : ℕ) : 1/2 ≤ totalMass t t := by
  have h := geometric_tail_bound (Stopped.stopping t) (Stopped.survival t)
    (Stopped.stopping_nonneg t) (Stopped.survival_nonneg t)
    (by linarith [Stopped.survival_add_stopping t]) (t+1)
  have he : ((t+1:ℕ):ℝ)*Stopped.stopping t = 1 := by
    unfold Stopped.stopping
    push_cast
    have ht : (t:ℝ)+1 ≠ 0 := by positivity
    field_simp
  rw [he] at h
  rw [totalMass_eq]
  linarith
end PortGraph

lemma powering_arithmetic (u m q r : ℝ) (hu : 0 ≤ u) (hm : 1/2 ≤ m)
    (hq : 0 < q) (hr : 0 ≤ r)
    (h : (u*(m/q)^2)^2 ≤ r*(20*u+16*u^2)) :
    min u 1 ≤ 576*q^4*r := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hm2 : 1/4 ≤ m^2 := by nlinarith
  have hm4 : 1/16 ≤ m^4 := by nlinarith [sq_nonneg (m^2-1/4)]
  have he : 16*q^4*(u*(m/q)^2)^2 = 16*u^2*m^4 := by
    field_simp
  have hlow : u^2 ≤ 16*q^4*(u*(m/q)^2)^2 := by
    rw [he]
    nlinarith [mul_nonneg (sq_nonneg u) (show 0 ≤ 16*m^4-1 by linarith)]
  have hh := hlow.trans (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 16*q^4))
  by_cases hzero : u=0
  · subst u; simp; positivity
  have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hzero)
  have hc : 0 ≤ 16*q^4*r := by positivity
  by_cases hu1 : u ≤ 1
  · rw [min_eq_left hu1]
    have hub : 20*u+16*u^2 ≤ 36*u := by nlinarith
    have hh' : u^2 ≤ (576*q^4*r)*u := by
      calc
        _ ≤ 16*q^4*(r*(20*u+16*u^2)) := hh
        _ = (16*q^4*r)*(20*u+16*u^2) := by ring
        _ ≤ (16*q^4*r)*(36*u) := mul_le_mul_of_nonneg_left hub hc
        _ = _ := by ring
    nlinarith
  · rw [min_eq_right (le_of_not_ge hu1)]
    have hub : 20*u+16*u^2 ≤ 36*u^2 := by nlinarith
    have hh' : u^2 ≤ (576*q^4*r)*u^2 := by
      calc
        _ ≤ 16*q^4*(r*(20*u+16*u^2)) := hh
        _ = (16*q^4*r)*(20*u+16*u^2) := by ring
        _ ≤ (16*q^4*r)*(36*u^2) := mul_le_mul_of_nonneg_left hub hc
        _ = _ := by ring
    exact (le_mul_iff_one_le_right (sq_pos_of_pos hup)).mp (by simpa only [mul_comm] using hh')

namespace PortCSP
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype A] [Inhabited A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A)

theorem powered_amplification_s53_oai (hG : G.Contracts (1/2)) (t : ℕ) (ht : 1 ≤ t)
    (a : V → Advice D A (2*t+2)) :
    min ((t:ℝ)*testRate (C.Bad (G.plurality a t t))) 1 ≤
      576*(Fintype.card A:ℝ)^4 * (C.powered (cap := 2*t+2) t).rejection a := by
  have hh := C.powered_sound_s53 hG a t t (by omega)
  have hd := testRate_nonneg (C.Bad (G.plurality a t t))
  have htR : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hc : ((2*t+2:ℕ):ℝ) ≤ 4*(t:ℝ) := by push_cast; linarith
  have hc0 : (0:ℝ) ≤ (2*t+2:ℕ) := Nat.cast_nonneg _
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg _
  have hc2 : (((2*t+2:ℕ):ℝ))^2 ≤ 16*(t:ℝ)^2 := by nlinarith
  have hbound : 5*((2*t+2:ℕ):ℝ)*testRate (C.Bad (G.plurality a t t)) +
      (((2*t+2:ℕ):ℝ))^2*(testRate (C.Bad (G.plurality a t t)))^2 ≤
      20*((t:ℝ)*testRate (C.Bad (G.plurality a t t))) +
      16*((t:ℝ)*testRate (C.Bad (G.plurality a t t)))^2 := by
    have h1 := mul_le_mul_of_nonneg_right hc hd
    have h2 := mul_le_mul_of_nonneg_right hc2 (sq_nonneg (testRate (C.Bad (G.plurality a t t))))
    nlinarith
  exact powering_arithmetic _ _ _ _ (mul_nonneg ht0 hd) (PortGraph.totalMass_half t)
    (Nat.cast_pos.mpr Fintype.card_pos) (testRate_nonneg _) (hh.trans
      (mul_le_mul_of_nonneg_left hbound (testRate_nonneg _)))

end PortCSP
end MetricKMedian.PCP

end Inline_PCPPoweringBound

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.PortCSP.powered_amplification_s53_oai := @OAI.MetricKMedian.PCP.PortCSP.powered_amplification_s53_oai
