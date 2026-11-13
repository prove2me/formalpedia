-- Prove2me | solution 1 for MultipleUnicast.Counterexample.multiple_unicast_coding_advantage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:10:40.443316+00:00
-- url     : https://prove2.me/submissions/d0766971-2827-4364-90ba-1dac183258f9

import Mathlib
import Theorems.Thm_MultipleUnicast_Counterexample_balanced_orientation
import Theorems.Thm_MultipleUnicast_Counterexample_coding_rate
import Theorems.Thm_MultipleUnicast_Counterexample_flow_bound

section
set_option maxRecDepth 2048
set_option autoImplicit false
open scoped Classical

namespace MultipleUnicast.Counterexample.Dev.Goal
open MultipleUnicast.Counterexample

theorem card_F9 : Fintype.card F9 = 9 := by
  rw [Fintype.card_congr (QuadraticAlgebra.equivProd (-1 : ZMod 3) 0)]
  simp

theorem pointEnd_lt (q : Edge) : (pointEnd q).val < 91 := (edgePair q).1.isLt

theorem lineEnd_ge (q : Edge) : 91 ≤ (lineEnd q).val := by
  simp [lineEnd]

theorem earlier_ne_later (q : Edge) : earlier q ≠ later q := by
  intro h
  have h1 := pointEnd_lt q
  have h2 := lineEnd_ge q
  unfold earlier later at h
  split_ifs at h with hh
  · have := congrArg Fin.val h; omega
  · have := congrArg Fin.val h; omega

theorem ratio_bound (ρ : ℝ) (c : ENNReal) (hρ : 0 < ρ) (hρle : ρ ≤ 147 / 157)
    (hc : 1 ≤ c) : ENNReal.ofReal ((157 : ℝ) / 147) ≤ c / ENNReal.ofReal ρ := by
  have hρ' : ENNReal.ofReal ρ ≠ 0 := by simpa using hρ
  have hρt : ENNReal.ofReal ρ ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.le_div_iff_mul_le (Or.inl hρ') (Or.inl hρt)]
  refine le_trans ?_ hc
  rw [← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_one.mpr
  have : (157 : ℝ) / 147 * ρ ≤ 157 / 147 * (147 / 157) :=
    mul_le_mul_of_nonneg_left hρle (by norm_num)
  linarith [show (157 : ℝ) / 147 * (147 / 157) = 1 by norm_num]

end MultipleUnicast.Counterexample.Dev.Goal

namespace MultipleUnicast.Counterexample
open MultipleUnicast.Counterexample.Dev.Goal

theorem chk_multiple_unicast_coding_advantage :
    Fintype.card F9 = 9 ∧ Fintype.card Vertex = 182 ∧
    incidenceList.length = 910 ∧ Function.Injective edgePair ∧
    physical.card = 735 ∧ network.k = 157 ∧
    (∀ i, network.D i = 1 ∧ network.s i ≠ network.t i) ∧
    (∀ u v, network.C u v = if graph.Adj u v then 1 else 0) ∧
    CausalLinearCode ∧
    (∀ m i, protocol.decode i (ownValues (network.t i) m)
      (received protocol (network.t i) m) = m i) ∧
    0 < witnessScale ∧ SupportsRate protocol witnessLaw 1 witnessScale ∧
    (1 : ENNReal) ≤ codingThroughput network ∧
    feasibleRates.Nonempty ∧ BddAbove feasibleRates ∧
    (∃ r : ℝ, 0 < r ∧ ∃ f, network.IsFeasibleFlow f r) ∧
    (∀ (r : ℝ) (f : Fin network.k → Vertex → Vertex → ℝ),
      0 ≤ r → network.IsFeasibleFlow f r → r ≤ (147 : ℝ) / 157) ∧
    0 < routingThroughput ∧ routingThroughput ≤ (147 : ℝ) / 157 ∧
    ENNReal.ofReal ((157 : ℝ) / 147) ≤
      codingThroughput network / ENNReal.ofReal routingThroughput ∧
    (1 : ℝ) < (157 : ℝ) / 147 := by
  obtain ⟨hlen, -, hinj, -, -, -, -, -, -, -, -, hphys, -⟩ := balanced_orientation
  obtain ⟨hk, hcode, hscale, hrate, hthr⟩ := coding_rate
  obtain ⟨hne, hbdd, hpos, hbound, hrpos, hrle, heq, -, -⟩ := flow_bound
  have hrle' : routingThroughput ≤ (147 : ℝ) / 157 := heq ▸ hrle
  refine ⟨card_F9, by simp, hlen, hinj, hphys, hk, fun i => ⟨rfl, earlier_ne_later _⟩,
    fun u v => rfl, hcode, hcode.2.2.2.1, hscale, hrate, hthr, hne, hbdd, hpos, hbound,
    hrpos, hrle', ratio_bound _ _ hrpos hrle' hthr, by norm_num⟩

end MultipleUnicast.Counterexample
end

theorem solution : type_of% @MultipleUnicast.Counterexample.chk_multiple_unicast_coding_advantage := @MultipleUnicast.Counterexample.chk_multiple_unicast_coding_advantage
