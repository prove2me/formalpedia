-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.RefinedRecovery.metric_length_bound_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:15:44.354901+00:00
-- url     : https://prove2.me/submissions/943bc461-9586-4049-a50f-9810fcc5dd33

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q224R000

section
-- module Solutions.Q224_RR.KMedianRecovery_Refined_Work
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RefinedRecovery

private lemma bits_length_le (n : ℕ) : n.bits.length ≤ n + 1 := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr ((show n < 2^n from Nat.lt_two_pow_self).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega)))

private lemma natBits_length_le (n : ℕ) :
    (RationalMetricInput.natBits n).length ≤ 2*n+3 := by
  simp only [RationalMetricInput.natBits, List.length_append, List.length_replicate,
    List.length_singleton]
  have := bits_length_le n
  omega

private lemma rationalBits_nat_length (n : ℕ) :
    (RationalMetricInput.rationalBits (n : ℚ)).length ≤ 2*n+7 := by
  simp only [RationalMetricInput.rationalBits, List.length_append, List.length_singleton,
    Rat.num_natCast, Int.natAbs_natCast, Rat.den_natCast]
  have := natBits_length_le n
  norm_num [RationalMetricInput.natBits, Nat.bits] at *
  omega

lemma metric_length_bound_s35_oai (I : Input) (b : Polynomial ℕ) (h : I.Bounded b) :
    I.metric.bits.length ≤ (metricLengthPolynomial b).eval I.size := by
  have hn : I.metric.pointCount ≤ I.size := by
    calc
      _ = (I.metric.clients ∪ I.metric.facilities).card := by rw [I.metric.covered]; simp
      _ ≤ I.size := Finset.card_union_le _ _
  have hk : I.metric.budget ≤ I.size :=
    I.anchor_card.symm.trans_le ((Finset.card_le_card I.anchor_subset).trans
      (by unfold Input.size RationalMetricInput.size; omega))
  have he (i j : I.Point) :
      (RationalMetricInput.rationalBits (I.metric.distance i j)).length ≤ 2*b.eval I.size+7 := by
    obtain ⟨z, hz⟩ := I.integral i j
    rw [hz]
    have hzb : z ≤ b.eval I.size := by exact_mod_cast (hz ▸ h i j)
    exact (rationalBits_nat_length z).trans (by omega)
  have hr (i : I.Point) :
      ((List.ofFn (fun j : I.Point => RationalMetricInput.rationalBits
        (I.metric.distance i j))).flatten).length ≤ I.metric.pointCount*(2*b.eval I.size+7) := by
    simp only [List.length_flatten, List.map_ofFn, List.sum_ofFn]
    exact (Finset.sum_le_sum (fun j _ => he i j)).trans_eq (by simp)
  have hm : ((List.ofFn (fun i : I.Point =>
      (List.ofFn (fun j : I.Point => RationalMetricInput.rationalBits
        (I.metric.distance i j))).flatten)).flatten).length ≤
      I.metric.pointCount^2*(2*b.eval I.size+7) := by
    simp only [List.length_flatten, List.map_ofFn, List.sum_ofFn]
    apply (Finset.sum_le_sum (fun i _ => hr i)).trans_eq
    simp [pow_two, mul_assoc]
  have hp := natBits_length_le I.metric.pointCount
  have hb := natBits_length_le I.metric.budget
  dsimp only [Input.Point] at hm
  have hpow : I.metric.pointCount^2*(2*b.eval I.size+7) ≤ I.size^2*(2*b.eval I.size+7) := by
    gcongr
  simp only [RationalMetricInput.bits, List.length_append, List.length_ofFn]
  simp only [metricLengthPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

end MetricKMedianRecovery.RefinedRecovery

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.RefinedRecovery.metric_length_bound_s35_oai := @OAI.MetricKMedianRecovery.RefinedRecovery.metric_length_bound_s35_oai
