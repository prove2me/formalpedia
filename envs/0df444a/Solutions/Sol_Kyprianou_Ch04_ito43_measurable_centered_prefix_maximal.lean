-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_measurable_centered_prefix_maximal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:00:56.719772+00:00
-- url     : https://prove2.me/submissions/df23dfdd-aeef-4b72-954a-cf9e359acfa9

import Mathlib
import Theorems.Thm_DurrettProbability_kolmogorov_maximal_inequality
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hm : ∀ k, Measurable (Y k)) (hi : iIndepFun Y P)
    (hL : ∀ k, MemLp (Y k) 2 P) (hmean : ∀ k, (∫ w, Y k w ∂P) = 0)
    (V : ℝ) (hv : ∀ k, variance (Y k) P ≤ V)
    (n : ℕ) (e : ℝ) (he : 0 < e) :
    (P {w | ∃ j ≤ n, e ≤ |∑ k ∈ Finset.range j, Y k w|}).toReal
      ≤ (n:ℝ)*V/e^2 := by
  have h := DurrettProbability.kolmogorov_maximal_inequality Y hm hi hL hmean n e he
  have hsub : {w | ∃ j ≤ n, e ≤ |∑ k ∈ Finset.range j, Y k w|} ⊆
      {w | ∃ j ∈ Finset.Icc 1 n, e ≤ |DurrettProbability.partialSum Y j w|} := by
    rintro w ⟨j,hj,herr⟩
    have hj0 : 1 ≤ j := by
      by_contra h0
      have hz : j = 0 := by omega
      subst j
      simp at herr
      linarith
    exact ⟨j,Finset.mem_Icc.mpr ⟨hj0,hj⟩,herr⟩
  refine (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsub)).trans (h.trans ?_)
  apply div_le_div_of_nonneg_right _ (sq_nonneg e)
  change variance (fun w => ∑ k ∈ Finset.range n, Y k w) P ≤ _
  have hsum : (fun w => ∑ k ∈ Finset.range n, Y k w) = ∑ k ∈ Finset.range n, Y k := by
    funext w
    simp [Finset.sum_apply]
  rw [hsum,IndepFun.variance_sum (fun k _ => hL k) (fun i _ j _ hij => hi.indepFun hij)]
  calc
    _ ≤ ∑ k ∈ Finset.range n, V := Finset.sum_le_sum (fun k _ => hv k)
    _ = _ := by simp [nsmul_eq_mul]
