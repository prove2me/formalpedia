-- Prove2me | solution 1 for MulticlassQNet.FirstOrder.theorem_4_3_idle_busy_split
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:19:47.79492+00:00
-- url     : https://prove2.me/submissions/ba352bf8-8995-4511-97bf-66a03567adc9

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics
import Definitions.Def_MulticlassQNet_FirstOrder_Constraints



namespace MulticlassQNet.FirstOrder

lemma mq_busy_nonneg {N R : ℕ} {net : Network N R} (P : Policy net) (n : Fin R → ℕ) (r : Fin R) :
    0 ≤ P.busy n r := by unfold Policy.busy; split_ifs <;> norm_num

lemma mq_busy_le_one {N R : ℕ} {net : Network N R} (P : Policy net) (n : Fin R → ℕ) (r : Fin R) :
    P.busy n r ≤ 1 := by unfold Policy.busy; split_ifs <;> norm_num

lemma mq_idle_nonneg {N R : ℕ} {net : Network N R} (P : Policy net) (i : Fin N) (n : Fin R → ℕ) :
    0 ≤ P.idle i n := by unfold Policy.idle; split_ifs <;> norm_num

lemma mq_busy_idle_sum {N R : ℕ} {net : Network N R} (P : Policy net) (i : Fin N)
    (n : Fin R → ℕ) : ∑ r ∈ net.C i, P.busy n r + P.idle i n = 1 := by
  by_cases h : ∀ r ∈ net.C i, P.serve n r = false
  · have h1 : ∑ r ∈ net.C i, P.busy n r = 0 :=
      Finset.sum_eq_zero (fun r hr => by simp [Policy.busy, h r hr])
    simp only [h1, Policy.idle, if_pos h]; norm_num
  · push Not at h
    obtain ⟨r0, hr0, hs⟩ := h
    have hs' : P.serve n r0 = true := by simpa using hs
    have h1 : ∑ r ∈ net.C i, P.busy n r = 1 := by
      rw [Finset.sum_eq_single r0]
      · simp [Policy.busy, hs']
      · intro b hb hne
        have hσ : net.σ b = net.σ r0 := by
          simp [Network.C] at hb hr0; rw [hb, hr0]
        have := P.serve_one_class n b r0 hσ hne
        have : P.serve n b = false := by
          cases hh : P.serve n b
          · rfl
          · exact absurd ⟨hh, hs'⟩ this
        simp [Policy.busy, this]
      · intro h; exact absurd hr0 h
    have h2 : P.idle i n = 0 := by
      simp only [Policy.idle]; rw [if_neg]; push Not; exact ⟨r0, hr0, by simp [hs']⟩
    rw [h1, h2]; norm_num

lemma mq_summable_pi {N R : ℕ} {net : Network N R} {P : Policy net} {π : (Fin R → ℕ) → ℝ}
    (hA : P.AssumptionA π) : Summable π := hA.1.2.1.summable

lemma mq_pi_nonneg {N R : ℕ} {net : Network N R} {P : Policy net} {π : (Fin R → ℕ) → ℝ}
    (hA : P.AssumptionA π) (n) : 0 ≤ π n := hA.1.1 n

lemma mq_summable_lin {N R : ℕ} {net : Network N R} {P : Policy net} {π : (Fin R → ℕ) → ℝ}
    (hA : P.AssumptionA π) (r : Fin R) : Summable (fun n => π n * (n r : ℝ)) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (mq_pi_nonneg hA n) (by positivity))
    (fun n => ?_) ((mq_summable_pi hA).add (hA.2.2 r))
  have := mq_pi_nonneg hA n
  have h0 : (0:ℝ) ≤ n r := by positivity
  nlinarith [sq_nonneg ((n r : ℝ) - 1)]

lemma mq_summable_bounded {N R : ℕ} {net : Network N R} {P : Policy net} {π : (Fin R → ℕ) → ℝ}
    (hA : P.AssumptionA π) (r : Fin R) (c : (Fin R → ℕ) → ℝ) (hc0 : ∀ n, 0 ≤ c n)
    (hc1 : ∀ n, c n ≤ 1) : Summable (fun n => π n * c n * (n r : ℝ)) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (mul_nonneg (mq_pi_nonneg hA n) (hc0 n))
    (by positivity)) (fun n => ?_) (mq_summable_lin hA r)
  have := mq_pi_nonneg hA n
  have h0 : (0:ℝ) ≤ n r := by positivity
  have : π n * c n ≤ π n := by nlinarith [hc0 n, hc1 n]
  exact mul_le_mul_of_nonneg_right this h0

theorem idle_busy_core {N R : ℕ} (net : Network N R)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : P.AssumptionA π) :
    net.Eq28 (meanNum π) (P.busyMoment π) (P.idleMoment π) := by
  intro i r'
  simp only [Policy.busyMoment, Policy.idleMoment, meanNum]
  rw [← Summable.tsum_finsetSum (fun r _ => mq_summable_bounded hA r' _ (mq_busy_nonneg P · r)
      (mq_busy_le_one P · r))]
  rw [← Summable.tsum_add (summable_sum (fun r _ => mq_summable_bounded hA r' _
      (mq_busy_nonneg P · r) (mq_busy_le_one P · r)))
    (mq_summable_bounded hA r' _ (mq_idle_nonneg P i) (fun n => by
      unfold Policy.idle; split_ifs <;> norm_num))]
  congr 1; funext n
  have := mq_busy_idle_sum P i n
  calc ∑ r ∈ net.C i, π n * P.busy n r * (n r' : ℝ) + π n * P.idle i n * (n r' : ℝ)
      = π n * (n r' : ℝ) * (∑ r ∈ net.C i, P.busy n r + P.idle i n) := by
        simp only [mul_add, Finset.mul_sum]; congr 1
        · apply Finset.sum_congr rfl; intro r _; ring
        · ring
    _ = π n * (n r' : ℝ) := by rw [this, mul_one]

end MulticlassQNet.FirstOrder

open MulticlassQNet.FirstOrder


theorem solution {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen) (hload : net.LoadLtOne lam)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : P.AssumptionA π) :
    net.Eq28 (meanNum π) (P.busyMoment π) (P.idleMoment π) := by
  exact idle_busy_core net P π hA
