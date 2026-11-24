-- Prove2me | solution 1 for GlobalTheory.meanSq_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:28:15.119866+00:00
-- url     : https://prove2.me/submissions/f0cf4864-fa96-4ad4-bd00-fd04e50bfb16

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimePowerVonMangoldtSumBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqIocLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumDivSubLeTwoLogOfPartialSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MeanSqCardPrimeFactorsOutPart
import Theorems.Thm_GlobalTheory_meanSq_cn_nonneg
import Theorems.Thm_GlobalTheory_meanSq_cn_eq_zero
import Theorems.Thm_GlobalTheory_meanSq_fiber_le
import Theorems.Thm_GlobalTheory_meanSq_card_primeFactors_outPart
import Theorems.Thm_GlobalTheory_meanSq_mem_outPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open GlobalTheory
open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2
namespace GlobalTheory
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) (m₀ : ℕ) (hm₀ : 0 < m₀) (nStar : ℕ) (A : ℕ → ℕ → ℝ) (η S : ℝ)
    (hη : 0 ≤ η) (hS0 : 0 ≤ S) (hS : ∀ p : ℕ, p.Prime → sP x p ≤ S) (hA1 : ∀ n n', A n n' ≤ 1)
    (hA : ∀ n n' : ℕ, n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊ → n' ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊ →
      IsPrimePow n → IsPrimePow n' → outPart m₀ (n * n') ≠ 1 → outPart m₀ (n * n') ≠ nStar → A n n' ≤ η) :
    ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, ∑ n' ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, cn x n * cn x n' * A n n' ≤
      η * (∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, cn x n) ^ 2 +
      ∑ p ∈ (Icc 1 ⌊x ^ (400 : ℝ)⌋₊).filter (fun p => p.Prime), sP x p ^ 2 +
      (Rsum x m₀ + 2 * S) ^ 2 := by
  classical
  have hfib := fun p hp => meanSq_fiber_le (p := p) hx hp
  have hc := meanSq_cn_nonneg hx
  unfold Rsum
  set N := ⌊x ^ (400 : ℝ)⌋₊ with hN
  set f : ℕ → ℕ → ℝ := fun p n => if n.minFac = p then cn x n else 0 with hf
  have hf0 : ∀ p n, 0 ≤ f p n := fun p n => by
    simp only [hf]; split_ifs
    exacts [hc n, le_rfl]
  set P := (Icc 1 N).filter (fun p => p.Prime) with hP
  set M := m₀.primeFactors.filter (fun p => p ≤ N) with hM
  set T : Finset ℕ := if nStar.primeFactors.card ≤ 2 then nStar.primeFactors else ∅ with hT
  have hTcard : T.card ≤ 2 := by
    simp only [hT]; split_ifs with h
    exacts [h, by simp]
  have hTprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    simp only [hT] at hp; split_ifs at hp with h
    exacts [Nat.prime_of_mem_primeFactors hp, absurd hp (Finset.notMem_empty p)]
  set U : ℕ → ℝ := fun n => (if IsSquare n then cn x n else 0) + ∑ p ∈ M, f p n + ∑ p ∈ T, f p n with hU
  have hU1 : ∀ n, 0 ≤ (if IsSquare n then cn x n else 0) := fun n => by
    split_ifs
    exacts [hc n, le_rfl]
  have hU2 : ∀ (B : Finset ℕ) n, 0 ≤ ∑ p ∈ B, f p n := fun B n => Finset.sum_nonneg fun p _ => hf0 p n
  have hU0 : ∀ n, 0 ≤ U n := fun n => add_nonneg (add_nonneg (hU1 n) (hU2 M n)) (hU2 T n)
  have hsingle : ∀ (B : Finset ℕ) (n : ℕ), n.minFac ∈ B → cn x n ≤ ∑ p ∈ B, f p n := by
    intro B n h
    have := Finset.single_le_sum (f := fun p => f p n) (fun p _ => hf0 p n) h
    simpa [hf] using this
  have hUc : ∀ n n' : ℕ, n ∈ Icc 1 N → IsPrimePow n → IsPrimePow n' → n.minFac ≠ n'.minFac →
      (outPart m₀ (n * n') = 1 ∨ outPart m₀ (n * n') = nStar) → cn x n ≤ U n := by
    intro n n' hn hpn hpn' hne ho
    have a1 := hU1 n
    have a2 := hU2 M n
    have a3 := hU2 T n
    simp only [hU]
    by_cases hsq : IsSquare n
    · rw [if_pos hsq]; linarith
    by_cases hm : n.minFac ∣ m₀
    · have : n.minFac ∈ M := Finset.mem_filter.2
        ⟨Nat.mem_primeFactors.2 ⟨Nat.minFac_prime hpn.ne_one, hm, hm₀.ne'⟩,
          (Nat.minFac_le hpn.pos).trans (Finset.mem_Icc.1 hn).2⟩
      have := hsingle M n this
      linarith
    have h1 := meanSq_mem_outPart m₀ hpn hpn' hne hsq hm
    have h2 := meanSq_card_primeFactors_outPart m₀ hpn hpn'
    rcases ho with ho | ho
    · rw [ho] at h1; simp at h1
    · rw [ho] at h1 h2
      have : n.minFac ∈ T := by simp only [hT]; rw [if_pos h2]; exact h1
      have := hsingle T n this
      linarith
  have hpt : ∀ n ∈ Icc 1 N, ∀ n' ∈ Icc 1 N, cn x n * cn x n' * A n n' ≤
      η * (cn x n * cn x n') + ∑ p ∈ P, f p n * f p n' + U n * U n' := by
    intro n hn n' hn'
    have b1 : 0 ≤ η * (cn x n * cn x n') := mul_nonneg hη (mul_nonneg (hc n) (hc n'))
    have b2 : 0 ≤ ∑ p ∈ P, f p n * f p n' := Finset.sum_nonneg fun p _ => mul_nonneg (hf0 p n) (hf0 p n')
    have b3 : 0 ≤ U n * U n' := mul_nonneg (hU0 n) (hU0 n')
    have b4 : cn x n * cn x n' * A n n' ≤ cn x n * cn x n' :=
      mul_le_of_le_one_right (mul_nonneg (hc n) (hc n')) (hA1 n n')
    by_cases hpn : IsPrimePow n
    swap
    · have : cn x n * cn x n' * A n n' = 0 := by rw [meanSq_cn_eq_zero x hpn]; ring
      linarith
    by_cases hpn' : IsPrimePow n'
    swap
    · have : cn x n * cn x n' * A n n' = 0 := by rw [meanSq_cn_eq_zero x hpn']; ring
      linarith
    by_cases hne : n.minFac = n'.minFac
    · have hmem : n.minFac ∈ P := Finset.mem_filter.2
        ⟨Finset.mem_Icc.2 ⟨Nat.minFac_pos n, (Nat.minFac_le hpn.pos).trans (Finset.mem_Icc.1 hn).2⟩,
          Nat.minFac_prime hpn.ne_one⟩
      have := Finset.single_le_sum (f := fun p => f p n * f p n')
        (fun p _ => mul_nonneg (hf0 p n) (hf0 p n')) hmem
      have e : f n.minFac n * f n.minFac n' = cn x n * cn x n' := by
        simp only [hf]; rw [if_pos trivial, if_pos hne.symm]
      simp only [e] at this
      linarith
    by_cases ho : outPart m₀ (n * n') = 1 ∨ outPart m₀ (n * n') = nStar
    · have c1 := hUc n n' hn hpn hpn' hne ho
      have c2 := hUc n' n hn' hpn' hpn (Ne.symm hne) (by rwa [mul_comm n' n])
      have := mul_le_mul c1 c2 (hc n') (hU0 n)
      linarith
    · rw [not_or] at ho
      have := mul_le_mul_of_nonneg_left (hA n n' hn hn' hpn hpn' ho.1 ho.2) (mul_nonneg (hc n) (hc n'))
      linarith
  refine (Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun n' hn' => hpt n hn n' hn').trans ?_
  simp_rw [Finset.sum_add_distrib]
  refine add_le_add (add_le_add (le_of_eq ?_) ?_) ?_
  · rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    simp_rw [Finset.mul_sum]
  · have : ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, ∑ p ∈ P, f p n * f p n' =
        ∑ p ∈ P, (∑ n ∈ Icc 1 N, f p n) ^ 2 := by
      simp_rw [sq, Finset.sum_mul_sum]
      rw [Finset.sum_comm (s := P)]
      exact Finset.sum_congr rfl fun n _ => Finset.sum_comm
    rw [this]
    refine Finset.sum_le_sum fun p hp => ?_
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => hf0 p n) (hfib p (Finset.mem_filter.1 hp).2) 2
  · rw [← Finset.sum_mul_sum, ← sq]
    refine pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => hU0 n) ?_ 2
    simp only [hU]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_filter,
      Finset.sum_comm (t := M), Finset.sum_comm (t := T)]
    refine add_le_add (add_le_add le_rfl (Finset.sum_le_sum fun p hp =>
      hfib p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1))) ?_
    have h1 : ∑ p ∈ T, ∑ n ∈ Icc 1 N, f p n ≤ T.card • S :=
      Finset.sum_le_card_nsmul _ _ _ fun p hp => (hfib p (hTprime p hp)).trans (hS p (hTprime p hp))
    rw [nsmul_eq_mul] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ hS0)
    exact_mod_cast hTcard
end GlobalTheory
